package org.tygus.suslik.synthesis

import akka.actor.{Actor, ActorRef, ActorSystem, PoisonPill, Props, Terminated}
import akka.pattern.ask
import org.tygus.suslik.language.Statements.{Solution, _}
import org.tygus.suslik.report.{Log, ProofTrace}
import org.tygus.suslik.synthesis.SearchTree._
import org.tygus.suslik.synthesis.Termination.isTerminatingExpansion
import org.tygus.suslik.synthesis.tactics.Tactic
import org.tygus.suslik.util.SynStats

import scala.concurrent.{Await, TimeoutException}
import scala.concurrent.duration.DurationInt


class ParallelSynthesis(tactic: Tactic, override implicit val log: Log, override implicit val trace: ProofTrace)
  extends Synthesis(tactic, log, trace) {

  var system: ActorSystem = _

  protected override def runProcessWorkList(implicit stats: SynStats, config: SynConfig): Option[Solution] = {

    import Protocol._

    system = ActorSystem("ParallelSynthesis")

    val master = system.actorOf(Props(new Master), name = "Master")

    val nWorkers = config.parallel.get
    val actorRefs: List[ActorRef] = master ::
      (for (i <- 0 until nWorkers)
        // TODO rename to Worker$i
        yield system.actorOf(Props(new Worker(master)), name = s"$i")
      ).toList

    // TODO: get timeout from stats.timedOut
    // TODO: use onComplete
    val timeout = 1000.seconds
    val solution: Option[Solution] = try {
      Await.result(master.ask(Protocol.StartSearch)(timeout), timeout) match {
        case SearchDone(sol) => sol
        case _ => None
      }
    } catch {
      case _: TimeoutException => {
        stop(actorRefs)
        throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut} seconds.\n")
      }
    }

    stop(actorRefs)
    solution
  }

  def stop(actorRefs: List[ActorRef]): Unit = {
    actorRefs foreach { _ ! PoisonPill }
    if (system ne null) {
      system.terminate()
      system = null
    }
  }

  object Protocol {
    case object StartSearch
    case class SearchDone(solution: Option[Solution])

    case class NewWorker(worker: ActorRef)
    case class RequestTask(node: OrNode)
    case class TaskDone(worker: ActorRef, res: (Option[Solution], List[OrNode], Boolean))
  }

  class Master(implicit stats: SynStats, config: SynConfig) extends Actor {

    import Protocol._

    var outer: ActorRef = _

    var workers = Map[ActorRef, Option[OrNode]]()

    def receive = {
      case StartSearch =>
        outer = sender

      case NewWorker(w) =>
        workers += w -> None
        context.watch(w)
        sendWork()

      case TaskDone(w, (sol, newNodes, isFailed)) =>
        if (!config.printDerivations & sol.isEmpty & isFailed) {
          println(getColor(w.path.name) + "Worker" + Console.RED + s" cannot expand goal: BACKTRACK")
        }
        var solution: Option[Solution] = None
        for (optionTask <- workers.get(w)) {
          for (node <- optionTask) {
            print(Console.WHITE + s"${worklist.map{_.id}.toString()}")
            if (!config.printDerivations) {
              println(getColor(w.path.name) + s"--------Done: ${node.id} puts ${newNodes.map{_.id}.toString()}")
            }
            worklist = newNodes ++ worklist
            solution = sol.flatMap(node.succeed(_))
            if (isFailed) node.fail
          }
        }
        if (solution.isDefined) {
          outer ! SearchDone(solution)
        } else {
          workers += w -> None
          sendWork()
        }

      case Terminated(w) =>
        if (workers contains w) {
          workers -= w
        }
    }

    def sendWork() = {
      val (idleWorkers, workingWorkers) = workers.partition(_._2.isEmpty)
      assert(idleWorkers.nonEmpty)

      val sz = worklist.length
      log.print(List((s"Worklist ($sz): ${worklist.map(n => s"${n.pp()}[${n.cost}]").mkString(" ")}", Console.YELLOW)))
      log.print(List((s"Succeeded leaves (${successLeaves.length}): ${successLeaves.map(n => s"${n.pp()}").mkString(" ")}", Console.YELLOW)))
      stats.updateMaxWLSize(sz)

      if (worklist.isEmpty) {
        if (workingWorkers.isEmpty) {
          outer ! SearchDone(None) // No goals to try & no goals in progress: synthesis failed
        }
      } else {
        val nodes = selectNodes(idleWorkers.size) // Select next nodes to expand
        for ((w, node) <- idleWorkers.keySet zip nodes) {
          workers += w -> Some(node)
          w ! RequestTask(node)

          val goal = node.goal
          stats.addExpandedGoal(node)
          log.print(List((s"Expand: ${node.pp()}[${node.cost}]", Console.YELLOW))) //      <goal: ${node.goal.label.pp}>
          if (config.printEnv) {
            log.print(List((s"${goal.env.pp}", Console.MAGENTA)))
          }
          log.print(List((s"${w.path.name}: ${node.id}", Console.GREEN)))
          log.print(List((s"${goal.pp}", Console.BLUE)))

          if (!config.printDerivations) {
            println(getColor(w.path.name) + s"${node.id}")
          }
        }
      }
    }

    private def getColor(actorName: String): String = actorName match {
      case "0" => Console.GREEN
      case "1" => Console.BLUE
      case _   => Console.YELLOW
    }
  }

  class Worker(master: ActorRef)(implicit stats: SynStats, config: SynConfig) extends Actor {
    import Protocol._

    def receive = {
      case RequestTask(node) =>
        master ! TaskDone(self, expandNode(node))
    }

    override def preStart() = master ! NewWorker(self)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Given a worklist, return some next nodes to work on
  protected def selectNodes(nWorkers: Int)
                           (implicit config: SynConfig): List[OrNode] = {
    val num = math.min(nWorkers, worklist.size)
    (for (_ <- 0 until num) yield {
      val best = worklist.minBy(_.cost)
      val idx = worklist.indexOf(best)
      worklist = worklist.take(idx) ++ worklist.drop(idx + 1)
      best
    }).toList
  }

  // Expand node and return either a new worklist or the final solution
  protected def expandNode(node: OrNode)
                          (implicit stats: SynStats, config: SynConfig): (Option[Solution], List[OrNode], Boolean) = {
    val goal = node.goal
    implicit val ctx = log.Context(goal)

    // Apply all possible rules to the current goal to get a list of alternative expansions,
    // each of which can have multiple open subgoals
    val rules = tactic.nextRules(node)
    val allExpansions = applyRules(rules)(node, stats, config, ctx)
    val expansions = tactic.filterExpansions(allExpansions)

    // Check if any of the expansions is a terminal
    expansions.find(_.subgoals.isEmpty) match {
      case Some(e) => {
        successLeaves = node :: successLeaves
        (Some(e.producer(Nil)), Nil, false)
      }

      case None => { // no terminals: add all expansions to worklist
        // Create new nodes from the expansions
        val newNodes = for {
          (e, i) <- expansions.zipWithIndex
          andNode = AndNode(i +: node.id, node, e)
          if isTerminatingExpansion(andNode) // termination check
            nSubs = e.subgoals.size
          (g, j) <- if (nSubs == 1) List((e.subgoals.head, -1)) else e.subgoals.zipWithIndex
        } yield {
          val extraCost = if (j == -1) 0 else e.subgoals.drop(j + 1).map(_.cost).sum
          OrNode(j +: andNode.id, g, Some(andNode), node.extraCost + extraCost)
        }

        if (newNodes.isEmpty) {
          // This is a dead-end: prune worklist and try something else
          log.print(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
        } else {
          stats.addGeneratedGoals(newNodes.size)
        }
        (None, newNodes.toList, newNodes.isEmpty)
      }
    }
  }
}