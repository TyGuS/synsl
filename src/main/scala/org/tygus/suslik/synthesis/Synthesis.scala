package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.util.{SynLogging, SynStats}
import org.tygus.suslik.synthesis.rules.Rules._

import scala.Console._
import scala.annotation.tailrec

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis extends SepLogicUtils {

  val log: SynLogging

  import log._

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)


  def allRules(goal: Goal): List[SynthesisRule]

  def nextRules(goal: Goal, depth: Int): List[SynthesisRule]

  def synthesizeProc(funGoal: FunSpec, env: Environment): Option[(List[Procedure], SynStats)] = {
    implicit val config: SynConfig = env.config
    val FunSpec(name, tp, formals, pre, post) = funGoal
    val goal = topLevelGoal(pre, post, formals, name, env)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))(i = 0, config)
    val stats = new SynStats()
    SMTSolving.init()
    try {
      synthesize(goal)(stats = stats) match {
        case Some((body, helpers)) =>
          val main = Procedure(name, tp, formals, body)
          Some(main :: helpers, stats)
        case None =>
          printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp}")
          None
      }
    } catch {
      case SynTimeOutException(msg) =>
        printlnErr(msg)
        None
    }
  }

  protected def synthesize(goal: Goal)
                          (stats: SynStats)
                          (implicit ind: Int = 0): Option[Solution] = {
    // Initialize worklist: root or-node containing the top-level goal
    val worklist = List(OrNode("", goal, None))
    processWorkList(worklist)(stats, goal.env.config, ind)
  }

  case class OrNode(label: String, goal: Goal, parent: Option[AndNode]) {
    // Does this node have a ancestor with label l?
    def hasAncestor(l: String): Boolean =
      if (label == l) true
      else if (label.length < l.length) false
      else parent match {
        // this node cannot be the root, because label.lengh > l.length
        case Some(p) => p.hasAncestor(l)
      }

    // Replace the ancestor labeled l with newAN
    def replaceAncestor(l: String, n: AndNode): OrNode = parent match {
      case None => this
      case Some(p) =>
        if (p.label == l) copy(parent = Some(n))
        else if (p.label.length <= l.length) this
        else p.parent.replaceAncestor(l, n)
    }

    // This node has failed: prune siblings from worklist
    def fail(wl: List[OrNode]): List[OrNode] = parent match {
      case None => wl // this is the root; wl must already be empty
      case Some(an) => { // a subgoal has failed: prune all other descendants of an
        wl.filterNot(_.hasAncestor(an.label))
      }
    }

    // This node has succeeded: update worklist or return solution
    def succeed(s: Solution, wl: List[OrNode]): Either[List[OrNode], Solution] = parent match {
      case None => Right(s) // this is the root: synthesis succeeded
      case Some(an) => { // a subgoal has succeeded
        val newWL = wl.filterNot(_.hasAncestor(label)) // prune all my descendants from worklist
        // Check if an has more open subgoals:
        if (an.kont.arity == 1) { // there are no more open subgoals: an has succeeded
          an.parent.succeed(an.kont(List(s)), newWL)
        } else { // there are other open subgoals: partially apply and replace in descendants
          val newAN = an.copy(kont = an.kont.partApply(s))
          Left(newWL.map(_.replaceAncestor(an.label, newAN)))
        }
      }
    }
  }

  case class AndNode(label: String, kont: StmtProducer, parent: OrNode) {
    // Does this node have a ancestor with label l?
    def hasAncestor(l: String): Boolean =
      if (label == l) true
      else if (label.length < l.length) false
      else parent.hasAncestor(l)
  }

  @tailrec final def processWorkList(worklist: List[OrNode])
                                    (implicit
                                     stats: SynStats,
                                     config: SynConfig,
                                     ind: Int): Option[Solution] = {

    // Check for timeouts
    val currentTime = System.currentTimeMillis()
    if (currentTime - config.startTime > config.timeOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut.toDouble / 1000} seconds.\n")
    }

    val sz = worklist.length
    printLog(List((s"\nWorklist ($sz): ${worklist.map(_.label).mkString(" ")}", Console.YELLOW)))
    stats.updateMaxWLSize(sz)

    worklist match {
      case Nil => // No more goals to try: synthesis failed
        None
      case node :: rest => {
        val goal = node.goal
        printLog(List((s"Goal to expand: ${goal.label.pp} (depth: ${goal.depth})", Console.BLUE)))
        stats.updateMaxDepth(goal.depth)
        if (config.printEnv) {
          printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
        }
        printLog(List((s"${goal.pp}", Console.BLUE)))

        // Apply all possible rules to the current goal to get a list of alternatives,
        // each of which can have multiple open goals
        val rules = nextRules(goal, 0)
        val expansions =
          if (goal.isUnsolvable) Nil  // This is a special unsolvable goal, discard eagerly
          else applyRules(rules)(goal, stats, config, ind)

        if (expansions.isEmpty) {
          stats.bumpUpBacktracing()
          printLog(List((s"Cannot expand goal: BACKTRACK", Console.RED)))
          val newWorkList = node.fail(rest)
          processWorkList(newWorkList)
        } else {
          collectResults(node, expansions) match {
            case Right(sol) => {
              node.succeed(sol, rest) match {
                case Right(sol) => Some(sol)
                case Left(newWorkList) => processWorkList(newWorkList)
              }
            }
            case Left(nodes) => {
              val newWorkList = nodes ++ rest
              processWorkList(newWorkList)
            }
          }
        }
      }
    }
  }

  def collectResults(node: OrNode, expansions: Seq[RuleResult]): Either[List[OrNode], Solution] = expansions match {
    case Nil => Left(Nil)
    case e +: es =>
      if (e.subgoals.isEmpty) {
        // Expansion with no premises: synthesis of this node succeeded
        Right(e.kont(Nil))
      } else {
        val andNode = AndNode(expansions.length.toString + node.label,  e.kont, node)
        val newOrNodes = e.subgoals.zipWithIndex.map{ case (g, j) => OrNode(j.toString + andNode.label, g, Some(andNode))}
        collectResults(node, es) match {
          case Left(nodes) => Left(newOrNodes.toList ++ nodes)
          case Right(sol) => Right(sol)
        }
      }
  }

  protected def applyRules(rules: List[SynthesisRule])(implicit goal: Goal,
                                                       stats: SynStats,
                                                       config: SynConfig,
                                                       ind: Int): Seq[RuleResult] = rules match
  {
    case Nil => Vector() // No more rules to apply: done expanding the goal
    case r :: rs =>
      val goalStr = s"$r: "
      // Invoke the rule
      val allChildren = r(goal)
      // Filter out children that contain out-of-order goals
      val children = if (config.commute) {
        allChildren.filterNot(_.subgoals.exists(goalOutOfOrder))
      } else allChildren

      if (children.isEmpty) {
        // Rule not applicable: try other rules
        printLog(List((s"${goalStr}FAIL", BLACK)), isFail = true)
        applyRules(rs)
      } else {
        // Rule applicable: try all possible sub-derivations
//        val subSizes = children.map(c => s"${c.subgoals.size} sub-goal(s)").mkString(", ")
        val succ = s"SUCCESS, ${children.size} alternative(s): ${children.map(_.pp).mkString(", ")}"
        printLog(List((s"$goalStr$GREEN$succ", BLACK)))
        stats.bumpUpRuleApps()
        if (config.invert && r.isInstanceOf[InvertibleRule]) {
          // The rule is invertible: do not try other rules on this goal
          children
        } else {
          // Both this and other rules apply
          children ++ applyRules(rs)
        }
      }
  }

  // Is current goal supposed to appear before g?
  def goalOutOfOrder(g: Goal)(implicit goal: Goal,
                              stats: SynStats,
                              config: SynConfig,
                              ind: Int): Boolean = {
    g.hist.outOfOrder(allRules(goal)) match {
      case None => false
      case Some(app) =>
        //              printLog(List((g.deriv.preIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        //              printLog(List((g.deriv.postIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
        printLog(List((s"${RED}Alternative ${g.hist.applications.head.pp} commutes with earlier ${app.pp}", BLACK)))
        true
    }
  }

  private def getIndent(implicit i: Int): String = if (i <= 0) "" else "|  " * i

  protected def printLog(sc: List[(String, String)], isFail: Boolean = false)
                      (implicit i: Int, config: SynConfig): Unit = {
    if (config.printDerivations) {
      if (!isFail || config.printFailed) {
        for ((s, c) <- sc if s.trim.length > 0) {
          print(s"$BLACK$getIndent")
          println(s"$c${s.replaceAll("\n", s"\n$BLACK$getIndent$c")}")
        }
      }
      print(s"$BLACK")
    }
  }

}