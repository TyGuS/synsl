package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.language.{Ident, Statements}
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.logic.unification.SpatialUnification._
import org.tygus.synsl.logic.unification.{PureUnification, UnificationGoal}
import org.tygus.synsl.synthesis._

/**
  * @author Ilya Sergey
  */

object SubtractionRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-subtraction"

  import Statements._

  /*

    -------------------------------- [emp]
    Γ ; {φ ; emp} ; {emp} ---> skip

  Empty rule: supposed to be applied at the end

  */

  object EmpRule extends SynthesisRule {

    override def toString: Ident = "[Sub: emp]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post

      if (pre.sigma.isEmp &&
        post.sigma.isEmp &&
        goal.existentials.isEmpty && // No existentials, otherwise should be solved by pure synthesis
        {
          SMTSolving.valid(pre.phi.implies(post.phi))
        })
        List(Subderivation(Nil, _ => Skip))
      else Nil
    }
  }

  /*
           (GV(Q) / GV(P)) * GV(R) = Ø
          Γ ; {φ ; P} ; {ψ ; Q} ---> S
    ---------------------------------------- [*-intro]
      Γ ; {φ ; P * R} ; {ψ ; Q * R} ---> S


    This is the former [frame] rule
   */

  object StarIntro extends SynthesisRule {
    override def toString: String = "[Sub: *-intro]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      def sideCond(p: SFormula, q: SFormula, r: Heaplet) = {
        val gvP = p.vars.filter(goal.isGhost).toSet
        val gvQ = q.vars.filter(goal.isGhost).toSet
        val gvR = r.vars.filter(goal.isGhost)

        gvQ.diff(gvP).intersect(gvR).isEmpty
      }

      val pre = goal.pre
      val post = goal.post

      for {
        t <- pre.sigma.chunks
        s <- post.sigma.chunks
        sub <- tryUnify(t, s, goal.universals ++ goal.formals, false)
        newPreSigma = pre.sigma - t
        newPostSigma = (post.sigma - s).subst(sub)
        if sideCond(newPreSigma, newPostSigma, t)
      } yield {
        val newPre = Assertion(pre.phi, newPreSigma)
        val newPost = Assertion(post.phi.subst(sub), newPostSigma)
        Subderivation(List((goal.copy(newPre, newPost), env)), pureKont(toString))
      }
    }
  }

  /*
    Γ ; {φ ∧ φ1 ; P} ; {ψ' ; Q'} ---> S
            s = unify(φ1, φ2)
      {ψ' ; Q'} = subst({ψ ; Q}, s)
  --------------------------------------- [Hypothesis-Unify]
  Γ ; {φ ∧ φ1 ; P} ; {ψ ∧ φ2 ; Q} ---> S

   */

  object HypothesisUnify extends SynthesisRule {
    override def toString: String = "[Sub: hypothesis-unify]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post
      val params = goal.gamma.map(_._2).toSet
      PureUnification.unify(
        UnificationGoal(pre, params), UnificationGoal(post, params), needRefreshing = false, precise = false) match {
        case None => Nil
        case Some(sbst) =>
          val postSubst = post.subst(sbst)
          removeEquivalent(pre.phi, postSubst.phi) match {
            case Some(cs) =>
              val newPost = Assertion(cs, postSubst.sigma)
              val newGoal = Goal(pre, newPost, goal.gamma, goal.fname)
              List(Subderivation(List((newGoal, env)), pureKont(toString)))
            case None => Nil
          }
      }
    }
  }


  /*
      Γ ; {φ ; x.f -> l * P} ; {ψ ∧ Y = l ; x.f -> Y * Q} ---> S
      ---------------------------------------------------------- [pick]
      Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> Y * Q} ---> S
   */

  object Pick extends SynthesisRule {
    override def toString: String = "[Sub: pick]"

    def apply(goal: Goal, env: Environment): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplet RHS has existentials
      def hasExistential: Heaplet => Boolean = {
        case PointsTo(_, _, e) => e.vars.exists(v => goal.isExistential(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && hasExistential(hr)

      findMatchingHeaplets(_.isInstanceOf[PointsTo], isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@(PointsTo(x@Var(_), offset, e1)), hr@(PointsTo(_, _, e2)))) =>
          val cs = conjuncts(post.phi)
          if (cs.contains(PEq(e1, e2)) || cs.contains(PEq(e2, e1)))
            Nil
          else {
            val newPre = Assertion(pre.phi, goal.pre.sigma)
            val newPost = Assertion(mkConjunction(PEq(e1, e2) :: cs), goal.post.sigma)
            val newGoal = goal.copy(newPre, newPost)
            List(Subderivation(List((newGoal, env)), pureKont(toString)))
          }
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Pick rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }

  }

}
