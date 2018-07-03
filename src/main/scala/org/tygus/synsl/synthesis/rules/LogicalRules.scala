package org.tygus.synsl.synthesis.rules

import org.tygus.synsl.language.Expressions._
import org.tygus.synsl.language.{Ident, IntType}
import org.tygus.synsl.language.Statements._
import org.tygus.synsl.logic._
import org.tygus.synsl.logic.smt.SMTSolving
import org.tygus.synsl.logic.Specifications._
import org.tygus.synsl.synthesis._

/**
  * Logical rules simplify specs and terminate the derivation;
  * they do not eliminate existentials.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object LogicalRules extends PureLogicUtils with SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-logical"

  /*

    -------------------------------- [emp]
    Γ ; {φ ; emp} ; {emp} ---> skip

    Axiom: heaps are empty and pure spec is valid -> emit skip

  */
  object EmpRule extends SynthesisRule with FlatPhase with InvertibleRule {

    override def toString: Ident = "[Sub: emp]"

    def condCandidates(goal: Goal): Seq[Expr] =
      for {
        lhs <- goal.programVars
        rhs <- goal.programVars
        if lhs != rhs
        if goal.getType(lhs) == IntType && goal.getType(rhs) == IntType
      } yield lhs |<=| rhs

    def guardedCandidates(goal: Goal, pre: PFormula, post: PFormula): Seq[Subderivation] =
      for {
        cond <- condCandidates(goal)
        if SMTSolving.valid((pre && cond) ==> post)
        if SMTSolving.sat(pre && cond)
      } yield Subderivation(Nil, _ => Guarded(cond, Skip))


    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post

      if (pre.sigma.isEmp && post.sigma.isEmp) { // heaps are empty
        val (eConjuncts, neConjuncts) = conjuncts(post.phi).partition(p => p.vars.exists(goal.isExistential))
        val universalPost = mkConjunction(neConjuncts)
        if (eConjuncts.isEmpty) { // no existentials
          if (SMTSolving.valid(pre.phi ==> post.phi))
            List(Subderivation(Nil, _ => Skip)) // pre implies post: we are done
          else {
            val guarded = guardedCandidates(goal, pre.phi, universalPost)
            if (guarded.isEmpty)
              List(Subderivation(Nil, _ => Magic)) // pre doesn't imply post: only magic can save us
            else guarded
          }
        } else { // has existentials: check if the rest of the post is already invalid
          if (SMTSolving.valid(pre.phi ==> universalPost))
            Nil // valid so far, nothing to say
          else{
            val guarded = guardedCandidates(goal, pre.phi, universalPost)
            if (guarded.isEmpty)
              List(Subderivation(Nil, _ => Magic)) // pre doesn't imply post: only magic can save us
            else guarded
          }
        }
      } else Nil // heaps non-empty
    }
  }

  /*
  --------------------------------------- [inconsistency]
  Γ ; {φ ∧ l ≠ l ; P} ; {ψ ; Q} ---> emp

  The other axiom: pre is inconsistent -> emit error
  */
  object Inconsistency extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: inconsistency]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre.phi
      val post = goal.post.phi

      if (!SMTSolving.sat(pre))
        List(Subderivation(Nil, _ => Error)) // pre inconsistent: return error
      else
        Nil
    }
  }


  /*
   Remove an equivalent heaplet from pre and post
   */
  abstract class Frame extends SynthesisRule {
    def heapletFilter(h: Heaplet): Boolean

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post
      val deriv = goal.deriv

      def isSuitable(hPost: Heaplet): Boolean = !hPost.vars.exists(goal.isExistential) && heapletFilter(hPost)
      def isMatch(hPre: Heaplet, hPost: Heaplet): Boolean = hPre.eqModTags(hPost) && isSuitable(hPost)

      findMatchingHeaplets(_ => true, isMatch, pre.sigma, post.sigma) match {
        case None => Nil
        case Some((hPre, hPost)) => {
          val newPreSigma = pre.sigma - hPre
          val newPostSigma = post.sigma - hPost
          val newPre = Assertion(pre.phi, newPreSigma)
          val newPost = Assertion(post.phi, newPostSigma)
          val preFootprint = Set(deriv.preIndex.lastIndexOf(hPre))
          val postFootprint = Set(deriv.postIndex.lastIndexOf(hPost))
          val ruleApp = saveApplication((preFootprint, postFootprint), deriv)
          val newGoal = goal.copy(newPre, newPost, newRuleApp = Some(ruleApp))
          List(Subderivation(List(newGoal), pureKont(toString)))
        }
      }
    }
  }

  object FrameUnfolding extends Frame with UnfoldingPhase {
    override def toString: String = "[Sub: frame-unfold]"
  }

  object FrameFlat extends Frame with FlatPhase with InvertibleRule {
    override def toString: String = "[Sub: frame-flat]"
  }


  /*
  x ≠ nil ∉ φ
  Γ ; {φ ∧ x ≠ nil ; x.f -> l * P} ; {ψ ; Q} ---> S
  -------------------------------------------------- [nil-not-lval]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; Q} ---> S
  */

  object NilNotLval extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: nil-not-lval]"

    def apply(goal: Goal): Seq[Subderivation] = {

      // Find pointers in `a` that are not yet known to be non-null
      def findPointers(a: Assertion): Set[Expr] = {
        val cs = conjuncts(a.phi)
        // All pointers
        val allPointers = (for (PointsTo(l, _, _) <- a.sigma.chunks) yield l).toSet
        allPointers.filter(
          x => !cs.contains(x |/=| NilPtr) && !cs.contains(NilPtr |/=| x)
        )
      }


      def addToAssertion(a: Assertion, ptrs: Set[Expr]): Assertion = {
        val cs = conjuncts(a.phi)
        val newPhi = mkConjunction(cs ++ ptrs.map { x => x |/=| NilPtr })
        Assertion(newPhi, a.sigma)
      }

      val pre = goal.pre
      val post = goal.post

      val prePointers = findPointers(pre)
      val postPointers = findPointers(post).filter(_.vars.forall(v => goal.isExistential(v)))

      if (prePointers.isEmpty && postPointers.isEmpty)
        Nil // no pointers to insert
      else {
        val newPre = addToAssertion(pre, prePointers)
        val newPost = addToAssertion(post, postPointers)
        val newGoal = goal.copy(newPre, newPost)
        List(Subderivation(List(newGoal), pureKont(toString)))
      }
    }
  }

  /*
  x ≠ y ∉ φ
  Γ ; {φ ∧ x ≠ y ; x.f -> l * y.f -> l' * P} ; {ψ ; Q} ---> S
  ------------------------------------------------------------ [*-partial]
  Γ ; {φ ; x.f -> l * y.f -> l' * P} ; {ψ ; Q} ---> S
   */
  object StarPartial extends SynthesisRule with AnyPhase with InvertibleRule {
    override def toString: String = "[Norm: *-partial]"

    def extendPure(p: PFormula, s: SFormula, excludeVars: Set[Var]): Option[PFormula] = {
      val cs = conjuncts(p)
      val ptrs = (for (PointsTo(x, _, _) <- s.chunks) yield x).toSet
      // All pairs of pointers
      val pairs = for (x <- ptrs; y <- ptrs if x != y) yield (x, y)
      val newPairs = pairs.filter {
        case (x, y) => excludeVars.intersect(x.vars ++ y.vars).isEmpty &&
          !cs.contains(x |/=| y) && !cs.contains(y |/=| x)
      }
      if (newPairs.isEmpty) None
      else Some(mkConjunction(cs ++ newPairs.map { case (x, y) => x |/=| y }))
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      val s1 = goal.pre.sigma
      val s2 = goal.post.sigma

      (extendPure(goal.pre.phi, s1, Set.empty), extendPure(goal.post.phi, s2, goal.existentials)) match {
          // TODO: make sure it's complete to include post, otherwise revert to pre only
        case (None, None) => Nil
        case (Some(p1), None) =>
          val newGoal = goal.copy(pre = Assertion(p1, s1))
          List(Subderivation(List(newGoal), pureKont(toString)))
        case (None, Some(p2)) =>
          val newGoal = goal.copy(post = Assertion(p2, s2))
          List(Subderivation(List(newGoal), pureKont(toString)))
        case (Some(p1), Some(p2)) =>
          val newGoal = goal.copy(pre = Assertion(p1, s1), post = Assertion(p2, s2))
          List(Subderivation(List(newGoal), pureKont(toString)))
//        case (None, _) => Nil
//        case (Some(p1), _) =>
//          val newGoal = goal.copy(pre = Assertion(p1, s1))
//          List(Subderivation(List(newGoal), pureKont(toString)))
      }
    }
  }


  /*
  Γ ; {[l/x]φ ; [l/x]P} ; {[l/x]ψ ; [l/x]Q} ---> S
  ------------------------------------------------ [subst-L]
  Γ ; {φ ∧ x = l ; P} ; {ψ ; Q} ---> S
  */
  object SubstLeft extends SynthesisRule with FlatPhase with InvertibleRule {
    override def toString: String = "[Norm: subst-L]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val p1 = goal.pre.phi
      val s1 = goal.pre.sigma
      val p2 = goal.post.phi
      val s2 = goal.post.sigma

      findConjunctAndRest({
        case BinaryExpr(OpEq, v1@Var(_), v2) => v1 != v2
        // This messes with hypothesis unify:
//        case BinaryExpr(OpSetEq, v1@Var(_), v2) => v1 != v2
        case _ => false
      }, simplify(p1)) match {
        case Some((BinaryExpr(_, x@Var(_), l), rest1)) =>
          val _p1 = simplify(mkConjunction(rest1).subst(x, l))
          val _s1 = s1.subst(x, l)
          val _p2 = simplify(p2.subst(x, l))
          val _s2 = s2.subst(x, l)
          val newGoal = goal.copy(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2))
            List(Subderivation(List(newGoal), pureKont(toString)))
        case _ => Nil
      }
    }
  }
}
