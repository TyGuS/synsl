package org.tygus.suslik.certification.targets.htt.translation

import org.tygus.suslik.certification.SuslikProofStep
import org.tygus.suslik.certification.targets.htt.language.CGamma
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.logic.Sentences.{CAssertion, CFunSpec, CInductiveClause, CInductivePredicate}
import org.tygus.suslik.certification.targets.htt.program.Statements._
import org.tygus.suslik.certification.targets.htt.translation.Translation.{translateAsn, translateExpr, translateParam, translateSApp, translateType, translateVar}
import org.tygus.suslik.certification.traversal.ProofTree
import org.tygus.suslik.language.Expressions.{Subst, SubstVar, Var}
import org.tygus.suslik.language.Statements
import org.tygus.suslik.language.Statements.{Call, Free, Load, Malloc, Store}
import org.tygus.suslik.logic.{FunSpec, Gamma}
import org.tygus.suslik.logic.Specifications.Goal

object IR {
  type Unfoldings = Map[CSApp, CInductiveClause]
  type SAppNames = Map[CSApp, CSApp]
  type CSubst = Map[CVar, CExpr]
  type CSubstVar = Map[CVar, CVar]
  type PredicateEnv = Map[String, CInductivePredicate]

  case class CGoal(pre: CAssertion,
                   post: CAssertion,
                   gamma: CGamma,
                   programVars: Seq[CVar],
                   universalGhosts: Seq[CVar],
                   fname: String) {
    val existentials: Seq[CVar] = post.valueVars.diff(programVars ++ universalGhosts)
    def subst(sub: CSubst): CGoal = CGoal(
      pre.subst(sub),
      post.subst(sub),
      gamma.map { case (v, t) => v.substVar(sub) -> t },
      programVars.map(_.substVar(sub)),
      universalGhosts.map(_.substVar(sub)),
      fname
    )

    def toFunspec: CFunSpec = {
      val params = programVars.map(v => (gamma(v), v))
      val ghosts = universalGhosts.map(v => (gamma(v), v))
      CFunSpec(fname, CUnitType, params, ghosts, pre, post)
    }
  }

  case class Context(
                      unfoldings: Unfoldings,
                      sappNames: SAppNames,
                      subst: CSubst,
                      substVar: CSubstVar,
                      predicateEnv: PredicateEnv,
                      nestedContext: Option[NestedContext],
                      topLevelGoal: Option[CGoal],
                    )

  val emptyContext: Context = Context(Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, None, None)

  case class NestedContext(funspec: CFunSpec, call: CCall, freshToActual: CSubst = Map.empty, companionToFresh: CSubstVar) {
    def updateSubstitution(sigma: CSubst): NestedContext = {
      this.copy(freshToActual = freshToActual.map { case (k, e) => k -> e.subst(sigma) } ++ sigma)
    }

    def applySubstitution: NestedContext = {
      val newPost = funspec.post.subst(freshToActual)
      val newFunSpec = funspec.copy(post = newPost)
      val newCall = call.copy(args = call.args.map(_.subst(freshToActual)))
      this.copy(funspec = newFunSpec, call = newCall)
    }
  }

  abstract class Node {
    val ctx : Context
    val next : Seq[Node]

    private def mapJoin[K, V](m1: Map[K, V], m2: Map[K, V]) : Map[K, V] = {
      m1.toSeq.intersect(m2.toSeq).toMap
    }

    def propagateContext: IR.Node = this match {
      case n:IR.EmpRule => n
      case n:IR.Open =>
        val children = n.next.map(_.propagateContext)
        val childCtxs = children.map(_.ctx)
        val childSubst = childCtxs.map(_.subst).reduceOption[CSubst](mapJoin).getOrElse(Map.empty)
        val childSubstVar = childCtxs.map(_.substVar).reduceOption[CSubstVar](mapJoin).getOrElse(Map.empty)
        val childSAppNames = childCtxs.map(_.sappNames).reduceOption[SAppNames](mapJoin).getOrElse(Map.empty)
        n.copy(next = children, ctx = n.ctx.copy(subst = childSubst, substVar = childSubstVar, sappNames = childSAppNames))
      case n:IR.Branch =>
        val children = n.next.map(_.propagateContext)
        val childCtxs = children.map(_.ctx)
        val childSubst = childCtxs.map(_.subst).reduceOption[CSubst](mapJoin).getOrElse(Map.empty)
        val childSubstVar = childCtxs.map(_.substVar).reduceOption[CSubstVar](mapJoin).getOrElse(Map.empty)
        val childSAppNames = childCtxs.map(_.sappNames).reduceOption[SAppNames](mapJoin).getOrElse(Map.empty)
        n.copy(next = children, ctx = n.ctx.copy(subst = childSubst, substVar = childSubstVar, sappNames = childSAppNames))
      case n:IR.Read =>
        val next1 = n.next.head.propagateContext
        n.copy(ctx = next1.ctx, next = Seq(next1))
      case n:IR.Call =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Free =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Write =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Malloc =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.PureSynthesis =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Close =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.AbduceCall =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Init =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.CheckPost =>
        val next1 = n.next.head.propagateContext
        val ctx1 = next1.ctx.copy(nestedContext = n.ctx.nestedContext)
        n.copy(ctx = ctx1, next = Seq(next1))
      case n:IR.Inconsistency => n
    }
  }

  case class Open(app: CSApp, clauses: Seq[CInductiveClause], selectors: Seq[CExpr], next: Seq[Node], ctx: Context) extends Node

  case class Close(app: CSApp, selector: CExpr, asn: CAssertion, fresh_exist: CSubstVar, next: Seq[Node], ctx: Context) extends Node

  case class Branch(cond: CExpr, next: Seq[Node], ctx: Context) extends Node

  case class PureSynthesis(is_final: Boolean, next: Seq[Node], ctx: Context) extends Node

  case class Read(op: CLoad, next: Seq[Node], ctx: Context) extends Node

  case class Write(stmt: CStore, next: Seq[Node], ctx: Context) extends Node

  case class Free(stmt: CFree, next: Seq[Node], ctx: Context) extends Node

  case class Malloc(stmt: CMalloc, next: Seq[Node], ctx: Context) extends Node

  case class AbduceCall(new_vars: Map[CVar, HTTType],
                        f_pre: CAssertion,
                        calleePost: CAssertion,
                        call: CCall,
                        freshSub: CSubstVar,
                        freshToActual: CSubst,
                        next: Seq[Node],
                        ctx: Context
                       ) extends Node

  case class Call(call: CCall, next: Seq[Node], ctx: Context) extends Node

  case class EmpRule(ctx: Context) extends Node {
    val next: Seq[Node] = Seq.empty
  }

  case class Init(ctx: Context, next: Seq[Node]) extends Node

  case class Inconsistency(ctx: Context) extends Node {
    val next: Seq[Node] = Seq.empty
  }

  case class CheckPost(prePhi: Set[CExpr], postPhi: Set[CExpr], next: Seq[Node], ctx: Context) extends Node

  private def translateSbst(sbst: Subst) = sbst.map{ case (k,v) => CVar(k.name) -> translateExpr(v)}
  private def translateSbstVar(sbst: SubstVar) = sbst.map{ case (k,v) => CVar(k.name) -> CVar(v.name)}
  private def updateSAppAliases(m: SAppNames, sub: CSubst): SAppNames = {
    val affected = m.map { case (app, alias) => app -> (app.subst(sub) -> alias) }.filter { case (app, (app1, _)) => app != app1 }
    m ++ affected.values.toMap
  }

  def translateGoal(goal: Goal): CGoal = {
    val pre = translateAsn(goal.pre)
    val post = translateAsn(goal.post)
    val gamma = goal.gamma.map { case (value, lType) => (translateVar(value), translateType(lType)) }
    val programVars = goal.programVars.map(translateVar)
    val universalGhosts = (pre.valueVars ++ post.valueVars).distinct.filter(v => goal.universalGhosts.contains(Var(v.name)))
    CGoal(pre, post, gamma, programVars, universalGhosts, goal.fname)
  }
  def translateFunSpec(f: FunSpec, gamma: Gamma): CFunSpec = {
    val rType = translateType(f.rType)
    val pre = translateAsn(f.pre)
    val post = translateAsn(f.post)
    val params = f.params.map(translateParam)
    val ghosts = pre.valueVars.diff(params.map(_._2)).map(v => (translateType(gamma(Var(v.name))), v))
    CFunSpec(f.name, rType, params, ghosts, pre, post)
  }

  def fromRule(node: ProofTree[SuslikProofStep], ctx: IR.Context) : IR.Node = node.step match {
    case SuslikProofStep.Init(goal) =>
      val cgoal = translateGoal(goal)
      val sappNames = (cgoal.pre.sigma.apps ++ cgoal.post.sigma.apps).map(a => a -> a).toMap
      val ctx1 = ctx.copy(topLevelGoal = Some(cgoal), sappNames = sappNames)
      IR.Init(ctx1, Seq(fromRule(node.children.head, ctx1)))
    case SuslikProofStep.Open(sapp, fresh_vars, sbst, selectors) =>
      val csapp = translateSApp(sapp)
      val freshCVars = fresh_vars.map{ case (k,v) => CVar(k.name) -> translateExpr(v)}
      val csbst = translateSbst(sbst)
      val pred = ctx.predicateEnv(sapp.pred).subst(freshCVars).subst(csbst)
      val next = node.children.map(n => fromRule(n, ctx))
      val cselectors = selectors.map(translateExpr)
      IR.Open(csapp, pred.clauses, cselectors, next, ctx)
    case SuslikProofStep.Close(sapp, selector, asn, sbst) =>
      val csapp = translateSApp(sapp)
      val cselector = translateExpr(selector)
      val casn = translateAsn(asn)
      val csbst = translateSbst(sbst)
      val pred = ctx.predicateEnv(csapp.pred)
      val cclause = pred.clauses.find(_.selector == cselector).get
      val ex = cclause.existentials.map(_.subst(csbst))
      val actualClause = CInductiveClause(csapp.pred, cclause.idx, cselector, casn, ex)
      val unfoldings = ctx.unfoldings + (csapp -> actualClause)
      val sappNames = ctx.sappNames ++ casn.sigma.apps.map(a => a -> a)
      fromRule(node.children.head, ctx.copy(unfoldings = unfoldings, sappNames = sappNames))
    case SuslikProofStep.Branch(cond, _) =>
      val Seq(ifTrue, ifFalse) = node.children
      IR.Branch(translateExpr(cond), Seq(fromRule(ifTrue, ctx), fromRule(ifFalse, ctx)), ctx)
    case SuslikProofStep.PureSynthesis(is_final, sbst) =>
      val csbst = translateSbst(sbst)
      val nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst))
      val sappNames = updateSAppAliases(ctx.sappNames, csbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = nestedContext, sappNames = sappNames)
      IR.PureSynthesis(is_final, Seq(fromRule(node.children.head, ctx1)), ctx1)
    case SuslikProofStep.SubstL(from, to) =>
      val csbst = translateSbst(Map(from -> to))
      val sappNames = updateSAppAliases(ctx.sappNames, csbst)
      fromRule(node.children.head, ctx.copy(subst = ctx.subst ++ csbst, sappNames = sappNames))
    case SuslikProofStep.SubstR(from, to) =>
      val csbst = translateSbst(Map(from -> to))
      val nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst))
      val sappNames = updateSAppAliases(ctx.sappNames, csbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = nestedContext, sappNames = sappNames)
      fromRule(node.children.head, ctx1)
    case SuslikProofStep.Pick(from, to) =>
      val csbst = translateSbst(Map(from -> to))
      val nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst))
      val sappNames = updateSAppAliases(ctx.sappNames, csbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = nestedContext, sappNames = sappNames)
      fromRule(node.children.head, ctx1)
    case SuslikProofStep.Read(ghostFrom, ghostTo, Load(to, tpe, from, offset)) =>
      val ctx1 = ctx.copy(substVar = ctx.substVar ++ translateSbstVar(Map(ghostFrom -> ghostTo)))
      IR.Read(CLoad(CVar(to.name), translateType(tpe), CVar(from.name), offset), Seq(fromRule(node.children.head, ctx1)), ctx1)
    case SuslikProofStep.Write(Store(to, offset, e)) =>
      IR.Write(CStore(CVar(to.name), offset, translateExpr(e)), Seq(fromRule(node.children.head, ctx)), ctx)
    case SuslikProofStep.Free(Statements.Free(v), size) =>
      IR.Free(CFree(CVar(v.name), size), Seq(fromRule(node.children.head, ctx)), ctx)
    case SuslikProofStep.Malloc(ghostFrom, ghostTo, Statements.Malloc(to, tpe, sz)) =>
      val ctx1 = ctx.copy(substVar = ctx.substVar ++ translateSbstVar(Map(ghostFrom -> ghostTo)))
      IR.Malloc(CMalloc(CVar(to.name), translateType(tpe), sz), Seq(fromRule(node.children.head, ctx1)), ctx1)
    case SuslikProofStep.Call(_, Statements.Call(fun, args, _)) =>
      val ctx1 = ctx.copy(nestedContext = ctx.nestedContext.map(_.applySubstitution))
      val ctx2 = ctx1.copy(nestedContext = None)
      IR.Call(CCall(CVar(fun.name), args.map(translateExpr)), Seq(fromRule(node.children.head, ctx2)), ctx1)
    case SuslikProofStep.PickArg(from, to) =>
      val csbst = translateSbst(Map(from -> to))
      val nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst))
      val sappNames = updateSAppAliases(ctx.sappNames, csbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = nestedContext, sappNames = sappNames)
      fromRule(node.children.head, ctx1)
    case SuslikProofStep.AbduceCall(new_vars, f_pre, callePost, call, companionToFresh, freshToActual, f, gamma) =>
      val cfunspec = translateFunSpec(f, gamma)
      val ccall = CCall(translateVar(call.fun), call.args.map(translateExpr))
      val nestedContext = NestedContext(funspec = cfunspec, call = ccall, freshToActual = translateSbst(freshToActual), companionToFresh = translateSbstVar(companionToFresh))
      val ctx1 = ctx.copy(nestedContext = Some(nestedContext))
      fromRule(node.children.head, ctx1)
    case SuslikProofStep.HeapUnifyPointer(from, to) =>
      val csbst = translateSbst(Map(from -> to))
      val nestedContext = ctx.nestedContext.map(_.updateSubstitution(csbst))
      val sappNames = updateSAppAliases(ctx.sappNames, csbst)
      val ctx1 = ctx.copy(subst = ctx.subst ++ csbst, nestedContext = nestedContext, sappNames = sappNames)
      fromRule(node.children.head, ctx1)
    case SuslikProofStep.EmpRule(_) => IR.EmpRule(ctx)
    case SuslikProofStep.CheckPost(prePhi, postPhi) =>
      IR.CheckPost(prePhi.conjuncts.map(translateExpr), postPhi.conjuncts.map(translateExpr), Seq(fromRule(node.children.head, ctx)), ctx)
    case SuslikProofStep.Inconsistency(_) => IR.Inconsistency(ctx)
    // unused rules:
    case SuslikProofStep.HeapUnify(_) => fromRule(node.children.head, ctx)
    case SuslikProofStep.NilNotLval(_) => fromRule(node.children.head, ctx)
    case SuslikProofStep.WeakenPre(_) => fromRule(node.children.head, ctx)
    case SuslikProofStep.StarPartial(_, _) => fromRule(node.children.head, ctx)
    case SuslikProofStep.PickCard(_, _) => fromRule(node.children.head, ctx)
    case SuslikProofStep.FrameUnfold(h_pre, h_post) => fromRule(node.children.head, ctx)
  }
}
