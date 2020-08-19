package org.tygus.suslik.certification.targets.vst.translation

import org.tygus.suslik.certification.targets.htt.language.Expressions.CPointsTo
import org.tygus.suslik.certification.targets.vst.clang.CTypes
import org.tygus.suslik.certification.targets.vst.clang.CTypes.VSTCType
import org.tygus.suslik.certification.targets.vst.clang.Expressions.CVar
import org.tygus.suslik.certification.targets.vst.clang.Statements.CProcedureDefinition
import org.tygus.suslik.certification.targets.vst.logic.Formulae.{CDataAt, CSApp, VSTHeaplet}
import org.tygus.suslik.certification.targets.vst.logic.{Proof, ProofTypes}
import org.tygus.suslik.certification.targets.vst.logic.Proof.Expressions.{ProofCBinOp, ProofCBinaryExpr, ProofCBoolConst, ProofCExpr, ProofCIfThenElse, ProofCIntConst, ProofCOpAnd, ProofCOpBoolEq, ProofCOpDiff, ProofCOpImplication, ProofCOpIn, ProofCOpIntEq, ProofCOpIntersect, ProofCOpLeq, ProofCOpLt, ProofCOpMinus, ProofCOpMultiply, ProofCOpNot, ProofCOpOr, ProofCOpPlus, ProofCOpSetEq, ProofCOpSubset, ProofCOpUnaryMinus, ProofCOpUnion, ProofCSetLiteral, ProofCUnOp, ProofCUnaryExpr, ProofCVar}
import org.tygus.suslik.certification.targets.vst.logic.Proof.{FormalCondition, FormalSpecification, IsTrueProp, IsValidInt, IsValidPointerOrNull}
import org.tygus.suslik.certification.targets.vst.logic.ProofTypes.{CoqIntType, CoqListType, CoqNatType, CoqPtrType, VSTProofType}
import org.tygus.suslik.language.Expressions.Var
import org.tygus.suslik.language.{BoolType, CardType, Expressions, Ident, IntSetType, IntType, LocType, SSLType}
import org.tygus.suslik.logic.{Block, FunSpec, Gamma, Heaplet, PointsTo, SApp}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}

import scala.collection.immutable

/** translates suslik proof terms to VST compatible proof terms  */
object ProofTranslation {

  def translate_type(lType: SSLType): VSTProofType =
    lType match {
      case IntType => CoqIntType
      case LocType => CoqPtrType
      case CardType => CoqNatType

      // TODO: WARNING: Suslik has a loose model of memory that allows elements of different types
      // to be allocated in the same block - i.e x :-> [loc; int] - this is technically possible
      // but doesn't mesh well with C in which an allocated array must have all elements of the same type
      // otherwise a separate struct definition would be needed
      case IntSetType => CoqListType(CoqPtrType, None)
    }


  def translate_expression(context: Map[Ident, VSTProofType])(expr: Expressions.Expr): Proof.Expressions.ProofCExpr = {
    def type_expr(left_1: ProofCExpr): VSTProofType = ???

    def translate_binop(op: Expressions.BinOp): ProofCBinOp = {
      op match {
        case op: Expressions.RelOp => op match {
          case Expressions.OpEq => ProofCOpIntEq
          case Expressions.OpBoolEq => ProofCOpBoolEq
          case Expressions.OpLeq => ProofCOpLeq
          case Expressions.OpLt => ProofCOpLt
          case Expressions.OpIn => ProofCOpIn
          case Expressions.OpSetEq => ProofCOpSetEq
          case Expressions.OpSubset => ProofCOpSubset
        }
        case op: Expressions.LogicOp => op match {
          case Expressions.OpAnd => ProofCOpAnd
          case Expressions.OpOr => ProofCOpOr
        }
        case Expressions.OpImplication => ProofCOpImplication
        case Expressions.OpPlus => ProofCOpPlus
        case Expressions.OpMinus => ProofCOpMinus
        case Expressions.OpMultiply => ProofCOpMultiply
        case Expressions.OpUnion => ProofCOpUnion
        case Expressions.OpDiff => ProofCOpDiff
        case Expressions.OpIntersect => ProofCOpIntersect
      }
    }

    expr match {
      case const: Expressions.Const => const match {
        case Expressions.IntConst(value) => ProofCIntConst(value)
        case Expressions.BoolConst(value) => ProofCBoolConst(value)
      }
      case Var(name) => ProofCVar(name, context(name))
      case Expressions.SetLiteral(elems) => {
        ProofCSetLiteral(elems.map(translate_expression(context)))
      }
      case Expressions.UnaryExpr(op, arg) =>
        val top: ProofCUnOp = op match {
          case Expressions.OpNot => ProofCOpNot
          case Expressions.OpUnaryMinus => ProofCOpUnaryMinus
        }
        ProofCUnaryExpr(top, translate_expression(context)(arg))
      case Expressions.BinaryExpr(op, left, right) =>
        val top: ProofCBinOp = translate_binop(op)
        ProofCBinaryExpr(top, translate_expression(context)(left), translate_expression(context)(right))
      case Expressions.IfThenElse(cond, left, right) =>
        ProofCIfThenElse(
          translate_expression(context)(cond),
          translate_expression(context)(left),
          translate_expression(context)(right)
        )
      case Expressions.OverloadedBinaryExpr(overloaded_op, left, right) =>
        val left_1 = translate_expression(context)(left)
        val right_1 = translate_expression(context)(right)
        overloaded_op match {
          case op: Expressions.BinOp =>
            ProofCBinaryExpr(translate_binop(op), left_1, right_1)
          case Expressions.OpOverloadedEq =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpIntEq, left_1, right_1)
              case CoqListType(_, _) =>
                ProofCBinaryExpr(ProofCOpSetEq, left_1, right_1)
              case ProofTypes.CoqPtrType => ??? /// TODO: Handle pointer equality? or fail?
            }
          case Expressions.OpNotEqual =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqIntType =>
                ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpIntEq, left_1, right_1))
              case CoqListType(elem, _) =>
                ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpSetEq, left_1, right_1))
              case ProofTypes.CoqPtrType => ??? // TODO: Handle pointer equality? or fail?
            }
          case Expressions.OpGt =>
            ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpLeq, left_1, right_1))
          case Expressions.OpGeq =>
            ProofCUnaryExpr(ProofCOpNot, ProofCBinaryExpr(ProofCOpLt, left_1, right_1))
          case Expressions.OpOverloadedPlus =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqPtrType => ??? // TODO: handle pointer equality or fail?
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpPlus, left_1, right_1)
              case CoqListType(elem, _) =>
                ProofCBinaryExpr(ProofCOpUnion, left_1, right_1)
            }
          case Expressions.OpOverloadedMinus =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqPtrType => ??? // TODO: handle pointer equality or fail?
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpMinus, left_1, right_1)
              case CoqListType(elem, _) =>
                ProofCBinaryExpr(ProofCOpDiff, left_1, right_1)
            }
          case Expressions.OpOverloadedLeq =>
            val l1_ty: VSTProofType = type_expr(left_1)
            l1_ty match {
              case ProofTypes.CoqPtrType => ??? // TODO: handle pointer equality or fail?
              case ProofTypes.CoqIntType =>
                ProofCBinaryExpr(ProofCOpLeq, left_1, right_1)
              case CoqListType(elem, _) =>
                ProofCBinaryExpr(ProofCOpSubset, left_1, right_1)
            }
          case Expressions.OpOverloadedStar => ??? // TODO: Handle star operation
        }

    }
  }


  def type_expr(context: Map[Ident, VSTProofType]) (cvalue: Proof.Expressions.ProofCExpr) : VSTProofType =
    cvalue match {
      case ProofCVar(name, typ) => typ
      case ProofCIntConst(value) => CoqIntType
      case ProofCSetLiteral(elems) => CoqListType(type_expr(context)(elems.head), Some (elems.length))
      case ProofCIfThenElse(cond, left, right) => type_expr(context)(left)
      case ProofCBinaryExpr(op, left, right) => op match {
        case ProofCOpPlus => CoqIntType
        case ProofCOpMinus => CoqIntType
        case ProofCOpMultiply => CoqIntType
      }
      case ProofCUnaryExpr(op, e) => op match {
        case ProofCOpUnaryMinus => CoqIntType
      }
    }

  def translate_heaplets(context: Map[Ident, VSTProofType])(heaplets: List[Heaplet]): List[VSTHeaplet] = {
    var initial_map: Map[Ident, (List[PointsTo], Option[Block])] = Map.empty

    var (map: Map[Ident, (List[PointsTo], Option[Block])], apps): (Map[Ident, (List[PointsTo], Option[Block])], List[CSApp]) =
      heaplets.foldLeft((initial_map, List(): List[CSApp]))({
        case ((map, acc), ty: Heaplet) =>
          ty match {
            case ty@PointsTo(loc@Var(name), offset, value) =>
              val updated_map = map.get(name) match {
                case None => map.updated(name, (List(ty), None))
                case Some((points_to_acc: List[_], block_acc)) =>
                  map.updated(name, (List(ty) ++ points_to_acc, block_acc))
              }
              (updated_map, acc: List[CSApp])
            case ty@Block(loc@Var(name), sz) =>
              val updated_map = map.get(name) match {
                case None => map.updated(name, (List(), Some(ty)))
                case Some((points_to_acc, None)) => map.updated(name, (points_to_acc, Some(ty)))
              }
              (updated_map, acc: List[CSApp])
            case SApp(pred, args, tag, card) =>
              (map, (List(CSApp(pred, args.map(translate_expression((context))), translate_expression(context)(card))) ++ acc)
              )
          }
      })
    val blocks: List[CDataAt] = map.map({ case (var_nam, (points_to, o_block)) =>
      o_block match {
        case Some((_@Block(loc,sz))) =>
          val loc_pos = translate_expression(context)(loc)
          val o_array : Array[Option[ProofCExpr]] = Array.fill(sz)(None)
          points_to.foreach({case PointsTo(_, offset, value) =>
              o_array.update(offset, Some(translate_expression(context)(value)))
          })
          val elems = o_array.map(_.get).toList
          val elem_type = type_expr(context)(elems.head)
          CDataAt(loc_pos, CoqListType(elem_type, Some(sz)), sz, ProofCSetLiteral(elems))
        case None =>
          assert(
            points_to.length == 1,
            "found multiple points to information (i.e x :-> 1, (x + 1) :-> 2) for a variable without an associated block"
          )
          (points_to.head : PointsTo) match {
            case PointsTo(loc, 0, value) =>
              val c_value = translate_expression(context)(value)
              CDataAt(translate_expression(context)(loc), type_expr(context)(c_value), 0, c_value)
            case PointsTo(_, _, _) =>
              assert(false, "found points to information without a block that references a non-zero element (i.e (x + 1) :-> 2)")
              ???
          }
      }
    }).toList

    blocks.map(_.asInstanceOf[VSTHeaplet]) ++ apps.map(_.asInstanceOf[VSTHeaplet])
  }

  /** translates a Suslik function specification into a proof */
  def translate_conditions(proc: CProcedureDefinition)(goal: Goal): FormalSpecification = {

    val name: Ident = proc.name
    val c_params: Seq[(Ident, VSTCType)] = proc.params.map({ case (CVar(name), cType) => (name, cType) })

    val formal_params: List[(Ident, VSTProofType)] = {
      val c_param_set = c_params.map(_._1).toSet
      goal.universals.map({ case variable@Var(name) => (name, translate_type(goal.gamma(variable))) })
        .filterNot({case (name, _) =>  c_param_set.contains(name)}).toList
    }
    val existential_params: List[(Ident, VSTProofType)] =
      goal.existentials.map({ case variable@Var(name) => (name, translate_type(goal.gamma(variable))) }).toList

    val return_type: VSTCType = proc.rt

    val context = (
      formal_params ++ existential_params ++
        c_params.map({ case (ident, cType) => (ident, ProofTypes.proof_type_of_c_type(cType)) })
      ).toMap

    val precondition: FormalCondition = {
      val pure_conditions =
        goal.pre.phi.conjuncts.map(translate_expression(context))
          .map(IsTrueProp).toList ++ c_params.flatMap({ case (ident, cType) =>
          cType match {
            case CTypes.CIntType => Some(IsValidInt(CVar(ident)))
            case CTypes.CUnitType => None
            case CTypes.CVoidPtrType => Some(IsValidPointerOrNull(CVar(ident)))
          }
      })
      val spatial_conditions: List[VSTHeaplet] =
        translate_heaplets(context)(goal.pre.sigma.chunks)

      FormalCondition(pure_conditions, spatial_conditions)
    }
    val postcondition: FormalCondition = {
      val pure_conditions =
        goal.post.phi.conjuncts.map(translate_expression(context))
          .map(IsTrueProp).toList
      val spatial_conditions =
        translate_heaplets(context)(goal.post.sigma.chunks)
        // goal.post.sigma.chunks.map(translate_heaplet(context)).toList
      FormalCondition(pure_conditions, spatial_conditions)
    }

    FormalSpecification(
      name, c_params, formal_params, existential_params, precondition, postcondition, return_type
    )
  }
}
