// #Sireum
/*
 Copyright (c) 2017-2025, Robby, Kansas State University
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice, this
    list of conditions and the following disclaimer.
 2. Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package org.sireum.anvil

import org.sireum._
import org.sireum.alir.{ControlFlowGraph, MonotonicDataflowFramework, TypeSpecializer}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Reporter
import org.sireum.U32._
import org.sireum.U8._
import org.sireum.anvil.PrinterIndex.U._

object Anvil {

  @datatype class Config(val projectName: String,
                         val memory: Z,
                         val defaultBitWidth: Z,
                         val maxStringSize: Z,
                         val maxArraySize: Z,
                         val customArraySizes: HashMap[AST.Typed, Z],
                         val customConstants: HashMap[QName, AST.Exp],
                         val stackTrace: B,
                         val maxExpDepth: Z,
                         val runtimeCheck: B,
                         val printSize: Z) {
    val shouldPrint: B = printSize > 0
  }

  object Config {
    @strictpure def empty(projectName: String): Config =
      Config(projectName, 512 * 1024, 64, 100, 100, HashMap.empty, HashMap.empty, T, 1, T, 0)
  }

  @sig trait Output {
    def add(isFinal: B, path: => ISZ[String], content: => ST): Unit
  }

  @record class TempCollector(var r: HashSSet[Z]) extends MAnvilIRTransformer {
    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      r = r + o.n
      return MNone()
    }
  }

  @datatype class GlobalInfo(val isScalar: B,
                             val offset: Z,
                             val size: Z,
                             val dataSize: Z,
                             val tipe: AST.Typed,
                             val pos: message.Position)

  @record class TempExpSubstitutor(val substMap: HashMap[Z, AST.IR.Exp], val haltOnNoMapping: B) extends MAnvilIRTransformer {
    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      substMap.get(o.n) match {
        case Some(e) => return MSome(e)
        case _ =>
          if (haltOnNoMapping) {
            halt(s"Infeasible: ${o.n}, $substMap")
          } else {
            return MNone()
          }
      }
    }
  }

  @record class OffsetSubsitutor(val anvil: Anvil,
                                 val localOffsetMap: HashMap[String, Z],
                                 val globalMap: HashSMap[QName, GlobalInfo]) extends MAnvilIRTransformer {
    override def post_langastIRExpLocalVarRef(o: AST.IR.Exp.LocalVarRef): MOption[AST.IR.Exp] = {
      val localOffset = localOffsetMap.get(o.id).get
      val t: AST.Typed = if (anvil.isScalar(o.tipe)) o.tipe else anvil.spType
      return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(
        AST.IR.Exp.Binary(anvil.spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, anvil.spType, o.pos)),
          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(anvil.spType, localOffset, o.pos), o.pos),
        anvil.isSigned(t), anvil.typeByteSize(t), o.prettyST, o.tipe, o.pos)))
    }
    override def post_langastIRExpGlobalVarRef(o: AST.IR.Exp.GlobalVarRef): MOption[AST.IR.Exp] = {
      val globalOffset = AST.IR.Exp.Int(anvil.spType, globalMap.get(o.name).get.offset, o.pos)
      val t: AST.Typed = if (anvil.isScalar(o.tipe)) o.tipe else anvil.spType
      return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(globalOffset, anvil.isSigned(t),
        anvil.typeByteSize(t), o.prettyST, o.tipe, o.pos)))
    }
    override def post_langastIRExpFieldVarRef(o: AST.IR.Exp.FieldVarRef): MOption[AST.IR.Exp] = {
      if (anvil.isSeq(o.receiver.tipe)) {
        assert(o.id == "size")
        return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(
          AST.IR.Exp.Binary(anvil.spType, o.receiver,
            AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(anvil.spType, anvil.typeShaSize, o.pos), o.pos),
          T, anvil.typeByteSize(o.tipe), o.prettyST, o.tipe, o.pos)))
      } else {
        val (ft, offset) = anvil.classSizeFieldOffsets(o.receiver.tipe.asInstanceOf[AST.Typed.Name]).
          _2.get(o.id).get
        val rhsOffset: AST.IR.Exp = if (offset != 0) AST.IR.Exp.Binary(anvil.spType, o.receiver,
          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(anvil.spType, offset, o.pos), o.pos) else o.receiver
        if (anvil.isScalar(ft)) {
          return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(rhsOffset,
            anvil.isSigned(ft), anvil.typeByteSize(ft), st"", ft, o.pos)))
        } else {
          return MSome(rhsOffset)
        }
      }
    }
    override def post_langastIRExpIndexing(o: AST.IR.Exp.Indexing): MOption[AST.IR.Exp] = {
      val seqType = o.exp.tipe.asInstanceOf[AST.Typed.Name]
      val indexType = seqType.args(0)
      val elementType = seqType.args(1)
      val min: Z = anvil.minIndex(indexType)
      var index = o.index
      if (index.tipe != anvil.spType) {
        index = AST.IR.Exp.Type(F, index, anvil.spType, index.pos)
      }
      val indexOffset: AST.IR.Exp = if (min == 0) index else AST.IR.Exp.Binary(
        anvil.spType, index, AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(anvil.spType, min, index.pos), index.pos)
      val elementSize = anvil.typeByteSize(elementType)
      val elementOffset: AST.IR.Exp = if (elementSize == 1) indexOffset else AST.IR.Exp.Binary(anvil.spType,
        indexOffset, AST.IR.Exp.Binary.Op.Mul, AST.IR.Exp.Int(anvil.spType, anvil.typeByteSize(elementType),
          index.pos), index.pos)
      val rhsOffset = AST.IR.Exp.Binary(anvil.spType, o.exp, AST.IR.Exp.Binary.Op.Add, elementOffset, o.exp.pos)
      if (anvil.isScalar(elementType)) {
        return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(rhsOffset,
          anvil.isSigned(elementType), anvil.typeByteSize(elementType), o.prettyST, elementType, o.pos)))
      } else {
        return MSome(rhsOffset)
      }
    }
  }

  @record class TempRenumberer(val map: HashMap[Z, Z]) extends MAnvilIRTransformer {
    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      map.get(o.n) match {
        case Some(n) => return MSome(o(n = n))
        case _ => halt(s"Infeasible: ${o.n}, $map")
      }
    }

    override def post_langastIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      map.get(o.lhs) match {
        case Some(n) => return MSome(o(lhs = n))
        case _ => halt(s"Infeasible: ${o.lhs}, $map")
      }
    }
  }

  @record class AccessPathCollector(var accessPaths: HashSet[ISZ[String]]) extends MAnvilIRTransformer {
    override def pre_langastIRExp(o: AST.IR.Exp): MAnvilIRTransformer.PreResult[AST.IR.Exp] = {
      accessPaths = accessPaths ++ AccessPathCollector.computeAccessPathsExp(o).elements
      return MAnvilIRTransformer.PreResult(continu = F, resultOpt = MNone())
    }
  }

  object AccessPathCollector {
    @strictpure def computeAccessPath(e: AST.IR.Exp, suffix: ISZ[String]): ISZ[String] = e match {
      case e: AST.IR.Exp.FieldVarRef => computeAccessPath(e.receiver, e.id +: suffix)
      case e: AST.IR.Exp.Indexing => computeAccessPath(e.exp, ISZ())
      case e: AST.IR.Exp.LocalVarRef => st"${(e.context.owner :+ e.context.id :+ e.id, ".")}".render +: suffix
      case e: AST.IR.Exp.GlobalVarRef => st"${(e.name, ".")}".render +: suffix
      case e: AST.IR.Exp.Type => computeAccessPath(e.exp, suffix)
      case _ => halt(s"Infeasible: $e")
    }

    def computeAccessPathsExp(exp: AST.IR.Exp): HashSet[ISZ[String]] = {
      var r = HashSet.empty[ISZ[String]]

      def rec(e: AST.IR.Exp): Unit = {
        e match {
          case _: AST.IR.Exp.Bool =>
          case _: AST.IR.Exp.Int =>
          case _: AST.IR.Exp.F32 =>
          case _: AST.IR.Exp.F64 =>
          case _: AST.IR.Exp.R =>
          case _: AST.IR.Exp.String =>
          case _: AST.IR.Exp.EnumElementRef =>
          case _: AST.IR.Exp.Temp =>
          case e: AST.IR.Exp.Unary => rec(e.exp)
          case e: AST.IR.Exp.Type => rec(e.exp)
          case e: AST.IR.Exp.Binary =>
            rec(e.left)
            rec(e.right)
          case e: AST.IR.Exp.LocalVarRef =>
            r = r + computeAccessPath(e, ISZ())
          case e: AST.IR.Exp.FieldVarRef =>
            r = r + computeAccessPath(e, ISZ())
          case e: AST.IR.Exp.GlobalVarRef =>
            r = r + computeAccessPath(e, ISZ())
          case e: AST.IR.Exp.Indexing =>
            rec(e.exp)
            rec(e.index)
          case e: AST.IR.Exp.Apply =>
            for (arg <- e.args) {
              rec(arg)
            }
          case e: AST.IR.Exp.Construct =>
            for (arg <- e.args) {
              rec(arg)
            }
          case e: AST.IR.Exp.Intrinsic =>
            r = r + computeAccessPath(e, ISZ())
          case _: AST.IR.Exp.If => halt("Infeasible")
        }
      }

      rec(exp)
      return r
    }
  }

  @record class CPSubstitutor(var cpSubstMap: HashMap[Z, Z]) extends MAnvilIRTransformer {
    override def post_langastIRBasicBlock(o: AST.IR.BasicBlock): MOption[AST.IR.BasicBlock] = {
      return MSome(o(label = cpSubstMap.get(o.label).get))
    }

    override def post_langastIRJumpIf(o: AST.IR.Jump.If): MOption[AST.IR.Jump] = {
      return MSome(o(thenLabel = cpSubstMap.get(o.thenLabel).get, elseLabel = cpSubstMap.get(o.elseLabel).get))
    }

    override def post_langastIRJumpSwitch(o: AST.IR.Jump.Switch): MOption[AST.IR.Jump] = {
      val dOpt: Option[Z] = o.defaultLabelOpt match {
        case Some(l) => Some(cpSubstMap.get(l).get)
        case _ => None()
      }
      return MSome(o(cases = for (c <- o.cases) yield c(label = cpSubstMap.get(c.label).get), defaultLabelOpt = dOpt))
    }

    override def post_langastIRJumpGoto(o: AST.IR.Jump.Goto): MOption[AST.IR.Jump] = {
      return MSome(o(label = cpSubstMap.get(o.label).get))
    }

    override def post_langastIRStmtIntrinsic(o: AST.IR.Stmt.Intrinsic): MOption[AST.IR.Stmt.Ground] = {
      o.intrinsic match {
        case in@Intrinsic.Store(AST.IR.Exp.Intrinsic(_: Intrinsic.Register), _, _, i@AST.IR.Exp.Int(_, cp, _), _, _, _) =>
          return MSome(o(intrinsic = in(rhs = i(value = cpSubstMap.get(cp).get))))
        case _ =>
      }
      return MNone()
    }

    override def post_langastIRJumpHalt(o: AST.IR.Jump.Halt): MOption[AST.IR.Jump] = {
      return MSome(AST.IR.Jump.Goto(errorLabel, o.pos))
    }
  }

  @record class RegisterDetector(var hasSP: B, var hasDP: B) extends MAnvilIRTransformer {
    override def postIntrinsicRegister(o: Intrinsic.Register): MOption[Intrinsic.Register] = {
      if (o.isSP) {
        hasSP = T
      } else {
        hasDP = T
      }
      return MNone()
    }
  }

  @record class StmtFilter(val anvil: Anvil) extends MAnvilIRTransformer {
    override def post_langastIRStmtBlock(o: AST.IR.Stmt.Block): MOption[AST.IR.Stmt] = {
      var changed = F
      var stmts = ISZ[AST.IR.Stmt]()
      for (stmt <- o.stmts) {
        stmt match {
          case _: AST.IR.Stmt.Assertume if !anvil.config.runtimeCheck => changed = T
          case _: AST.IR.Stmt.Print if !anvil.config.shouldPrint => changed = T
          case _ => stmts = stmts :+ stmt
        }
      }
      return if (changed) MSome(o(stmts = stmts)) else MNone()
    }
  }

  @record class ExtMethodCollector(val anvil: Anvil,
                                   var nameMap: HashSMap[QName, ISZ[message.Position]]) extends MAnvilIRTransformer {
    override def post_langastIRExpApply(o: AST.IR.Exp.Apply): MOption[AST.IR.Exp] = {
      anvil.th.nameMap.get(o.owner :+ o.id) match {
        case Some(info: Info.ExtMethod) =>
          val name = info.name
          val poss = nameMap.get(name).getOrElse(ISZ())
          nameMap = nameMap + name ~> (poss :+ o.pos)
        case _ =>
      }
      return MNone()
    }
  }

  @record class ConversionsTransformer(val anvil: Anvil) extends MAnvilIRTransformer {
    override def post_langastIRStmtBlock(o: AST.IR.Stmt.Block): MOption[AST.IR.Stmt] = {
      @strictpure def isConversions(name: QName): B =
        (name.size > 3  && name(0) == "org" && name(1) == "sireum" && name(2) == "conversions") ||
          name == ISZ("org", "sireum", "anvil", "Printer", "Ext")
      var changed = F
      var stmts = ISZ[AST.IR.Stmt]()
      for (stmt <- o.stmts) {
        stmt match {
          case stmt@AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.Apply, pos) if isConversions(rhs.owner) =>
            val objectOps = ops.StringOps(rhs.owner(rhs.owner.size - 1))
            val idOps = ops.StringOps(rhs.id)
            assert(rhs.args.size == 1)
            val arg = rhs.args(0)
            if (idOps.s == "z2u") {
              val cond = AST.IR.Exp.Binary(AST.Typed.b, AST.IR.Exp.Int(AST.Typed.z, 0, pos), AST.IR.Exp.Binary.Op.Le,
                arg, pos)
              stmts = stmts :+ AST.IR.Stmt.Assertume(F, cond, Some(AST.IR.ExpBlock(ISZ(), AST.IR.Exp.String(
                st"Out of bound ${rhs.tipe} value".render, pos))), pos)
              stmts = stmts :+ stmt(rhs = AST.IR.Exp.Type(F, rhs.args(0), AST.Typed.z, pos))
            } else if (idOps.s == "u2z") {
              stmts = stmts :+ stmt(rhs = AST.IR.Exp.Type(F, rhs.args(0), AST.Typed.z, pos))
            } else if (idOps.startsWith("toRaw")) {
              val (t, mask): (AST.Typed.Name, AST.IR.Exp.Int) = anvil.typeByteSize(arg.tipe) match {
                case z"1" => (AST.Typed.u8, AST.IR.Exp.Int(AST.Typed.u8, 0xFF, pos))
                case z"2" => (AST.Typed.u16, AST.IR.Exp.Int(AST.Typed.u16, 0xFFFF, pos))
                case z"4" => (AST.Typed.u32, AST.IR.Exp.Int(AST.Typed.u32, 0xFFFFFFFF, pos))
                case z"8" => (AST.Typed.u64, AST.IR.Exp.Int(AST.Typed.u64, 0xFFFFFFFFFFFFFFFFL, pos))
                case n => halt(s"Infeasible: $n")
              }
              var r: AST.IR.Exp = AST.IR.Exp.Binary(t, AST.IR.Exp.Type(F, arg, t, pos), AST.IR.Exp.Binary.Op.And,
                mask, pos)
              if (t != rhs.tipe) {
                r = AST.IR.Exp.Type(F, r, rhs.tipe.asInstanceOf[AST.Typed.Name], pos)
              }
              stmts = stmts :+ stmt(rhs = r)
            } else {
              objectOps.s match {
                case string"String" =>
                  idOps.s match {
                    case string"toU8is" => stmts = stmts :+ stmt(rhs = rhs.args(0))
                    case _ => halt(s"TODO: ${stmt.prettyST.render}")
                  }
                case string"ISB" => halt(s"TODO: ${stmt.prettyST.render}")
                case string"MSB" => halt(s"TODO: ${stmt.prettyST.render}")
                case _ =>
                  if (idOps.s == "toCodePoints") {
                    halt(s"TODO: ${stmt.prettyST.render}")
                  } else if (idOps.startsWith("to")) {
                    if (rhs.tipe == AST.Typed.z) {
                      stmts = stmts :+ stmt(rhs = AST.IR.Exp.Type(F, arg, AST.Typed.z, pos))
                    } else {
                      if (anvil.config.runtimeCheck) {
                        val ct: AST.Typed.Name = if (anvil.isSigned(arg.tipe)) AST.Typed.s64 else AST.Typed.u64
                        var cond: AST.IR.Exp = AST.IR.Exp.Bool(T, pos)
                        val (argMinOpt, argMaxOpt) = anvil.minMaxOpt(arg.tipe)
                        val (rMinOpt, rMaxOpt) = anvil.minMaxOpt(rhs.tipe)
                        (argMinOpt, rMinOpt) match {
                          case (_, None()) =>
                          case (Some(argMin), Some(rMin)) if rMin <= argMin =>
                          case (_, Some(rMin)) =>
                            arg match {
                              case arg: AST.IR.Exp.Int if arg.value >= rMin =>
                              case _ =>
                                var c: AST.IR.Exp = if (ct == arg.tipe) arg else AST.IR.Exp.Type(F, arg, ct, pos)
                                c = AST.IR.Exp.Binary(AST.Typed.b, AST.IR.Exp.Int(ct, rMin, pos), AST.IR.Exp.Binary.Op.Le,
                                  c, pos)
                                cond = c
                            }
                        }
                        (argMaxOpt, rMaxOpt) match {
                          case (_, None()) =>
                          case (Some(argMax), Some(rMax)) if rMax >= argMax =>
                          case (_, Some(rMax)) =>
                            arg match {
                              case arg: AST.IR.Exp.Int if arg.value <= rMax =>
                              case _ =>
                                var c: AST.IR.Exp = if (ct == arg.tipe) arg else AST.IR.Exp.Type(F, arg, ct, pos)
                                c = AST.IR.Exp.Binary(AST.Typed.b, c, AST.IR.Exp.Binary.Op.Le,
                                  AST.IR.Exp.Int(ct, rMax, pos), pos)
                                cond = if (cond.isInstanceOf[AST.IR.Exp.Bool]) c else AST.IR.Exp.Binary(AST.Typed.b, cond,
                                  AST.IR.Exp.Binary.Op.And, c, pos)
                            }
                        }
                        if (!cond.isInstanceOf[AST.IR.Exp.Bool]) {
                          stmts = stmts :+ AST.IR.Stmt.Assertume(F, cond, Some(AST.IR.ExpBlock(ISZ(), AST.IR.Exp.String(
                            st"Out of bound ${rhs.tipe} value".render, pos))), pos)
                        }
                      }
                      stmts = stmts :+ stmt(rhs = AST.IR.Exp.Type(F, arg, rhs.tipe.asInstanceOf[AST.Typed.Name], pos))
                    }
                  } else {
                    halt(s"TODO: $stmt")
                  }
              }
            }
            changed = T
          case _ => stmts = stmts :+ stmt
        }
      }
      return if (changed) MSome(o(stmts = stmts)) else MNone()
    }
  }

  @record class RuntimeCheckInserter(val anvil: Anvil) extends MAnvilIRTransformer {
    override def post_langastIRStmtBlock(o: AST.IR.Stmt.Block): MOption[AST.IR.Stmt] = {
      if (!anvil.config.runtimeCheck) {
        return MNone()
      }
      var changed = F
      var stmts = ISZ[AST.IR.Stmt]()
      for (stmt <- o.stmts) {
        stmt match {
          case stmt@AST.IR.Stmt.Assign.Temp(lhs, rhs, pos) =>
            def addRangeCheck(): Unit = {
              stmts = stmts :+ stmt
              if (anvil.isBitVector(rhs.tipe)) {
                return
              }
              val (minOpt, maxOpt) = anvil.minMaxOpt(rhs.tipe)
              if (minOpt.isEmpty || maxOpt.isEmpty) {
                return
              }
              var cond: AST.IR.Exp = AST.IR.Exp.Bool(T, pos)
              val temp = AST.IR.Exp.Temp(lhs, rhs.tipe, pos)
              minOpt match {
                case Some(min) =>
                  cond = AST.IR.Exp.Binary(AST.Typed.b, AST.IR.Exp.Int(rhs.tipe, min, pos), AST.IR.Exp.Binary.Op.Le,
                    temp, pos)
                case _ =>
              }
              maxOpt match {
                case Some(max) =>
                  val c = AST.IR.Exp.Binary(AST.Typed.b, temp, AST.IR.Exp.Binary.Op.Le,
                    AST.IR.Exp.Int(rhs.tipe, max, pos), pos)
                  cond = if (cond.isInstanceOf[AST.IR.Exp.Bool]) c else AST.IR.Exp.Binary(AST.Typed.b, cond,
                    AST.IR.Exp.Binary.Op.And, c, pos)
                case _ =>
              }
              if (!cond.isInstanceOf[AST.IR.Exp.Bool]) {
                changed = T
                stmts = stmts :+ AST.IR.Stmt.Assertume(T, cond, Some(AST.IR.ExpBlock(ISZ(), AST.IR.Exp.String(
                  st"Out of range ${rhs.tipe} value".render, pos))), pos)
              }
            }
            rhs match {
              case rhs: AST.IR.Exp.Binary if rhs.tipe != AST.Typed.b =>
                if (rhs.op == AST.IR.Exp.Binary.Op.Div || rhs.op == AST.IR.Exp.Binary.Op.Rem) {
                  val cond = AST.IR.Exp.Binary(AST.Typed.b, rhs.right, AST.IR.Exp.Binary.Op.Ne,
                    AST.IR.Exp.Int(rhs.right.tipe, 0, pos), pos)
                  changed = T
                  stmts = stmts :+ AST.IR.Stmt.Assertume(T, cond, Some(AST.IR.ExpBlock(ISZ(), AST.IR.Exp.String(
                    st"Division by zero".render, pos))), pos)
                  stmts = stmts :+ stmt
                } else {
                  addRangeCheck()
                }
              case rhs: AST.IR.Exp.Unary if rhs.tipe != AST.Typed.b =>
                addRangeCheck()
              case rhs: AST.IR.Exp.Indexing =>
                val indexType = rhs.tipe.asInstanceOf[AST.Typed.Name].args(0)
                val min = anvil.minIndex(indexType)
                val lo = AST.IR.Exp.Int(rhs.tipe, min, pos)
                var hi: AST.IR.Exp = AST.IR.Exp.FieldVarRef(rhs.exp, "size", AST.Typed.z, pos)
                if (min != 0) {
                  hi = AST.IR.Exp.Binary(AST.Typed.z, hi, AST.IR.Exp.Binary.Op.Sub, lo, pos)
                }
                var hil = rhs.index
                if (hil.tipe != AST.Typed.z) {
                  hil = AST.IR.Exp.Type(F, hil, AST.Typed.z, pos)
                }
                val cond = AST.IR.Exp.Binary(AST.Typed.b,
                  AST.IR.Exp.Binary(AST.Typed.b, lo, AST.IR.Exp.Binary.Op.Le, rhs.index, pos),
                  AST.IR.Exp.Binary.Op.And,
                  AST.IR.Exp.Binary(AST.Typed.b, hil, AST.IR.Exp.Binary.Op.Le, hi, pos),
                  pos)
                changed = T
                stmts = stmts :+ AST.IR.Stmt.Assertume(T, cond, Some(AST.IR.ExpBlock(ISZ(), AST.IR.Exp.String(
                  st"Index out of bounds".render, pos))), pos)
                stmts = stmts :+ stmt
              case _ => stmts = stmts :+ stmt
            }
          case _ => stmts = stmts :+ stmt
        }
      }
      return if (changed) MSome(o(stmts = stmts)) else MNone()
    }
  }

  @datatype class TempLV(val cfg: Graph[Z, Unit]) extends MonotonicDataflowFramework.Basic[Z] {
    @strictpure def isForward: B = F
    @strictpure def isLUB: B = T
    @strictpure def iota: HashSSet[Z] = HashSSet.empty
    @strictpure def init: HashSSet[Z] = HashSSet.empty
    @pure def genGround(g: AST.IR.Stmt.Ground): HashSSet[Z] = {
      val tc = TempCollector(HashSSet.empty)
      g match {
        case g: AST.IR.Stmt.Assign.Temp => tc.transform_langastIRExp(g.rhs)
        case _ => tc.transform_langastIRStmtGround(g)
      }
      return tc.r
    }
    @pure def killGround(g: AST.IR.Stmt.Ground): HashSSet[Z] = {
      g match {
        case g: AST.IR.Stmt.Assign.Temp => return HashSSet.empty[Z] + g.lhs
        case _ => return HashSSet.empty
      }
    }
    @pure def genJump(j: AST.IR.Jump): HashSSet[Z] = {
      val tc = TempCollector(HashSSet.empty)
      tc.transform_langastIRJump(j)
      return tc.r
    }
    @strictpure def killJump(j: AST.IR.Jump): HashSSet[Z] = HashSSet.empty
  }

  val kind: String = "Anvil"
  val exitLabel: Z = 0
  val errorLabel: Z = 1
  val startingLabel: Z = 3
  val returnLocalId: String = "$ret"
  val resultLocalId: String = "$res"
  val constructLocalId: String = "$new"
  val typeFieldId: String = "$type"
  val objInitId: String = "<objinit>"
  val newInitId: String = "<init>"
  val displayId: String = "$display"
  val displayName: ISZ[String] = ISZ(displayId)
  val displayIndexType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "anvil", "PrinterIndex", "U"), ISZ())
  val displayType: AST.Typed.Name = AST.Typed.Name(AST.Typed.msName, ISZ(displayIndexType, AST.Typed.u8))
  val f32DigitIndexType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "anvil", "PrinterIndex", "I50"), ISZ())
  val f64DigitIndexType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "anvil", "PrinterIndex", "I320"), ISZ())
  val f32DigitBufferType: AST.Typed.Name = AST.Typed.Name(AST.Typed.msName, ISZ(f32DigitIndexType, AST.Typed.u8))
  val f64DigitBufferType: AST.Typed.Name = AST.Typed.Name(AST.Typed.msName, ISZ(f64DigitIndexType, AST.Typed.u8))
  val printerName: QName = AST.Typed.sireumName :+ "anvil" :+ "Printer"
  val printTypeMap: HashSMap[String, AST.Typed.Fun] = HashSMap.empty[String, AST.Typed.Fun] +
    "printB" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.b), AST.Typed.u64) +
    "printC" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.c), AST.Typed.u64) +
    "printS64" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.s64), AST.Typed.u64) +
    "printU64" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.u64), AST.Typed.u64) +
    "printU64Hex" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.u64, AST.Typed.z), AST.Typed.u64) +
    "f32Digit" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(f32DigitBufferType, f32DigitIndexType, AST.Typed.f32), AST.Typed.u64) +
    "f64Digit" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(f64DigitBufferType, f64DigitIndexType, AST.Typed.f64), AST.Typed.u64) +
    "printF32_2" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.f32), AST.Typed.u64) +
    "printF64_2" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.f64), AST.Typed.u64) +
    "printString" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.string), AST.Typed.u64)

  def synthesize(fresh: lang.IRTranslator.Fresh, th: TypeHierarchy, owner: QName, id: String, config: Config,
                 output: Output, reporter: Reporter): Unit = {
    assert(config.memory > 0 && config.memory % 8 == 0, s"Memory configuration has to be a positive integer multiples of 8")
    val tsr = TypeSpecializer.specialize(th, ISZ(TypeSpecializer.EntryPoint.Method(owner :+ id)), HashMap.empty,
      reporter)
    if (tsr.extMethods.nonEmpty) {
      reporter.error(None(), kind, s"@ext methods are not supported")
    }
    if (reporter.hasError) {
      return
    }
    fresh.setTemp(0)
    fresh.setLabel(startingLabel)
    Anvil(th, tsr, owner, id, config, 0).synthesize(fresh, output, reporter)
  }
}

import Anvil._

@datatype class Anvil(val th: TypeHierarchy,
                      val tsr: TypeSpecializer.Result,
                      val owner: QName,
                      val id: String,
                      val config: Config,
                      val numOfLocs: Z) {

  val typeShaType: AST.Typed.Name = AST.Typed.u32
  val typeShaSize: Z = typeByteSize(typeShaType)
  val spType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "SP"), ISZ())
  val cpType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "CP"), ISZ())
  val dpType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "DP"), ISZ())
  val dpMask: Z = {
    val size = anvil.Printer.Ext.z2u(config.printSize)
    var r = u"2"
    while (r < size) {
      r = r << u"1"
    }
    r = r - u"1"
    anvil.Printer.Ext.u2z(r)
  }

  val spTypeByteSize: Z = {
    val n = computeBitwidth(config.memory) + 1
    if (n % 8 == 0) n / 8 else (n / 8) + 1
  }
  val dpTypeByteSize: Z = 8
  @memoize def cpTypeByteSize: Z = {
    assert(numOfLocs != 0, "Number of locations for CP has not been initialized")
    val n = computeBitwidth(numOfLocs) + 1
    return if (n % 8 == 0) n / 8 else (n / 8) + 1
  }

  @strictpure def irProcedurePath(procedureId: String, pType: AST.Typed.Fun, stage: Z, pass: Z, id: String): ISZ[String] =
    ISZ("ir", "procedures", s"$procedureId-${sha3(pType.string)}-$stage-$pass-$id.sir")

  def synthesize(fresh: lang.IRTranslator.Fresh, output: Output, reporter: Reporter): Unit = {
    val threeAddressCode = T

    val irt = lang.IRTranslator(threeAddressCode = threeAddressCode, threeAddressCodeLit = F,
      th = tsr.typeHierarchy, fresh = fresh)

    var stage: Z = 0

    val mq: (AST.IR.MethodContext, AST.IR.Program, Z, HashSMap[ISZ[String], GlobalInfo]) = {
      var globals = ISZ[AST.IR.Global]()
      var procedures = ISZ[AST.IR.Procedure]()
      var globalSize: Z = 0

      var mainOpt = Option.none[AST.IR.Procedure]()
      for (ms <- tsr.methods.values; m <- ms.elements) {
        val receiverOpt: Option[AST.Typed] = m.receiverOpt match {
          case Some(t) => Some(t)
          case _ => None()
        }
        val p = irt.translateMethod(F, receiverOpt, m.info.owner, m.info.ast)
        procedures = procedures :+ p
        if (m.info.owner == owner && m.info.ast.sig.id.value == id) {
          mainOpt = Some(p)
        }
      }
      for (t <- tsr.typeImpl.nodes.keys) {
        val stmts = classInit(t)
        if (stmts.nonEmpty) {
          val posOpt = th.typeMap.get(t.ids).get.posOpt
          procedures = procedures :+ irt.translateMethodH(F, Some(t), t.ids, newInitId, ISZ(),
            ISZ("this"), AST.Typed.Fun(AST.Purity.Impure, F, ISZ(t), AST.Typed.unit), posOpt.get,
            Some(AST.Body(stmts, ISZ())))
        }
      }
      if (config.shouldPrint) {
        globals = globals :+ AST.IR.Global(displayType, displayName, mainOpt.get.pos)
        for (id <- printTypeMap.keys) {
          val info = th.nameMap.get(printerName :+ id).get.asInstanceOf[Info.Method]
          procedures = procedures :+ irt.translateMethod(F, None(), info.owner, info.ast)
        }
      }
      for (vs <- tsr.objectVars.entries) {
        val (owner, ids) = vs
        var objPosOpt: Option[message.Position] = th.nameMap.get(owner) match {
          case Some(info: Info.Object) => Some(info.posOpt.get)
          case _ => None()
        }
        globals = globals :+ AST.IR.Global(AST.Typed.b, owner, objPosOpt.get)
        var stmts = ISZ[AST.Stmt]()
        for (id <- ids.elements) {
          val name = owner :+ id
          val v = th.nameMap.get(name).get.asInstanceOf[Info.Var]
          globals = globals :+ AST.IR.Global(v.typedOpt.get, name, v.posOpt.get)
          if (objPosOpt.isEmpty) {
            objPosOpt = v.posOpt
          }
          stmts = stmts :+ AST.Stmt.Assign(AST.Exp.Ident(v.ast.id, AST.ResolvedAttr(v.posOpt, v.resOpt, v.typedOpt)),
            v.ast.initOpt.get, AST.Attr(v.posOpt))
        }
        val pos = objPosOpt.get
        val objInit = irt.translateMethodH(F, None(), owner, objInitId, ISZ(), ISZ(),
          AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.unit), pos, Some(AST.Body(stmts, ISZ())))
        var body = objInit.body.asInstanceOf[AST.IR.Body.Block]
        body = body(block = body.block(stmts =
          AST.IR.Stmt.Assign.Global(owner, AST.Typed.b, AST.IR.Exp.Bool(T, pos), pos) +: body.block.stmts))
        procedures = procedures :+ objInit(body = body)
      }
      var globalMap = HashSMap.empty[ISZ[String], GlobalInfo]
      val spSize = typeByteSize(spType)
      for (g <- globals) {
        val size = typeByteSize(g.tipe)
        if (!isScalar(g.tipe)) {
          globalMap = globalMap + g.name ~> GlobalInfo(F, globalSize, spSize, size, g.tipe, g.pos)
          globalSize = globalSize + spSize
        } else {
          globalMap = globalMap + g.name ~> GlobalInfo(T, globalSize, size, 0, g.tipe, g.pos)
        }
        globalSize = globalSize + size
      }
      (mainOpt.get.context, AST.IR.Program(threeAddressCode, globals, procedures), globalSize, globalMap)
    }

    val mainContext = mq._1
    var program = mq._2
    val globalSize = mq._3
    val globalMap = mq._4

    output.add(F, ISZ("ir", s"$stage-initial.sir"), program.prettyST)

    stage = stage + 1

    program = program(procedures = ops.ISZOps(program.procedures).mParMap(
      (p: AST.IR.Procedure) => transformBlock(stage, output, p)))

    program = program(procedures = for (p <- program.procedures) yield
      p(body = irt.toBasic(p.body.asInstanceOf[AST.IR.Body.Block], p.pos)))

    output.add(F, ISZ("ir", s"$stage-basic.sir"), program.prettyST)

    stage = stage + 1

    program = transformBasicBlock(stage, fresh, program, output)
    output.add(F, ISZ("ir", s"$stage-transformed.sir"), program.prettyST)

    stage = stage + 1

    val numOfLocs: Z = ops.ISZOps(for (p <- program.procedures)
      yield p.body.asInstanceOf[AST.IR.Body.Basic].blocks.size).foldLeft[Z]((r: Z, n: Z) => r + n, 0)
    val anvil = Anvil(th, tsr, owner, id, config, numOfLocs + 1)

    var procedureMap = HashSMap.empty[AST.IR.MethodContext, AST.IR.Procedure]
    var procedureSizeMap = HashMap.empty[AST.IR.MethodContext, Z]
    var callResultOffsetMap = HashMap.empty[String, Z]
    program = {
      for (p <- program.procedures) {
        val (maxOffset, p2, m) = anvil.transformOffset(globalMap, p)
        callResultOffsetMap = callResultOffsetMap ++ m.entries
        var proc = p2
        var pass: Z = 0

        output.add(F, irProcedurePath(proc.id, proc.tipe, stage, pass, "offset"), proc.prettyST)
        pass = pass + 1

        if (config.maxExpDepth != 1) {
          proc = anvil.transformReduceExp(proc)
          output.add(F, irProcedurePath(proc.id, proc.tipe, stage, pass, "reduce-exp"), proc.prettyST)
          pass = pass + 1

          proc = anvil.transformTempCompress(proc)
          output.add(F, irProcedurePath(proc.id, proc.tipe, stage, pass, "temp-compress"), proc.prettyST)
          pass = pass + 1
        }
        procedureMap = procedureMap + proc.context ~> proc
        procedureSizeMap = procedureSizeMap + p2.context ~> maxOffset
      }
      program(procedures = procedureMap.values)
    }
    output.add(F, ISZ("ir", s"$stage-offset.sir"), program.prettyST)

    stage = stage + 1

    val maxRegisters: Z = {
      val tc = TempCollector(HashSSet.empty)
      tc.transform_langastIRProgram(program)
      tc.r.elements.size
    }

    val main = procedureMap.get(mainContext).get
    program = {
      val p = main(body = main.body.asInstanceOf[AST.IR.Body.Basic](blocks =
        anvil.mergeProcedures(main, fresh, procedureMap, procedureSizeMap, callResultOffsetMap, maxRegisters)))
      output.add(F, irProcedurePath(p.id, p.tipe, stage, 0, "merged"), p.prettyST)
      program(procedures = ISZ(p))
    }
    output.add(F, ISZ("ir", s"$stage-merged.sir"), program.prettyST)

    stage = stage + 1

    program = {
      var p = program.procedures(0)
      var pass: Z = 0

      p = anvil.transformRegisterInc(fresh, p)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "register-inc"), p.prettyST)
      pass = pass + 1

      p = anvil.transformMergeRegisterInc(p)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "merge-register-inc"), p.prettyST)
      pass = pass + 1

      p = anvil.transformMain(fresh, p, globalSize, globalMap)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "main"), p.prettyST)
      pass = pass + 1

      p = anvil.transformCP(p)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "cp"), p.prettyST)
      pass = pass + 1

      program(procedures = ISZ(p))
    }

    {
      val emc = ExtMethodCollector(this, HashSMap.empty)
      emc.transform_langastIRProgram(program)
      for (pair <- emc.nameMap.entries) {
        val (name, poss) = pair
        for (pos <- poss) {
          reporter.error(Some(pos), kind, st"Extension method ${(name, ".")} is not currently handled".render)
        }
      }
    }

    val header: ST = {
      var offset: Z = anvil.typeByteSize(cpType)
      val resOpt: Option[ST] =
        if (main.tipe.ret != AST.Typed.unit) {
          offset = offset + anvil.typeByteSize(spType) + anvil.typeByteSize(main.tipe.ret)
          Some(
            st"- $$res (*(SP + ${anvil.typeByteSize(cpType)})) = ${globalSize + anvil.typeByteSize(cpType) + anvil.typeByteSize(spType)} (${anvil.signedString(spType)}, size = ${anvil.typeByteSize(spType)}, data-size = ${anvil.typeByteSize(main.tipe.ret)})")
        } else {
          None()
        }
      var globalParamSTs = ISZ[ST]()
      for (pair <- globalMap.entries) {
        val (name, info) = pair
        globalParamSTs = globalParamSTs :+ st"- global ${(name, ".")}: ${info.tipe} @[offset = ${info.offset}, size = ${info.size}, data-size = ${info.dataSize}]"
      }
      for (param <- ops.ISZOps(main.paramNames).zip(main.tipe.args)) {
        if (!isScalar(param._2)) {
          globalParamSTs = globalParamSTs :+ st"- for parameter ${param._1}: *(SP + $offset) = ${globalSize + offset + anvil.typeByteSize(spType)} (${if (anvil.isSigned(spType)) "signed" else "unsigned"}, size = ${anvil.typeByteSize(spType)}, data-size = ${anvil.typeByteSize(param._2)})"
          offset = offset + anvil.typeByteSize(spType) + anvil.typeByteSize(param._2)
        } else {
          offset = offset + anvil.typeByteSize(param._2)
        }
      }
      st"""/*
          |   Note that globalSize = $globalSize, max registers (beside SP and CP) = $maxRegisters, and initially:
          |   - register CP (code pointer) = 2 (${anvil.signedString(cpType)}, byte size = ${anvil.typeByteSize(cpType)})
          |   - register SP (stack pointer) = $globalSize (${anvil.signedString(spType)}, byte size = ${anvil.typeByteSize(spType)})
          |   - register DP (display pointer) = 0 (${anvil.signedString(dpType)}, byte size = ${anvil.typeByteSize(dpType)})
          |   - $$ret (*SP) = 0 (signed, byte size = ${anvil.typeByteSize(cpType)})
          |   $resOpt
          |   ${(globalParamSTs, "\n")}
          |
          |   Also note that IS/MS bytearray consists of:
          |   - the first 4 bytes of the IS/MS type string SHA3 encoding
          |     (e.g., for "org.sireum.MS[Z, U8]", it is 0xEF2BFABD)
          |   - 8 bytes for .size
          |   - IS/MS element bytes
          |
          |   A @datatype/@record class bytearray consists of:
          |   - the first 4 bytes of the class type string SHA3 encoding
          |   - the class field bytes
          |
          |   decl/undecl and alloc/dealloc are the same except alloc/dealloc store raw data only,
          |   while decl/undecl may store raw data and/or stack pointer.
          | */"""

    }

    output.add(F, ISZ("ir", s"$stage-reordered.sir"),
      st"""$header
          |${program.prettyST}""")

    stage = stage + 1

    {
      val nlocs = program.procedures(0).body.asInstanceOf[AST.IR.Body.Basic].blocks.size
      val cpMax = pow(2, anvil.typeByteSize(cpType) * 8)
      assert(nlocs <= cpMax, s"nlocs ($nlocs) > cpMax (2 ** (${anvil.typeByteSize(cpType) * 8}) == $cpMax)")
    }

    HwSynthesizer(anvil).printProcedure(id, program.procedures(0), output, maxRegisters)
  }

  @pure def transformBlock(stage: Z, output: Output, p: AST.IR.Procedure): AST.IR.Procedure = {
    var pass: Z = 0
    var r = p

    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "initial"), r.prettyST)
    pass = pass + 1

    r = ConversionsTransformer(this).transform_langastIRProcedure(r).getOrElse(r)
    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "conversions"), r.prettyST)
    pass = pass + 1

    r = RuntimeCheckInserter(this).transform_langastIRProcedure(r).getOrElse(r)
    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "runtime-check"), r.prettyST)
    pass = pass + 1

    r = StmtFilter(this).transform_langastIRProcedure(r).getOrElse(r)
    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "stmt-filter"), r.prettyST)
    pass = pass + 1

    return r
  }

  def transformEmptyBlock(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    var map = HashMap.empty[Z, Z]
    for (b <- body.blocks) {
      b.jump match {
        case j: AST.IR.Jump.Goto if b.grounds.isEmpty => map = map + b.label ~> j.label
        case _ =>
      }
    }
    if (map.isEmpty) {
      return p
    }
    def getTarget(l: Z): Z = {
      map.get(l) match {
        case Some(l2) => return getTarget(l2)
        case _ => return l
      }
    }
    for (b <- body.blocks) {
      val jump: AST.IR.Jump = b.jump match {
        case j: AST.IR.Jump.If => j(thenLabel = getTarget(j.thenLabel), elseLabel = getTarget(j.elseLabel))
        case j: AST.IR.Jump.Switch =>
          val dOpt: Option[Z] = j.defaultLabelOpt match {
            case Some(l) => Some(getTarget(l))
            case _ => None()
          }
          j(cases = for (c <- j.cases) yield c(label = getTarget(c.label)), defaultLabelOpt = dOpt)
        case j: AST.IR.Jump.Goto => j(label = getTarget(j.label))
        case j: AST.IR.Jump.Return => j
        case j: AST.IR.Jump.Intrinsic => j
        case j: AST.IR.Jump.Halt => j
      }
      blockMap = blockMap + b.label ~> b(jump = jump)
    }
    blockMap = blockMap -- map.keys
    return p(body = body(blocks = blockMap.values))
  }

  def transformSplitTest(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure,
                         test: AST.IR.Stmt.Ground => B @pure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var block = b
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        if (test(g)) {
          if (grounds.isEmpty) {
            val n = fresh.label()
            blocks = blocks :+ AST.IR.BasicBlock(block.label, ISZ(g), AST.IR.Jump.Goto(n, g.pos))
            grounds = ISZ()
            block = AST.IR.BasicBlock(n, grounds, block.jump)
          } else {
            val n = fresh.label()
            val m = fresh.label()
            blocks = blocks :+ AST.IR.BasicBlock(block.label, grounds, AST.IR.Jump.Goto(n, g.pos))
            blocks = blocks :+ AST.IR.BasicBlock(n, ISZ(g), AST.IR.Jump.Goto(m, g.pos))
            grounds = ISZ()
            block = AST.IR.BasicBlock(m, grounds, block.jump)
          }
        } else {
          grounds = grounds :+ g
        }
      }
      blocks = blocks :+ block(grounds = grounds)
    }
    return transformEmptyBlock(p(body = body(blocks = blocks)))
  }

  def transformCP(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var cpSubstMap = HashMap.empty[Z, Z]
    for (i <- 0 until startingLabel) {
      cpSubstMap = cpSubstMap + i ~> i
    }
    var blockMap = HashSMap.empty[Z, AST.IR.BasicBlock] ++ (for (b <- body.blocks) yield (b.label, b))
    var blocks = ISZ[AST.IR.BasicBlock]()
    var work = ISZ(body.blocks(0))
    while (work.nonEmpty || blockMap.nonEmpty) {
      if (work.isEmpty) {
        val bs = blockMap.entries
        work = ISZ(bs(0)._2)
        blockMap = HashSMap.empty[Z, AST.IR.BasicBlock] ++ ops.ISZOps(bs).drop(1)
      }
      val b = work(work.size - 1)
      work = ops.ISZOps(work).dropRight(1)
      blocks = blocks :+ b
      blockMap = blockMap -- ISZ(b.label)
      for (target <- ops.ISZOps(b.jump.targets).reverse) {
        blockMap.get(target) match {
          case Some(b2) => work = work :+ b2
          case _ =>
        }
      }
    }

    for (b <- blocks) {
      if (b.label >= startingLabel) {
        cpSubstMap = cpSubstMap + b.label ~> cpSubstMap.size
      }
    }
    return transformEmptyBlock(CPSubstitutor(cpSubstMap).
      transform_langastIRProcedure(p(body = body(blocks = blocks))).getOrElse(p))
  }

  def transformSplitReadWrite(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    def areReadWritePathsDisallowed(reads: HashSet[ISZ[String]], writes: HashSet[ISZ[String]]): B = {
      if (reads.isEmpty || writes.isEmpty) {
        return F
      }
      for (w <- writes.elements) {
        val wf = w(0)
        for (r <- reads.elements if wf == r(0)) {
          if (w.size < r.size && w == ops.ISZOps(r).dropRight(r.size - w.size)) {
            return T
          } else if (w.size > r.size && ops.ISZOps(w).dropRight(w.size - r.size) == r) {
            return T
          } else if (w == r) {
            return T
          }
        }
      }
      return F
    }

    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    var tempSubstMap = HashMap.empty[Z, HashMap[Z, AST.IR.Exp]] + body.blocks(0).label ~> HashMap.empty
    var work = ISZ[AST.IR.BasicBlock](body.blocks(0))
    var blocks = ISZ[AST.IR.BasicBlock]()
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.BasicBlock]()
      for (b <- work) {
        var readAccessPaths = HashSet.empty[ISZ[String]]
        var writeAccessPaths = HashSet.empty[ISZ[String]]
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        var substMap = tempSubstMap.get(b.label).get
        var block = b

        def introBlock(pos: message.Position): Unit = {
          if (grounds.isEmpty) {
            return
          }
          val n = fresh.label()
          blocks = blocks :+ AST.IR.BasicBlock(block.label, grounds, AST.IR.Jump.Goto(n, pos))
          grounds = ISZ()
          readAccessPaths = HashSet.empty[ISZ[String]]
          writeAccessPaths = HashSet.empty[ISZ[String]]
          block = AST.IR.BasicBlock(n, grounds, block.jump)
          tempSubstMap = tempSubstMap + n ~> substMap
        }

        def computeWrites(g: AST.IR.Stmt.Ground): Unit = {
          g match {
            case g: AST.IR.Stmt.Assign.Temp =>
              substMap = substMap + g.lhs ~> TempExpSubstitutor(substMap, T).transform_langastIRExp(g.rhs).getOrElse(g.rhs)
            case g: AST.IR.Stmt.Assign.Local => writeAccessPaths = writeAccessPaths +
              ISZ(st"${(g.context.owner :+ g.context.id :+ g.lhs, ".")}".render)
            case g: AST.IR.Stmt.Assign.Field if !g.receiver.isInstanceOf[AST.IR.Exp.Construct] =>
              writeAccessPaths = writeAccessPaths + AccessPathCollector.computeAccessPath(g.receiver, ISZ(g.id))
            case g: AST.IR.Stmt.Assign.Index if !g.receiver.isInstanceOf[AST.IR.Exp.Construct] =>
              writeAccessPaths = writeAccessPaths + AccessPathCollector.computeAccessPath(g.receiver, ISZ())
            case g: AST.IR.Stmt.Assign.Global => writeAccessPaths = writeAccessPaths + ISZ(st"${(g.name, ".")}".render)
            case _ =>
          }
        }

        def computeReads(g: AST.IR.Stmt.Ground): Unit = {
          val rc = AccessPathCollector(readAccessPaths)
          g match {
            case _: AST.IR.Stmt.Assign.Temp =>
            case g: AST.IR.Stmt.Assign => rc.transform_langastIRExp(g.rhs)
            case _ => rc.transform_langastIRStmtGround(g)
          }
          readAccessPaths = rc.accessPaths
        }
        for (ground <- b.grounds) {
          val g = TempExpSubstitutor(substMap, T).transform_langastIRStmtGround(ground).getOrElse(ground)
          computeWrites(g)
          if (writeAccessPaths.nonEmpty) {
            computeReads(g)
            if (areReadWritePathsDisallowed(readAccessPaths, writeAccessPaths)) {
              introBlock(g.pos)
              grounds = grounds :+ ground
              computeWrites(g)
            } else {
              grounds = grounds :+ ground
            }
          } else {
            grounds = grounds :+ ground
          }
        }
        val rc = AccessPathCollector(readAccessPaths)
        rc.transform_langastIRJump(TempExpSubstitutor(substMap, T).transform_langastIRJump(b.jump).getOrElse(b.jump))
        readAccessPaths = rc.accessPaths
        if (areReadWritePathsDisallowed(readAccessPaths, writeAccessPaths)) {
          introBlock(b.jump.pos)
        }
        blocks = blocks :+ block(grounds = grounds, jump = b.jump)
        for (target <- block.jump.targets) {
          tempSubstMap.get(target) match {
            case Some(_) =>
            case _ =>
              next = next :+ blockMap.get(target).get
              tempSubstMap = tempSubstMap + target ~> substMap
          }
        }
      }
      work = next
    }
    return transformEmptyBlock(p(body = body(blocks = blocks)))
  }

  def transformApplyConstructResult(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]

    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      var undeclMap = HashMap.empty[Z, AST.IR.Stmt.Decl]
      for (g <- b.grounds) {
        g match {
          case g: AST.IR.Stmt.Expr if g.exp.methodType.ret != AST.Typed.unit =>
            val decl = AST.IR.Stmt.Decl(F, T, T, p.context, ISZ(
              AST.IR.Stmt.Decl.Local(callResultId(g.exp.id, g.exp.pos), g.exp.tipe)), g.pos)
            grounds = grounds :+ decl
            grounds = grounds :+ g
            grounds = grounds :+ decl.undeclare
          case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
            val e = g.rhs.asInstanceOf[AST.IR.Exp.Apply]
            val decl = AST.IR.Stmt.Decl(F, T, T, p.context, ISZ(
              AST.IR.Stmt.Decl.Local(callResultId(e.id, e.pos), e.tipe)), g.pos)
            grounds = grounds :+ decl
            grounds = grounds :+ g
            undeclMap = undeclMap + g.lhs ~> decl.undeclare
          case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Construct] =>
            val e = g.rhs.asInstanceOf[AST.IR.Exp.Construct]
            val temp = AST.IR.Exp.Temp(g.lhs, e.tipe, e.pos)
            val decl = AST.IR.Stmt.Decl(F, T, T, p.context, ISZ(
              AST.IR.Stmt.Decl.Local(constructResultId(e.pos), e.tipe)), g.pos)
            grounds = grounds :+ decl
            grounds = grounds :+ g
            if (e.tipe.ids == AST.Typed.isName || e.tipe.ids == AST.Typed.msName) {
              val indexType = e.tipe.args(0)
              val min: Z = indexType match {
                case AST.Typed.z => 0
                case _ =>
                  val subz = subZOpt(indexType).get.ast
                  if (subz.isIndex) subz.min
                  else if (subz.isZeroIndex) 0
                  else subz.min
              }
              for (i <- e.args.indices) {
                val arg = e.args(i)
                grounds = grounds :+ AST.IR.Stmt.Assign.Index(temp, AST.IR.Exp.Int(indexType, min + i, arg.pos), arg,
                  arg.pos)
              }
            } else {
              val info = th.typeMap.get(e.tipe.ids).get.asInstanceOf[TypeInfo.Adt]
              val sm = TypeChecker.buildTypeSubstMap(e.tipe.ids, None(), info.ast.typeParams, e.tipe.args,
                message.Reporter.create).get
              for (pair <- ops.ISZOps(info.ast.params).zip(e.args)) {
                grounds = grounds :+ AST.IR.Stmt.Assign.Field(temp, pair._1.id.value,
                  pair._1.tipe.typedOpt.get.subst(sm), pair._2, pair._2.pos)
              }
            }
            if (classInit(e.tipe).nonEmpty) {
              grounds = grounds :+ AST.IR.Stmt.Expr(AST.IR.Exp.Apply(F, e.tipe.ids, newInitId,
                ISZ(temp), AST.Typed.Fun(AST.Purity.Impure, F, ISZ(e.tipe), AST.Typed.unit), AST.Typed.unit, e.pos))
            }
            undeclMap = undeclMap + g.lhs ~> decl.undeclare
          case _ =>
            grounds = grounds :+ g
        }
      }
      var grounds2 = ISZ[AST.IR.Stmt.Ground]()
      for (i <- grounds.size - 1 to 0 by -1) {
        val g = grounds(i)
        val tc = TempCollector(HashSSet.empty)
        tc.transform_langastIRStmtGround(g)
        for (temp <- tc.r.elements) {
          undeclMap.get(temp) match {
            case Some(undecl) =>
              grounds2 = grounds2 :+ undecl
              undeclMap = undeclMap -- ISZ(temp)
            case _ =>
          }
        }
        grounds2 = grounds2 :+ g
      }
      blocks = blocks :+ b(grounds = for (i <- grounds2.size - 1 to 0 by - 1) yield grounds2(i))
    }

    @strictpure def isInvoke(g: AST.IR.Stmt.Ground): B = g match {
      case AST.IR.Stmt.Assign.Temp(_, _: AST.IR.Exp.Apply, _) => T
      case _: AST.IR.Stmt.Expr => T
      case _ => F
    }

    return transformSplitTest(fresh, p(body = body(blocks = blocks)), isInvoke _)
  }

  def transformGlobalVarRef(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      var block = b
      for (g <- b.grounds) {
        g match {
          case g@AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.GlobalVarRef, pos) if rhs.name != displayName =>
            val owner = ops.ISZOps(rhs.name).dropRight(1)
            if (p.owner :+ p.id != owner) {
              val label1 = fresh.label()
              val label2 = fresh.label()
              blocks = blocks :+ AST.IR.BasicBlock(block.label, grounds, AST.IR.Jump.If(AST.IR.Exp.GlobalVarRef(
                owner, AST.Typed.b, pos), label2, label1, pos))
              blocks = blocks :+ AST.IR.BasicBlock(label1, ISZ(AST.IR.Stmt.Expr(AST.IR.Exp.Apply(T, owner, objInitId,
                ISZ(), AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.unit), AST.Typed.unit, pos))),
                AST.IR.Jump.Goto(label2, pos))
              grounds = ISZ(g)
              block = b(label = label2, grounds = grounds)
            } else {
              grounds = grounds :+ g
            }
          case _ => grounds = grounds :+ g
        }
      }
      blocks = blocks :+ block(grounds = grounds)
    }
    return p(body = body(blocks = blocks))
  }

  def transformBasicBlock(stage: Z, fresh: lang.IRTranslator.Fresh, program: AST.IR.Program, output: Output): AST.IR.Program = {
    @pure def transform(p: AST.IR.Procedure): AST.IR.Procedure = {
      var r = p
      var pass: Z = 0

      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "basic"), r.prettyST)
      pass = pass + 1

      r = transformGlobalVarRef(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "global"), r.prettyST)
      pass = pass + 1

      r = transformPrint(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "print"), r.prettyST)
      pass = pass + 1

      r = transformApplyConstructResult(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "apply-construct-result"), r.prettyST)
      pass = pass + 1

      r = transformEmptyBlock(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "empty-block"), r.prettyST)
      pass = pass + 1

      r = transformReduceTemp(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "reduce-temp"), r.prettyST)
      pass = pass + 1

      r = transformReduceExp(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "reduce-exp"), r.prettyST)
      pass = pass + 1

      r = transformTempCompress(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "temp-compress"), r.prettyST)
      pass = pass + 1

      r = transformSplitTemp(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-temp"), r.prettyST)
      pass = pass + 1

      r = transformSplitReadWrite(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-read-write"), r.prettyST)
      pass = pass + 1

      r = transformInstanceOf(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "instanceof"), r.prettyST)
      pass = pass + 1

      r = transformEmptyBlock(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "empty-block"), r.prettyST)
      pass = pass + 1

      return r
    }
    return program(procedures = ops.ISZOps(program.procedures).mParMap(transform _))
  }

  @memoize def callResultId(id: String, pos: message.Position): String = {
    return s"$id$resultLocalId@[${pos.beginLine},${pos.beginColumn}].${sha3(pos.string)}"
  }

  @memoize def constructResultId(pos: message.Position): String = {
    return s"$constructLocalId@[${pos.beginLine},${pos.beginColumn}].${sha3(pos.string)}"
  }

  @pure def countNumOfIncomingJumps(blocks: ISZ[AST.IR.BasicBlock]): HashMap[Z, Z] = {
    var r = HashMap ++ (for (b <- blocks) yield (b.label, z"0"))
    for (b <- blocks; target <- b.jump.targets) {
      r = r + target ~> (r.get(target).get + 1)
    }
    return r
  }

  def mergeProcedures(main: AST.IR.Procedure,
                      fresh: lang.IRTranslator.Fresh,
                      procedureMap: HashSMap[AST.IR.MethodContext, AST.IR.Procedure],
                      procedureSizeMap: HashMap[AST.IR.MethodContext, Z],
                      callResultOffsetMap: HashMap[String, Z],
                      maxRegisters: Z): ISZ[AST.IR.BasicBlock] = {
    var seen = HashSet.empty[AST.IR.MethodContext]
    var work = ISZ[AST.IR.Procedure](main)
    var mergedBlocks = ISZ[AST.IR.BasicBlock]()
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.Procedure]()
      for (p <- work) {
        seen = seen + p.context
        var addBeginningMap = HashSMap.empty[Z, ISZ[AST.IR.Stmt.Ground]]
        var blocks = ISZ[AST.IR.BasicBlock]()
        val body = p.body.asInstanceOf[AST.IR.Body.Basic]
        for (b <- body.blocks) {
          def processInvoke(g: AST.IR.Stmt.Ground, lhsOpt: Option[Z], e: AST.IR.Exp.Apply, label: Z): Unit = {
            val numOfRegisters: Z = lhsOpt match {
              case Some(lhs) => lhs
              case _ => maxRegisters
            }
            val mc = AST.IR.MethodContext(e.isInObject, e.owner, e.id, e.methodType)
            val called = procedureMap.get(mc).get
            if (!seen.contains(mc)) {
              next = next :+ called
            }
            val spAdd = procedureSizeMap.get(p.context).get
            var grounds = ISZ[AST.IR.Stmt.Ground]()
            grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(T, T,
              AST.IR.Exp.Int(spType, spAdd + numOfRegisters * 8, e.pos), e.pos))

            var offset: Z = 0
            var locals = ISZ[Intrinsic.Decl.Local](
              Intrinsic.Decl.Local(offset, typeByteSize(cpType), returnLocalId, cpType)
            )
            offset = offset + typeByteSize(cpType)
            val isMain = called.owner == owner && called.id == id
            if (p.tipe.ret != AST.Typed.unit) {
              val size: Z = if (isMain) typeByteSize(spType) + typeByteSize(p.tipe.ret) else typeByteSize(spType)
              locals = locals :+ Intrinsic.Decl.Local(offset, size, resultLocalId, spType)
              offset = offset + size
            }
            var paramOffsetMap = HashMap.empty[String, Z]
            for (param <- ops.ISZOps(called.paramNames).zip(called.tipe.args)) {
              paramOffsetMap = paramOffsetMap + param._1 ~> offset
              val size: Z =
                if (isScalar(param._2)) typeByteSize(param._2)
                else if (isMain) typeByteSize(spType) + typeByteSize(param._2) else typeByteSize(spType)
              locals = locals :+ Intrinsic.Decl.Local(offset, size, param._1, param._2)
              offset = offset + size
            }
            grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(F, F, locals, e.pos))
            grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
              AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
              T, typeByteSize(cpType), AST.IR.Exp.Int(cpType, label, e.pos), st"$returnLocalId@0 = $label", cpType, e.pos
            ))
            if (called.tipe.ret != AST.Typed.unit) {
              val n = callResultOffsetMap.get(callResultId(e.id, e.pos)).get - (spAdd + numOfRegisters * 8)
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeByteSize(cpType), e.pos), e.pos),
                isSigned(spType), typeByteSize(spType),
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, -n, e.pos), e.pos),
                st"$resultLocalId@${typeByteSize(cpType)} = $n", spType, e.pos))
            }
            for (param <- ops.ISZOps(ops.ISZOps(called.paramNames).zip(mc.t.args)).zip(e.args)) {
              val ((pid, pt), parg) = param
              val t: AST.Typed = if (isScalar(pt)) pt else spType
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, paramOffsetMap.get(pid).get, e.pos), e.pos),
                isSigned(t), typeByteSize(t), parg, st"$pid = ${parg.prettyST}", t, parg.pos))
            }
            var rgrounds = ISZ[AST.IR.Stmt.Ground]()
            for (i <- 0 until numOfRegisters if lhsOpt.isEmpty || lhsOpt.get > i) {
              val tempOffset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, -(-(numOfRegisters * 8) + i * 8), e.pos), e.pos)
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                tempOffset, F, 8, AST.IR.Exp.Temp(i, AST.Typed.u64, e.pos), st"save $$$i", AST.Typed.u64, e.pos))
              rgrounds = rgrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(i, tempOffset, F, 8, st"restore $$$i",
                AST.Typed.u64, e.pos))
            }

            var bgrounds = ISZ[AST.IR.Stmt.Ground]()
            bgrounds = bgrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(T, F,
              for (i <- locals.size - 1 to 0 by -1) yield locals(i), e.pos))
            bgrounds = bgrounds :+ AST.IR.Stmt.Intrinsic(
              Intrinsic.RegisterAssign(T, T, AST.IR.Exp.Int(spType, -(spAdd + numOfRegisters * 8), e.pos), e.pos))

            lhsOpt match {
              case Some(lhs) =>
                val t: AST.Typed = if(isScalar(called.tipe.ret)) called.tipe.ret else spType
                val rhsOffset = AST.IR.Exp.Intrinsic(Intrinsic.Load(
                  AST.IR.Exp.Binary(spType,
                    AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                    AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeByteSize(cpType), g.pos), g.pos),
                  isSigned(t), typeByteSize(t), st"", t, g.pos))
                bgrounds = (rgrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(lhs, rhsOffset, F,
                  typeByteSize(spType), st"$$$lhs = $returnLocalId", spType, g.pos))) ++ bgrounds
              case _ =>
                bgrounds = rgrounds ++ bgrounds
            }
            addBeginningMap = addBeginningMap + label ~> bgrounds
            blocks = blocks :+ b(grounds = grounds,
              jump = AST.IR.Jump.Goto(called.body.asInstanceOf[AST.IR.Body.Basic].blocks(0).label, e.pos))
          }
          def processInvokeH(g: AST.IR.Stmt.Ground, lhsOpt: Option[Z], e: AST.IR.Exp.Apply, lbl: Z): Unit = {
            th.nameMap.get(e.owner :+ e.id) match {
              case Some(_: Info.ExtMethod) =>
                blocks = blocks :+ b
                return
              case _ =>
            }
            val label = fresh.label()
            processInvoke(g, lhsOpt, e, label)
            blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(), AST.IR.Jump.Goto(lbl, e.pos))
          }

          b.jump match {
            case j: AST.IR.Jump.Goto if b.grounds.size == 1 =>
              b.grounds(0) match {
                case g: AST.IR.Stmt.Expr =>
                  processInvokeH(g, None(), g.exp, j.label)
                case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
                  processInvokeH(g, Some(g.lhs), g.rhs.asInstanceOf[AST.IR.Exp.Apply], j.label)
                case _ => blocks = blocks :+ b
              }
            case j: AST.IR.Jump.Return =>
              var addGrounds = ISZ[AST.IR.Stmt.Ground]()
              j.expOpt match {
                case Some(exp) =>
                  val lhsOffset = AST.IR.Exp.Intrinsic(Intrinsic.Load(
                    AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(
                      Intrinsic.Register(T, spType, exp.pos)), AST.IR.Exp.Binary.Op.Add,
                      AST.IR.Exp.Int(spType, typeByteSize(cpType), exp.pos), exp.pos),
                    isSigned(spType), typeByteSize(spType), st"", spType, exp.pos))
                  if (isScalar(exp.tipe)) {
                    addGrounds = addGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(lhsOffset,
                      isSigned(exp.tipe), typeByteSize(exp.tipe), exp, st"$resultLocalId = ${exp.prettyST}", exp.tipe, exp.pos))
                  } else {
                    addGrounds = addGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(lhsOffset,
                      typeByteSize(p.context.t.ret), typeByteSize(exp.tipe), exp, st"$resultLocalId = ${exp.prettyST}",
                      p.context.t.ret, exp.tipe, exp.pos))
                  }
                case _ =>
              }
              blocks = blocks :+ b(grounds = b.grounds ++ addGrounds,
                jump = AST.IR.Jump.Intrinsic(Intrinsic.GotoLocal(0, p.context, returnLocalId, j.pos)))
            case _ => blocks = blocks :+ b
          }
        }
        for (b <- blocks) {
          addBeginningMap.get(b.label) match {
            case Some(grounds) => mergedBlocks = mergedBlocks :+ b(grounds = grounds ++ b.grounds)
            case _ => mergedBlocks = mergedBlocks :+ b
          }
        }
      }
      work = next
    }
    return mergedBlocks :+
      AST.IR.BasicBlock(exitLabel, ISZ(), AST.IR.Jump.Return(None(), main.pos)) :+
      AST.IR.BasicBlock(errorLabel, ISZ(), AST.IR.Jump.Return(None(), main.pos))
  }

  def transformReduceExp(proc: AST.IR.Procedure): AST.IR.Procedure = {
    val body = proc.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      val tc = TempCollector(HashSSet.empty)
      tc.transform_langastIRBasicBlock(b)
      var m = HashMap.empty[Z, AST.IR.Exp]
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case g@AST.IR.Stmt.Intrinsic(in: Intrinsic.TempLoad) =>
            val rhs = TempExpSubstitutor(m, F).transform_langastIRExp(in.rhsOffset).getOrElse(in.rhsOffset)
            if (tc.r.contains(in.temp) && (config.maxExpDepth <= 0 || in.rhsOffset.depth < config.maxExpDepth)) {
              m = m + in.temp ~> AST.IR.Exp.Intrinsic(Intrinsic.Load(rhs, in.isSigned, in.bytes, in.comment, in.tipe, in.pos))
            } else {
              m = m -- ISZ(in.temp)
              grounds = grounds :+ g(intrinsic = in(rhsOffset = rhs))
            }
          case g: AST.IR.Stmt.Assign.Temp =>
            val rhs = TempExpSubstitutor(m, F).transform_langastIRExp(g.rhs).getOrElse(g.rhs)
            if (tc.r.contains(g.lhs) && (config.maxExpDepth <= 0 || g.rhs.depth < config.maxExpDepth)) {
              m = m + g.lhs ~> rhs
            } else {
              m = m -- ISZ(g.lhs)
              grounds = grounds :+ g(rhs = rhs)
            }
          case _ =>
            grounds = grounds :+ TempExpSubstitutor(m, F).transform_langastIRStmtGround(g).getOrElse(g)
        }
      }
      val jump = TempExpSubstitutor(m, F).transform_langastIRJump(b.jump).getOrElse(b.jump)
      blocks = blocks :+ b(grounds = grounds, jump = jump)
    }
    return proc(body = body(blocks = blocks))
  }

  def transformReduceTemp(proc: AST.IR.Procedure): AST.IR.Procedure = {
    var body = proc.body.asInstanceOf[AST.IR.Body.Basic]
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    var tempSubstMap = HashMap.empty[Z, ISZ[HashMap[Z, AST.IR.Exp]]] + body.blocks(0).label ~> ISZ(HashMap.empty)
    var work = ISZ[AST.IR.BasicBlock](body.blocks(0))
    val incomingMap = countNumOfIncomingJumps(body.blocks)
    def getSubstMap(label: Z): HashMap[Z, AST.IR.Exp] = {
      val ms = tempSubstMap.get(label).get
      var r = ms(0)
      for (i <- 1 until ms.size) {
        val m = ms(i)
        for (entry <- m.entries) {
          val (k, v2) = entry
          r.get(k) match {
            case Some(v) =>
              if (v != v2) {
                r = r + k ~> AST.IR.Exp.Temp(k, v.tipe, v.pos)
              }
            case _ =>
              r = r + k ~> v2
          }
        }
      }
      return r
    }
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.BasicBlock]()
      for (b <- work) {
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        var substMap = getSubstMap(b.label)
        for (g <- b.grounds) {
          def rest(): Unit = {
            grounds = grounds :+ TempExpSubstitutor(substMap, T).transform_langastIRStmtGround(g).getOrElse(g)
          }
          g match {
            case g: AST.IR.Stmt.Assign.Temp =>
              def restAssignTemp(): Unit = {
                substMap = substMap + g.lhs ~> AST.IR.Exp.Temp(g.lhs, g.rhs.tipe, g.pos)
                rest()
              }
              g.rhs match {
                case rhs: AST.IR.Exp.Bool =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.Int =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.F32 =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.F64 =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.R =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.String =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.EnumElementRef =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.Temp =>
                  substMap = substMap + g.lhs ~> substMap.get(rhs.n).get
                  grounds = grounds :+ g
                case rhs: AST.IR.Exp.Unary =>
                  val newRhs = rhs(exp = TempExpSubstitutor(substMap, T).transform_langastIRExp(rhs.exp).getOrElse(rhs.exp))
                  if (newRhs.depth <= config.maxExpDepth) {
                    substMap = substMap + g.lhs ~> newRhs
                    rest()
                  } else {
                    restAssignTemp()
                  }
                case rhs: AST.IR.Exp.Type =>
                  val newRhs = rhs(exp = TempExpSubstitutor(substMap, T).transform_langastIRExp(rhs.exp).getOrElse(rhs.exp))
                  if (newRhs.depth <= config.maxExpDepth) {
                    substMap = substMap + g.lhs ~> newRhs
                    rest()
                  } else {
                    restAssignTemp()
                  }
                case rhs: AST.IR.Exp.Binary =>
                  val tes = TempExpSubstitutor(substMap, T)
                  val newRhs = rhs(left = tes.transform_langastIRExp(rhs.left).getOrElse(rhs.left),
                    right = tes.transform_langastIRExp(rhs.right).getOrElse(rhs.right))
                  if (newRhs.depth <= config.maxExpDepth) {
                    substMap = substMap + g.lhs ~> newRhs
                    rest()
                  } else {
                    restAssignTemp()
                  }
                case _: AST.IR.Exp.Intrinsic => halt("Infeasible")
                case _: AST.IR.Exp.If => halt("Infeasible")
                case _ => restAssignTemp()
              }
            case _ => rest()
          }
        }
        val jump = TempExpSubstitutor(substMap, T).transform_langastIRJump(b.jump).getOrElse(b.jump)
        blockMap = blockMap + b.label ~> b(grounds = grounds, jump = jump)
        for (target <- jump.targets) {
          tempSubstMap.get(target) match {
            case Some(ms) => tempSubstMap = tempSubstMap + target ~> (ms :+ substMap)
            case _ =>
              tempSubstMap = tempSubstMap + target ~> ISZ(substMap)
          }
          if (tempSubstMap.get(target).get.size == incomingMap.get(target).get) {
            next = next :+ blockMap.get(target).get
          }
        }
      }
      work = next
    }
    body = body(blocks = blockMap.values)
    var changed = T
    while (changed) {
      changed = F
      val lv = TempLV(ControlFlowGraph.buildBasic(body))
      val entrySet = MBox(HashSMap.empty[Z, ISZ[HashSSet[Z]]])
      val exitSet = MBox(entrySet.value)
      lv.compute(body, entrySet, exitSet)
      var blocks = ISZ[AST.IR.BasicBlock]()
      for (b <- body.blocks) {
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        for (i <- b.grounds.indices) {
          val g = b.grounds(i)
          g match {
            case g: AST.IR.Stmt.Assign.Temp if !exitSet.value.get(b.label).get(i).contains(g.lhs) => changed = T
            case _ => grounds = grounds :+ g
          }
        }
        blocks = blocks :+ b(grounds = grounds)
      }
      body = body(blocks = blocks)
    }
    return proc(body = body)
  }

  def transformTempCompress(proc: AST.IR.Procedure): AST.IR.Procedure = {
    val tc = TempCollector(HashSSet.empty)
    tc.transform_langastIRProcedure(proc)
    val temps = tc.r.elements
    var tempMap = HashMap.empty[Z, Z]
    for (i <- temps.indices) {
      tempMap = tempMap + temps(i) ~> i
    }
    return TempRenumberer(tempMap).transform_langastIRProcedure(proc).getOrElse(proc)
  }

  def transformOffset(globalMap: HashSMap[ISZ[String], GlobalInfo],
                      proc: AST.IR.Procedure): (Z, AST.IR.Procedure, HashMap[String, Z]) = {
    val body = proc.body.asInstanceOf[AST.IR.Body.Basic]
    val blocks = body.blocks
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- blocks) yield (b.label, b))
    var blockLocalOffsetMap = HashMap.empty[Z, (Z, HashMap[String, Z])]
    var callResultIdOffsetMap = HashMap.empty[String, Z]
    val isMain = proc.context.owner == owner && proc.context.id == id
    var maxOffset: Z = typeByteSize(cpType)
    if (proc.tipe.ret != AST.Typed.unit) {
      maxOffset = maxOffset + typeByteSize(spType)
      if (isMain) {
        maxOffset = maxOffset + typeByteSize(proc.tipe.ret)
      }
    }
    {
      var m = HashMap.empty[String, Z]
      var offset: Z = maxOffset
      for (param <- ops.ISZOps(proc.paramNames).zip(proc.tipe.args)) {
        val (id, t) = param
        m = m + id ~> offset
        val size: Z =
          if (isScalar(t)) typeByteSize(t)
          else if (isMain) typeByteSize(spType) + typeByteSize(t) else typeByteSize(spType)
        offset = offset + size
      }
      blockLocalOffsetMap = blockLocalOffsetMap + blocks(0).label ~> (offset, m)
      maxOffset = offset
    }
    var work = ISZ(blocks(0))
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.BasicBlock]()
      for (b <- work) {
        var (offset, m) = blockLocalOffsetMap.get(b.label).get
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        for (g <- b.grounds) {
          g match {
            case g: AST.IR.Stmt.Decl =>
              var locals = ISZ[Intrinsic.Decl.Local]()
              val mult: Z = if (g.undecl) -1 else 1
              var assignSPs = ISZ[AST.IR.Stmt.Ground]()
              for (l <- g.locals) {
                val (size, assignSP): (Z, B) =
                  if (g.isAlloc || isScalar(l.tipe)) (typeByteSize(l.tipe), F)
                  else (typeByteSize(spType) + typeByteSize(l.tipe), !g.undecl)
                if (g.undecl) {
                  locals = locals :+ Intrinsic.Decl.Local(m.get(l.id).get, size, l.id, l.tipe)
                  m = m -- ISZ(l.id)
                } else {
                  m = m + l.id ~> offset
                  locals = locals :+ Intrinsic.Decl.Local(offset, size, l.id, l.tipe)
                }
                if (assignSP) {
                  assignSPs = assignSPs :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                    AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                      AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, offset, g.pos), g.pos),
                    isSigned(spType), typeByteSize(spType),
                    AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                      AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, offset + typeByteSize(spType), g.pos), g.pos),
                    st"address of ${l.id}", spType, g.pos))
                }
                offset = offset + size * mult
              }
              if (maxOffset < offset) {
                maxOffset = offset
              }
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(g.undecl, g.isAlloc, locals, g.pos))
              grounds = grounds ++ assignSPs
            case _ =>
              g match {
                case AST.IR.Stmt.Assign.Global(name, tipe, rhs, pos) =>
                  val newRhs = OffsetSubsitutor(this, m, globalMap).transform_langastIRExp(rhs).getOrElse(rhs)
                  val globalOffset = AST.IR.Exp.Int(spType, globalMap.get(name).get.offset, pos)
                  if (isScalar(tipe)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(globalOffset, isSigned(tipe),
                      typeByteSize(tipe), newRhs, g.prettyST, tipe, g.pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(globalOffset, typeByteSize(tipe),
                      typeByteSize(newRhs.tipe), newRhs, g.prettyST, tipe, newRhs.tipe, g.pos))
                  }
                case AST.IR.Stmt.Assign.Local(_, lhs, t, rhs, pos) =>
                  val newRhs = OffsetSubsitutor(this, m, globalMap).transform_langastIRExp(rhs).getOrElse(rhs)
                  val localOffset = m.get(lhs).get
                  if (isScalar(t)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                      AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, newRhs.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, newRhs.pos), newRhs.pos),
                      T, typeByteSize(t), newRhs, st"$lhs = ${newRhs.prettyST}", t, pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(
                      AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, newRhs.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, newRhs.pos), newRhs.pos),
                      typeByteSize(t), typeByteSize(newRhs.tipe), newRhs, st"$lhs = ${newRhs.prettyST}", t, newRhs.tipe, pos))
                  }
                case AST.IR.Stmt.Assign.Field(receiver, id, _, rhs, pos) =>
                  val (ft, offset) = classSizeFieldOffsets(receiver.tipe.asInstanceOf[AST.Typed.Name])._2.get(id).get
                  val lhsOffset = AST.IR.Exp.Binary(spType, receiver, AST.IR.Exp.Binary.Op.Add,
                    AST.IR.Exp.Int(spType, offset, rhs.pos), rhs.pos)
                  if (isScalar(ft)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(lhsOffset, isSigned(ft),
                      typeByteSize(ft), rhs, g.prettyST, ft, pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(lhsOffset, typeByteSize(ft),
                      typeByteSize(rhs.tipe), rhs, g.prettyST, ft, rhs.tipe, pos))
                  }
                case AST.IR.Stmt.Assign.Index(rcv, idx, rhs, pos) =>
                  val newRhs = OffsetSubsitutor(this, m, globalMap).transform_langastIRExp(rhs).getOrElse(rhs)
                  val seqType = rcv.tipe.asInstanceOf[AST.Typed.Name]
                  val indexType = seqType.args(0)
                  val elementType = seqType.args(1)
                  val min: Z = indexType match {
                    case AST.Typed.z => 0
                    case _ =>
                      val subz = subZOpt(indexType).get.ast
                      if (subz.isIndex) subz.min
                      else if (subz.isZeroIndex) 0
                      else subz.min
                  }
                  val os = OffsetSubsitutor(this, m, globalMap)
                  var index = os.transform_langastIRExp(idx).getOrElse(idx)
                  if (index.tipe != spType) {
                    index = AST.IR.Exp.Type(F, index, spType, index.pos)
                  }
                  val indexOffset: AST.IR.Exp = if (min == 0) index else AST.IR.Exp.Binary(
                    spType, index, AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, min, index.pos), index.pos)
                  val elementSize = typeByteSize(elementType)
                  val elementOffset: AST.IR.Exp = if (elementSize == 1) indexOffset else AST.IR.Exp.Binary(spType,
                    indexOffset, AST.IR.Exp.Binary.Op.Mul, AST.IR.Exp.Int(spType, typeByteSize(elementType),
                      index.pos), index.pos)
                  val receiver = AST.IR.Exp.Binary(spType, os.transform_langastIRExp(rcv).getOrElse(rcv),
                    AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeShaSize + typeByteSize(AST.Typed.z), rcv.pos), rcv.pos)
                  val receiverOffset = AST.IR.Exp.Binary(spType, receiver, AST.IR.Exp.Binary.Op.Add, elementOffset, pos)
                  if (isScalar(elementType)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(receiverOffset,
                      isSigned(elementType), typeByteSize(elementType), newRhs, g.prettyST, elementType, g.pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(receiverOffset, typeByteSize(elementType),
                      typeByteSize(newRhs.tipe), newRhs, g.prettyST, elementType, newRhs.tipe, g.pos))
                  }
                case AST.IR.Stmt.Assign.Temp(n, rhs, pos) =>
                  rhs match {
                    case rhs: AST.IR.Exp.LocalVarRef =>
                      val localOffset = m.get(rhs.id).get
                      val temp = n
                      val t: AST.Typed = if (isScalar(rhs.tipe)) rhs.tipe else spType
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp,
                        AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, rhs.pos)),
                          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, rhs.pos), rhs.pos),
                        isSigned(t), typeByteSize(t), g.prettyST, rhs.tipe, pos))
                    case rhs: AST.IR.Exp.GlobalVarRef =>
                      val temp = n
                      val globalOffset = AST.IR.Exp.Int(spType, globalMap.get(rhs.name).get.offset, rhs.pos)
                      val t: AST.Typed = if (isScalar(rhs.tipe)) rhs.tipe else spType
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp, globalOffset, isSigned(t),
                        typeByteSize(t), g.prettyST, t, pos))
                    case rhs: AST.IR.Exp.FieldVarRef =>
                      val receiver = OffsetSubsitutor(this, m, globalMap).transform_langastIRExp(rhs.receiver).
                        getOrElse(rhs.receiver)
                      if (isSeq(rhs.receiver.tipe)) {
                        assert(rhs.id == "size")
                        val temp = n
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(
                          temp, AST.IR.Exp.Binary(spType, receiver,
                            AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeShaSize, rhs.pos), rhs.pos),
                          T, typeByteSize(rhs.tipe), g.prettyST, rhs.tipe, pos))
                      } else {
                        val temp = n
                        val (ft, offset) = classSizeFieldOffsets(rhs.receiver.tipe.asInstanceOf[AST.Typed.Name]).
                          _2.get(rhs.id).get
                        val rhsOffset: AST.IR.Exp = if (offset != 0) AST.IR.Exp.Binary(spType, receiver,
                          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, offset, rhs.pos), rhs.pos) else receiver
                        if (isScalar(ft)) {
                          grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp, rhsOffset,
                            isSigned(ft), typeByteSize(ft), g.prettyST, ft, pos))
                        } else {
                          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, rhsOffset, pos)
                        }
                      }
                    case rhs: AST.IR.Exp.Indexing =>
                      val seqType = rhs.exp.tipe.asInstanceOf[AST.Typed.Name]
                      val indexType = seqType.args(0)
                      val elementType = seqType.args(1)
                      val min: Z = indexType match {
                        case AST.Typed.z => 0
                        case _ =>
                          val subz = subZOpt(indexType).get.ast
                          if (subz.isIndex) subz.min
                          else if (subz.isZeroIndex) 0
                          else subz.min
                      }
                      val os = OffsetSubsitutor(this, m, globalMap)
                      var index = os.transform_langastIRExp(rhs.index).getOrElse(rhs.index)
                      if (index.tipe != spType) {
                        index = AST.IR.Exp.Type(F, index, spType, index.pos)
                      }
                      val temp = n
                      val indexOffset: AST.IR.Exp = if (min == 0) index else AST.IR.Exp.Binary(
                        spType, index, AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, min, index.pos), index.pos)
                      val elementSize = typeByteSize(elementType)
                      val elementOffset: AST.IR.Exp = if (elementSize == 1) indexOffset else AST.IR.Exp.Binary(spType,
                        indexOffset, AST.IR.Exp.Binary.Op.Mul, AST.IR.Exp.Int(spType, typeByteSize(elementType),
                          index.pos), index.pos)
                      val exp = AST.IR.Exp.Binary(spType, os.transform_langastIRExp(rhs.exp).getOrElse(rhs.exp),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeShaSize + typeByteSize(AST.Typed.z), rhs.exp.pos),
                        rhs.exp.pos)
                      val rhsOffset = AST.IR.Exp.Binary(spType, exp, AST.IR.Exp.Binary.Op.Add, elementOffset, rhs.exp.pos)
                      if (isScalar(elementType)) {
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp, rhsOffset,
                          isSigned(elementType), typeByteSize(elementType), g.prettyST, elementType, pos))
                      } else {
                        grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, rhsOffset, pos)
                      }
                    case rhs: AST.IR.Exp.Construct =>
                      val loffset =  m.get(constructResultId(rhs.pos)).get
                      val lhsOffset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, loffset, g.pos),
                        g.pos)
                      val sha = sha3(rhs.tipe.string)
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(lhsOffset, F, typeShaSize,
                        AST.IR.Exp.Int(AST.Typed.u32, sha.toZ, g.pos),
                        st"sha3 type signature of ${rhs.tipe}: 0x$sha", AST.Typed.u32, g.pos))
                      if (rhs.tipe.ids == AST.Typed.isName || rhs.tipe.ids == AST.Typed.msName) {
                        val sizeOffset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, loffset + 4, g.pos),
                          g.pos)
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(sizeOffset,
                          isSigned(AST.Typed.z), typeByteSize(AST.Typed.z), AST.IR.Exp.Int(AST.Typed.z, rhs.args.size, g.pos),
                          st"size of ${rhs.prettyST}", AST.Typed.z, g.pos))
                      }
                    case _: AST.IR.Exp.If => halt(s"Infeasible: $rhs")
                    case _: AST.IR.Exp.Intrinsic => halt(s"Infeasible: $rhs")
                    case _ =>
                      grounds = grounds :+ OffsetSubsitutor(this, m, globalMap).transform_langastIRStmtGround(g).getOrElse(g)
                  }
                case _ =>
                  grounds = grounds :+ OffsetSubsitutor(this, m, globalMap).transform_langastIRStmtGround(g).getOrElse(g)
              }
              g match {
                case g: AST.IR.Stmt.Expr if g.exp.methodType.ret != AST.Typed.unit =>
                  val id = callResultId(g.exp.id, g.exp.pos)
                  callResultIdOffsetMap = callResultIdOffsetMap + id ~> m.get(id).get
                case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
                  val e = g.rhs.asInstanceOf[AST.IR.Exp.Apply]
                  val id = callResultId(e.id, e.pos)
                  callResultIdOffsetMap = callResultIdOffsetMap + id ~> m.get(id).get
                case _ =>
              }
          }
        }
        blockMap = blockMap + b.label ~> b(grounds = grounds,
          jump = OffsetSubsitutor(this, m, globalMap).transform_langastIRJump(b.jump).getOrElse(b.jump))
        for (target <- b.jump.targets) {
          blockLocalOffsetMap.get(target) match {
            case Some((po, pm)) =>
              assert(offset == po && m == pm, s"$target: offset = $offset, po = $po, m = $m, pm = $pm")
            case _ =>
              blockLocalOffsetMap = blockLocalOffsetMap + target ~> (offset, m)
              next = next :+ blockMap.get(target).get
          }
        }
      }
      work = next
    }
    return (maxOffset, proc(body = body(blocks = blockMap.values)), callResultIdOffsetMap)
  }

  def transformSplitTemp(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      var writes = HashSSet.empty[Z]
      var reads = HashSSet.empty[Z]
      var block = b
      def computeWrites(g: AST.IR.Stmt.Ground): Unit = {
        g match {
          case g: AST.IR.Stmt.Assign.Temp =>
            writes = writes + g.lhs
          case _ =>
        }
      }
      def computeReads(g: AST.IR.Stmt.Ground): Unit = {
        val tc = TempCollector(reads)
        tc.transform_langastIRStmtGround(g)
        reads = tc.r
      }
      def introBlock(pos: message.Position): Unit = {
        if (grounds.isEmpty) {
          return
        }
        val n = fresh.label()
        blocks = blocks :+ AST.IR.BasicBlock(block.label, grounds, AST.IR.Jump.Goto(n, pos))
        grounds = ISZ()
        reads = HashSSet.empty[Z]
        writes = HashSSet.empty[Z]
        block = AST.IR.BasicBlock(n, grounds, block.jump)
      }
      for (g <- b.grounds) {
        computeWrites(g)
        if (writes.nonEmpty) {
          computeReads(g)
          if (reads.intersect(writes).nonEmpty) {
            introBlock(g.pos)
            grounds = grounds :+ g
            computeWrites(g)
          } else {
            grounds = grounds :+ g
          }
        } else {
          grounds = grounds :+ g
        }
      }
      val tc = TempCollector(reads)
      tc.transform_langastIRJump(b.jump)
      reads = tc.r
      if (reads.intersect(writes).nonEmpty) {
        introBlock(b.jump.pos)
      }
      blocks = blocks :+ block(grounds = grounds, jump = b.jump)
    }
    return p(body = body(blocks = blocks))
  }

  def transformRegisterInc(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var i: Z = 0
      var split = b.grounds.size
      val rd = RegisterDetector(F, F)
      while (i < b.grounds.size) {
        b.grounds(i) match {
          case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.RegisterAssign) if intrinsic.isInc =>
            var j = i + 1
            while (j < b.grounds.size) {
              rd.transform_langastIRStmtGround(b.grounds(j))
              if ((intrinsic.isSP && rd.hasSP || !intrinsic.isSP && rd.hasDP) && split == b.grounds.size) {
                split = j
              }
              j = j + 1
            }
          case _ =>
        }
        i = i + 1
      }
      if (split == b.grounds.size) {
        blocks = blocks :+ b
      } else {
        val label = fresh.label()
        val b1 = AST.IR.BasicBlock(b.label, ops.ISZOps(b.grounds).slice(0, split), AST.IR.Jump.Goto(label, b.grounds(split - 1).pos))
        val b2 = AST.IR.BasicBlock(label, ops.ISZOps(b.grounds).slice(split, b.grounds.size), b.jump)
        blocks = blocks :+ b1 :+ b2
      }
    }
    return p(body = body(blocks = blocks))
  }

  def transformMergeRegisterInc(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blockMap = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    val m = countNumOfIncomingJumps(body.blocks)
    for (b <- body.blocks if blockMap.contains(b.label)) {
      b.jump match {
        case j: AST.IR.Jump.Goto if m.get(j.label).get == 1 =>
          val b2 = blockMap.get(j.label).get
          b2.grounds match {
            case ISZ(AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.RegisterAssign), _*) if intrinsic.isInc =>
              blockMap = blockMap -- ISZ(b2.label)
              blockMap = blockMap + b.label ~> b(grounds = b.grounds ++ b2.grounds, jump = b2.jump)
            case _ =>
          }
        case _ =>
      }
    }
    return p(body = body(blocks = blockMap.values))
  }

  @pure def printStringLit(incDP: B, s: String, pos: message.Position): ISZ[AST.IR.Stmt.Ground] = {
    var r = ISZ[AST.IR.Stmt.Ground]()
    if (config.shouldPrint) {
      val cis = conversions.String.toCis(s)
      var i = 0
      val register = AST.IR.Exp.Intrinsic(Intrinsic.Register(F, dpType, pos))
      for (c <- cis) {
        for (byte <- conversions.String.toU8is(s"$c")) {
          var lhsOffset: AST.IR.Exp = register
          if (i != 0) {
            lhsOffset = AST.IR.Exp.Binary(dpType, lhsOffset, AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(dpType, i, pos), pos)
          }
          lhsOffset = AST.IR.Exp.Binary(dpType, lhsOffset, AST.IR.Exp.Binary.Op.And, AST.IR.Exp.Int(dpType, dpMask, pos), pos)
          r = r :+ AST.IR.Stmt.Assign.Index(AST.IR.Exp.GlobalVarRef(displayName, displayType, pos), lhsOffset, AST.IR.Exp.Int(AST.Typed.u8, byte.toZ, pos), pos)
          i = i + 1
        }
      }
      if (incDP) {
        r = r :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, T, AST.IR.Exp.Int(dpType, r.size, pos), pos))
      }
    }
    return r
  }

  def transformPrint(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      val maxTemp: Z = {
        val tc = TempCollector(HashSSet.empty)
        tc.transform_langastIRBasicBlock(b)
        var max: Z = 0
        for (t <- tc.r.elements) {
          if (max <= t) {
            max = max + 1
          }
        }
        max
      }
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case AST.IR.Stmt.Expr(e) if e.isInObject && e.owner == AST.Typed.sireumName &&
            (e.id == "print" || e.id == "eprint" || e.id == "cprint") =>
            e.args(if (e.id == "cprint") 1 else 0) match {
              case arg: AST.IR.Exp.Bool =>
                grounds = grounds ++ printStringLit(T, if (arg.value) "T" else "F", arg.pos)
              case arg: AST.IR.Exp.Int =>
                if (isBitVector(arg.tipe)) {
                  val n = typeByteSize(arg.tipe) * 2
                  val buffer = MS.create[anvil.PrinterIndex.U, U8](n, u8"0")
                  val value: U64 =
                    if (arg.value < 0) conversions.S64.toRawU64(conversions.Z.toS64(arg.value))
                    else conversions.Z.toU64(arg.value)
                  anvil.Printer.printU64Hex(buffer, u"0", anvil.Printer.Ext.z2u(dpMask), value, n)
                  val u8ms = MSZ.create(n, u8"0")
                  for (i <- 0 until n) {
                    u8ms(i) = buffer(anvil.Printer.Ext.z2u(i))
                  }
                  grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
                } else {
                  val buffer = MS.create[anvil.PrinterIndex.U, U8](20, u8"0")
                  val n: Z =
                    if (isSigned(arg.tipe)) anvil.Printer.printS64(buffer, u"0", anvil.Printer.Ext.z2u(dpMask), conversions.Z.toS64(arg.value)).toZ
                    else anvil.Printer.printU64(buffer, u"0", anvil.Printer.Ext.z2u(dpMask), conversions.Z.toU64(arg.value)).toZ
                  val u8ms = MSZ.create(n, u8"0")
                  for (i <- 0 until n) {
                    u8ms(i) = buffer(anvil.Printer.Ext.z2u(i))
                  }
                  grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
                }
              case arg: AST.IR.Exp.F32 =>
                val buffer = MS.create[anvil.PrinterIndex.U, U8](50, u8"0")
                val n = anvil.Printer.printF32_2(buffer, u"0", anvil.Printer.Ext.z2u(dpMask), arg.value).toZ
                val u8ms = MSZ.create(n, u8"0")
                for (i <- 0 until n) {
                  u8ms(i) = buffer(anvil.Printer.Ext.z2u(i))
                }
                grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
              case arg: AST.IR.Exp.F64 =>
                val buffer = MS.create[anvil.PrinterIndex.U, U8](320, u8"0")
                val n = anvil.Printer.printF64_2(buffer, u"0", anvil.Printer.Ext.z2u(dpMask), arg.value).toZ
                val u8ms = MSZ.create(n, u8"0")
                for (i <- 0 until n) {
                  u8ms(i) = buffer(anvil.Printer.Ext.z2u(i))
                }
                grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
              case arg: AST.IR.Exp.R => halt(s"TODO: $arg")
              case arg: AST.IR.Exp.String => grounds = grounds ++ printStringLit(T, arg.value, arg.pos)
              case arg =>
                fresh.setTemp(maxTemp)
                val pos = g.pos
                val buffer = AST.IR.Exp.GlobalVarRef(displayName, displayType, pos)
                val index = AST.IR.Exp.Intrinsic(Intrinsic.Register(F, dpType, pos))
                val mask = AST.IR.Exp.Int(displayIndexType, dpMask, pos)
                val printApply: AST.IR.Exp.Apply = arg.tipe match {
                  case AST.Typed.b =>
                    val id = "printB"
                    val mt = printTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.c =>
                    val id = "printC"
                    val mt = printTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.z =>
                    val id = "printS64"
                    val mt = printTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, AST.IR.Exp.Type(F, arg, AST.Typed.s64, pos)), mt, mt.ret, pos)
                  case AST.Typed.f32 =>
                    val id = "printF32_2"
                    val mt = printTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.f64 =>
                    val id = "printF64_2"
                    val mt = printTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.string =>
                    val id = "printString"
                    val mt = printTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case t if subZOpt(t).nonEmpty =>
                    if (isBitVector(t)) {
                      val digits = AST.IR.Exp.Int(AST.Typed.z, typeByteSize(t), pos)
                      val id = "printU64Hex"
                      val mt = printTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.u64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.u64, pos)
                      }
                      AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, a, digits), mt, mt.ret, pos)
                    } else if (isSigned(t)) {
                      val id = "printS64"
                      val mt = printTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.s64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.s64, pos)
                      }
                      AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, a), mt, mt.ret, pos)
                    } else {
                      val id = "printU64"
                      val mt = printTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.u64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.u64, pos)
                      }
                      AST.IR.Exp.Apply(T, printerName, id, ISZ(buffer, index, mask, a), mt, mt.ret, pos)
                    }
                    halt(s"TODO: $arg")
                  case AST.Typed.r => halt(s"TODO: $arg")
                  case t => halt(s"TODO: $t, $arg")
                }
                val temp = fresh.temp()
                grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, printApply, pos)
                val inc = AST.IR.Exp.Type(F, AST.IR.Exp.Temp(temp, AST.Typed.u64, pos), dpType, pos)
                grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, T, inc, pos))
            }

          case _ => grounds = grounds :+ g
        }
      }
      blocks = blocks :+ b(grounds = grounds)
    }
    return p(body = body(blocks = blocks))
  }

  def transformInstanceOf(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var block = b
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case AST.IR.Stmt.Assign.Temp(lhs, rhs: AST.IR.Exp.Type, pos) if !isScalar(rhs.t) =>
            val sha3Types = sha3TypeImplOf(rhs.t)
            val tLabel = fresh.label()
            val fLabel = fresh.label()
            val eLabel = fresh.label()
            blocks = blocks :+ AST.IR.BasicBlock(b.label, grounds, AST.IR.Jump.Switch(
              AST.IR.Exp.FieldVarRef(rhs.exp, typeFieldId, typeShaType, pos),
              for (sha3t <- sha3Types) yield AST.IR.Jump.Switch.Case(AST.IR.Exp.Int(typeShaType, sha3t, pos), tLabel),
              Some(fLabel), pos
            ))
            val egoto = AST.IR.Jump.Goto(eLabel, pos)
            val (tStmts, tJump, fStmts, fJump): (ISZ[AST.IR.Stmt.Ground], AST.IR.Jump, ISZ[AST.IR.Stmt.Ground], AST.IR.Jump) =
              if (rhs.test)
                (ISZ(AST.IR.Stmt.Assign.Temp(lhs, AST.IR.Exp.Bool(T, pos), pos)),
                  egoto,
                  ISZ(AST.IR.Stmt.Assign.Temp(lhs, AST.IR.Exp.Bool(F, pos), pos)),
                  egoto)
              else
                (ISZ(),
                  AST.IR.Jump.Goto(eLabel, pos),
                  printStringLit(T, s"Cannot cast to ${rhs.t}\n", pos),
                  if (config.runtimeCheck) AST.IR.Jump.Halt(pos)
                  else egoto)
            blocks = blocks :+ AST.IR.BasicBlock(tLabel, tStmts, tJump)
            blocks = blocks :+ AST.IR.BasicBlock(fLabel, fStmts, fJump)
            grounds = ISZ()
            block = AST.IR.BasicBlock(eLabel, grounds, b.jump)
          case _ => grounds = grounds :+ g
        }
      }
      blocks = blocks :+ block(grounds = grounds)
    }
    return p(body = body(blocks = blocks))
  }

  def transformMain(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure, globalSize: Z, globalMap: HashSMap[QName, GlobalInfo]): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var grounds = ISZ[AST.IR.Stmt.Ground](
      AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(T, F, AST.IR.Exp.Int(spType, globalSize, p.pos), p.pos))
    )
    if (config.shouldPrint) {
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, F, AST.IR.Exp.Int(dpType, 0, p.pos), p.pos))
      val display = globalMap.get(displayName).get
      val sha3t = sha3(displayType.string)
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(typeShaType, display.offset + typeByteSize(spType), p.pos), isSigned(typeShaType), typeShaSize,
        AST.IR.Exp.Int(typeShaType, sha3t.toZ, p.pos), st"$displayId.$typeFieldId ($displayType: 0x$sha3t)", typeShaType, p.pos))
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, display.offset + typeByteSize(spType) + typeByteSize(typeShaType), p.pos),
        isSigned(AST.Typed.z), typeByteSize(AST.Typed.z),
        AST.IR.Exp.Int(AST.Typed.z, dpMask + 1, p.pos), st"$displayId.size", AST.Typed.z, p.pos))
    }
    var offset: Z = 0
    for (ge <- globalMap.entries) {
      val (name, info) = ge
      if (!info.isScalar) {
        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Int(spType, offset, p.pos), isSigned(spType), typeByteSize(spType),
          AST.IR.Exp.Int(spType, offset + typeByteSize(spType), p.pos), st"data address of ${(name, ".")} (size = ${typeByteSize(info.tipe)})", spType, p.pos))
      }
      offset = offset + info.size + info.dataSize
    }
    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
      AST.IR.Exp.Int(cpType, offset, p.pos), isSigned(cpType), typeByteSize(cpType),
      AST.IR.Exp.Int(cpType, 0, p.pos), st"$returnLocalId", cpType, p.pos))
    offset = offset + typeByteSize(cpType)
    if (p.tipe.ret != AST.Typed.unit) {
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, offset, p.pos), isSigned(spType), typeByteSize(spType),
        AST.IR.Exp.Int(spType, offset + typeByteSize(spType), p.pos), st"data address of $resultLocalId (size = ${typeByteSize(p.tipe.ret)})", spType, p.pos))
      offset = offset + typeByteSize(spType)
      offset = offset + typeByteSize(p.tipe.ret)
    }
    def updateOffset(id: String, t: AST.Typed): Unit = {
      if (isScalar(t)) {
        offset = offset + typeByteSize(t)
      } else {
        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Int(spType, offset, p.pos), isSigned(spType), typeByteSize(spType),
          AST.IR.Exp.Int(spType, offset + typeByteSize(spType), p.pos), st"data address of $id (size = ${typeByteSize(t)})", spType, p.pos))
        offset = offset + typeByteSize(spType)
        offset = offset + typeByteSize(t)
      }
    }
    for (param <- ops.ISZOps(p.paramNames).zip(p.tipe.args)) {
      updateOffset(param._1, param._2)
    }
    return p(body = body(AST.IR.BasicBlock(fresh.label(), grounds, AST.IR.Jump.Goto(startingLabel, p.pos)) +: body.blocks))
  }

  @memoize def subZOpt(t: AST.Typed): Option[TypeInfo.SubZ] = {
    t match {
      case t: AST.Typed.Name =>
        th.typeMap.get(t.ids).get match {
          case ti: TypeInfo.SubZ => return Some(ti)
          case _ =>
        }
      case _ =>
    }
    return None()
  }

  @memoize def classSizeFieldOffsets(t: AST.Typed.Name): (Z, HashSMap[String, (AST.Typed, Z)]) = {
    var r = HashSMap.empty[String, (AST.Typed, Z)] + typeFieldId ~> (typeShaType, 0)
    var offset: Z = typeShaSize
    if (t == AST.Typed.string) {
      r = r + "size" ~> (AST.Typed.z, offset)
      return (offset + typeByteSize(AST.Typed.z), r)
    }
    val info = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
    val sm = TypeChecker.buildTypeSubstMap(t.ids, None(), info.ast.typeParams, t.args, message.Reporter.create).get
    for (v <- info.vars.values) {
      val ft = v.typedOpt.get.subst(sm)
      r = r + v.ast.id.value ~> (ft, offset)
      offset = offset + typeByteSize(ft)
    }
    return (offset, r)
  }

  @memoize def getMaxArraySize(t: AST.Typed.Name): Z = {
    if (t == displayType) {
      assert(config.shouldPrint)
      return dpMask + 1
    }
    assert(t.ids == AST.Typed.isName || t.ids == AST.Typed.msName)
    config.customArraySizes.get(t) match {
      case Some(n) => return n
      case _ =>
    }
    subZOpt(t.args(0)) match {
      case Some(subz) =>
        if (subz.ast.hasMax && subz.ast.hasMin) {
          val size = subz.ast.max - subz.ast.min + 1
          if (size < config.maxArraySize) {
            return size
          }
        }
      case _ =>
    }
    return config.maxArraySize
  }

  @memoize def isBitVector(t: AST.Typed): B = {
    subZOpt(t) match {
      case Some(subz) => return subz.ast.isBitVector
      case _ => return F
    }
  }

  @memoize def typeByteSize(t: AST.Typed): Z = {
    def typeImplMaxSize(c: AST.Typed.Name): Z = {
      var r: Z = 0
      for (c <- tsr.typeImpl.childrenOf(c).elements) {
        val cSize = typeByteSize(c)
        if (r < cSize) {
          r = cSize
        }
      }
      return r
    }

    @strictpure def numOfBytes(bitWidth: Z): Z = bitWidth / 8 + (if (bitWidth % 8 == 0) 0 else 1)

    @strictpure def rangeNumOfBytes(signed: B, min: Z, max: Z): Z =
      if (signed) {
        if (min >= S8.Min.toZ && max <= S8.Max.toZ) {
          1
        } else if (min >= S16.Min.toZ && max <= S16.Max.toZ) {
          2
        } else if (min >= S32.Min.toZ && max <= S32.Max.toZ) {
          4
        } else if (min >= S64.Min.toZ && max <= S64.Max.toZ) {
          8
        } else {
          halt(s"Infeasible: $signed, $min, $max")
        }
      } else {
        if (min >= U8.Min.toZ && max <= U8.Max.toZ) {
          1
        } else if (min >= U16.Min.toZ && max <= U16.Max.toZ) {
          2
        } else if (min >= U32.Min.toZ && max <= U32.Max.toZ) {
          4
        } else if (min >= U64.Min.toZ && max <= U64.Max.toZ) {
          8
        } else {
          halt(s"Infeasible: $signed, $min, $max")
        }
      }

    @strictpure def is1Bit(tpe: AST.Typed): B = if (tpe == AST.Typed.b) {
      T
    } else {
      subZOpt(tpe) match {
        case Some(info) => info.ast.isBitVector && info.ast.bitWidth == 1
        case _ => F
      }
    }

    t match {
      case AST.Typed.b => return 1
      case AST.Typed.c => return 4
      case AST.Typed.z => return numOfBytes(config.defaultBitWidth)
      case AST.Typed.f32 => return 4
      case AST.Typed.f64 => return 8
      case AST.Typed.r => return 8
      case AST.Typed.string =>
        var r: Z = 4 // type sha
        r = r + 4 // size
        r = r + config.maxStringSize
        return r
      case AST.Typed.unit => return 0
      case AST.Typed.nothing => return 0
      case `dpType` => return dpTypeByteSize
      case `spType` => return spTypeByteSize
      case `cpType` =>
        assert(numOfLocs != 0, "Number of locations for CP has not been initialized")
        return cpTypeByteSize
      case t: AST.Typed.Name =>
        if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
          var r: Z = 4 // type sha
          r = r + typeByteSize(AST.Typed.z) // .size
          val et = t.args(1)
          if (et == AST.Typed.b) {

          } else {
            r = r + getMaxArraySize(t) * typeByteSize(t.args(1)) // elements
          }
          return r
        } else {
          th.typeMap.get(t.ids).get match {
            case info: TypeInfo.Adt =>
              if (info.ast.isRoot) {
                return typeImplMaxSize(t)
              } else {
                return classSizeFieldOffsets(t)._1
              }
            case _: TypeInfo.Sig => return typeImplMaxSize(t)
            case info: TypeInfo.Enum => return rangeNumOfBytes(F, 0, info.elements.size - 1)
            case info: TypeInfo.SubZ =>
              if (info.ast.isBitVector) {
                return numOfBytes(info.ast.bitWidth)
              } else if (info.ast.hasMax && info.ast.hasMin) {
                return rangeNumOfBytes(info.ast.isSigned, info.ast.min, info.ast.max)
              } else {
                return numOfBytes(config.defaultBitWidth)
              }
            case _ => halt(s"Infeasible: $t")
          }
        }
      case t: AST.Typed.Tuple =>
        var r: Z = 4 // type sha
        for (arg <- t.args) {
          r = r + typeByteSize(arg)
        }
        return r
      case t => halt(s"Infeasible: $t")
    }
  }

  @memoize def isSubZ(t: AST.Typed): B = {
    t match {
      case t: AST.Typed.Name if t.args.isEmpty =>
        th.typeMap.get(t.ids) match {
          case Some(_: TypeInfo.SubZ) => return T
          case _ =>
        }
      case _ =>
    }
    return F
  }

  @pure def sha3(s: String): U32 = {
    val sha = crypto.SHA3.init512
    sha.update(conversions.String.toU8is(s))
    val bs = sha.finalise()
    return conversions.U8.toU32(bs(0)) << u32"24" | conversions.U8.toU32(bs(1)) << u32"16" |
      conversions.U8.toU32(bs(2)) << u32"8" | conversions.U8.toU32(bs(3))
  }

  @memoize def isScalar(t: AST.Typed): B = {
    t match {
      case AST.Typed.b =>
      case AST.Typed.c =>
      case AST.Typed.z =>
      case AST.Typed.f32 =>
      case AST.Typed.f64 =>
      case AST.Typed.r =>
      case `spType` =>
      case `cpType` => assert(numOfLocs != 0, "Number of locations for CP has not been initialized")
      case `dpType` =>
      case _ => return isSubZ(t)
    }
    return T
  }

  @strictpure def signedString(t: AST.Typed): String = if (isSigned(t)) "signed" else "unsigned"

  @memoize def minMaxOpt(t: AST.Typed): (Option[Z], Option[Z]) = {
    if (t != AST.Typed.z) {
      subZOpt(t) match {
        case Some(info) =>
          val minOpt: Option[Z] = if (info.ast.hasMin) Some(info.ast.min) else None()
          val maxOpt: Option[Z] = if (info.ast.hasMax) Some(info.ast.max) else None()
          return (minOpt, maxOpt)
        case _ =>
      }
    }
    return (None(), None())
  }

  @memoize def isSigned(t: AST.Typed): B = {
    t match {
      case AST.Typed.b => return F
      case AST.Typed.c => return F
      case AST.Typed.z => return T
      case AST.Typed.f32 => return T
      case AST.Typed.f64 => return T
      case AST.Typed.r => return T
      case `spType` => return F
      case `cpType` =>
        assert(numOfLocs != 0, "Number of locations for CP has not been initialized")
        return F
      case `dpType` => return F
      case _ => return subZOpt(t).get.ast.isSigned
    }
  }

  @memoize def isSeq(t: AST.Typed): B = {
    t match {
      case t: AST.Typed.Name => return t.ids == AST.Typed.isName || t.ids == AST.Typed.msName
      case _ =>
    }
    return F
  }

  @memoize def classInit(t: AST.Typed.Name): ISZ[AST.Stmt] = {
    var r = ISZ[AST.Stmt]()
    th.typeMap.get(t.ids).get match {
      case info: TypeInfo.Adt if !info.ast.isRoot =>
        val sm = TypeChecker.buildTypeSubstMap(t.ids, None(), info.ast.typeParams, t.args, message.Reporter.create).get
        val tsubst = AST.Transformer(AST.Util.TypePrePostSubstitutor(sm))
        val params = HashSet ++ (for (p <- info.ast.params) yield p.id.value)
        val context = t.ids :+ newInitId
        val receiver = Option.some[AST.Exp](AST.Exp.This(context, AST.TypedAttr(info.posOpt, Some(t))))
        for (v <- info.vars.values if !params.contains(v.ast.id.value)) {
          v.ast.initOpt match {
            case Some(ae) =>
              val tOpt = Option.some(ae.typedOpt.get.subst(sm))
              r = r :+ AST.Stmt.Assign(AST.Exp.Select(receiver, v.ast.id, ISZ(),
                AST.ResolvedAttr(ae.asStmt.posOpt, v.resOpt, tOpt)),
                tsubst.transformAssignExp(T, ae).resultOpt.getOrElse(ae), AST.Attr(v.posOpt))
            case _ =>
          }
        }
      case _ =>
    }
    return r
  }

  @memoize def minIndex(indexType: AST.Typed): Z = {
    val min: Z = indexType match {
      case AST.Typed.z => 0
      case _ =>
        val subz = subZOpt(indexType).get.ast
        if (subz.isIndex) subz.min
        else if (subz.isZeroIndex) 0
        else subz.min
    }
    return min
  }

  @memoize def sha3TypeImplOf(t: AST.Typed.Name): ISZ[Z] = {
    var r = ISZ[Z]()
    th.typeMap.get(t.ids).get match {
      case info: TypeInfo.Adt if !info.ast.isRoot => r = r :+ sha3(t.string).toZ
      case _ =>
        for (ct <- tsr.typeImpl.descendantsOf(t).elements) {
          th.typeMap.get(ct.ids).get match {
            case info: TypeInfo.Adt if !info.ast.isRoot => r = r :+ sha3(ct.string).toZ
            case _ =>
          }
        }
    }
    return r
  }

  @pure def computeBitwidth(maxValue: Z): Z = {
    var r: Z = 2
    var i = 1
    while (r < maxValue) {
      r = r * 2
      i = i + 1
    }
    return i
  }

  @pure def pow(n: Z, m: Z): Z = {
    var r: Z = 1
    var i: Z = 0
    while (i < m) {
      r = r * n
      i = i + 1
    }
    return r
  }

}