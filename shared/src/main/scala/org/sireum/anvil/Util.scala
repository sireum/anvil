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
import org.sireum.alir.MonotonicDataflowFramework
import org.sireum.lang.symbol.Info
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.{ast => AST}

object Util {
  @enum object PMod {
    "Main"
    "Test"
    "None"
  }

  @datatype class PBox(val p: AST.IR.Procedure) {
    @strictpure override def hash: Z = p.context.hash
    @strictpure def isEqual(other: PBox): B = p.context == other.p.context
  }

  @datatype class LocalOffsetInfo(val offsetMap: HashMap[String, Z], val freeCells: ISZ[LocalOffsetInfo.FreeCell]) {
    @strictpure def get(id: String): Option[Z] = offsetMap.get(id)
    @strictpure def +(kv: (String, Z)): LocalOffsetInfo = LocalOffsetInfo(offsetMap + kv, freeCells)
    @strictpure def --(ids: ISZ[String]): LocalOffsetInfo = LocalOffsetInfo(offsetMap -- ids, freeCells)
    @pure def addFreeCell(newFC: LocalOffsetInfo.FreeCell): LocalOffsetInfo = {
      var fcs = ISZ[LocalOffsetInfo.FreeCell]()
      var added = F
      for (fc <- freeCells) {
        if (!added) {
          if (newFC.size < fc.size) {
            added = T
            fcs = fcs :+ newFC
            fcs = fcs :+ fc
          } else if (newFC.size == fc.size) {
            if (newFC.offset < fc.offset) {
              fcs = fcs :+ newFC
              fcs = fcs :+ fc
            } else {
              fcs = fcs :+ fc
              fcs = fcs :+ newFC
            }
          }
        }
      }
      if (!added) {
        fcs = fcs :+ newFC
      }
      return LocalOffsetInfo(offsetMap, fcs)
    }
  }

  object LocalOffsetInfo {
    @datatype class FreeCell(val offset: Z, val size: Z)

    @strictpure def empty: LocalOffsetInfo = LocalOffsetInfo(HashMap.empty, ISZ())
  }

  @record class TempCollector(val includeAssign: B, var r: HashSMap[Z, HashSSet[AST.Typed]]) extends MAnvilIRTransformer {
    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      r = r + o.n ~> (r.get(o.n).getOrElse(HashSSet.empty[AST.Typed]) + o.tipe)
      return MNone()
    }

    override def post_langastIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      if (includeAssign) {
        r = r + o.lhs ~> (r.get(o.lhs).getOrElse(HashSSet.empty[AST.Typed]) + o.rhs.tipe)
      }
      return MNone()
    }

    override def postIntrinsicTempLoad(o: Intrinsic.TempLoad): MOption[Intrinsic.TempLoad] = {
      if (includeAssign) {
        r = r + o.temp ~> (r.get(o.temp).getOrElse(HashSSet.empty[AST.Typed]) + o.tipe)
      }
      return MNone()
    }
  }

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
                                 val paramSet: HashSet[String],
                                 val localOffsetInfo: LocalOffsetInfo,
                                 val globalMap: HashSMap[QName, Anvil.VarInfo]) extends MAnvilIRTransformer {
    @strictpure def localOffsetMap: HashMap[String, Z] = localOffsetInfo.offsetMap
    override def post_langastIRExpLocalVarRef(o: AST.IR.Exp.LocalVarRef): MOption[AST.IR.Exp] = {
      val localOffset = localOffsetMap.get(o.id).get
      if (anvil.isScalar(o.tipe) || paramSet.contains(o.id)) {
        val t: AST.Typed = if (anvil.isScalar(o.tipe)) o.tipe else anvil.spType
        return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(
          AST.IR.Exp.Intrinsic(Intrinsic.Register(T, anvil.spType, o.pos)), localOffset, anvil.isSigned(t),
          anvil.typeByteSize(t), o.prettyST(anvil.printer), t, o.pos)))
      } else {
        val lhsOffset = AST.IR.Exp.Binary(anvil.spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, anvil.spType, o.pos)),
          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(anvil.spType, localOffset, o.pos), o.pos)
        return MSome(lhsOffset)
      }
    }
    override def post_langastIRExpGlobalVarRef(o: AST.IR.Exp.GlobalVarRef): MOption[AST.IR.Exp] = {
      val globalInfo = globalMap.get(o.name).get
      if (isTempGlobal(anvil, globalInfo.tipe, o.name)) {
        return MNone()
      }
      val globalOffset = AST.IR.Exp.Int(anvil.spType, globalInfo.loc, o.pos)
      if (anvil.isScalar(o.tipe)) {
        return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(globalOffset, 0, anvil.isSigned(o.tipe),
          anvil.typeByteSize(o.tipe), st"", o.tipe, o.pos)))
      } else {
        return MSome(globalOffset)
      }
    }
    override def post_langastIRExpFieldVarRef(o: AST.IR.Exp.FieldVarRef): MOption[AST.IR.Exp] = {
      if (anvil.isSeq(o.receiver.tipe)) {
        assert(o.id == "size")
        return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(
          o.receiver, anvil.typeShaSize, T, anvil.typeByteSize(o.tipe), o.prettyST(anvil.printer), o.tipe, o.pos)))
      } else {
        val (ft, offset) = anvil.classSizeFieldOffsets(o.receiver.tipe.asInstanceOf[AST.Typed.Name]).
          _2.get(o.id).get
        if (anvil.isScalar(ft)) {
          return MSome(AST.IR.Exp.Intrinsic(Intrinsic.Load(o.receiver, offset,
            anvil.isSigned(ft), anvil.typeByteSize(ft), st"", ft, o.pos)))
        } else {
          val rhsOffset: AST.IR.Exp = if (offset != 0) AST.IR.Exp.Binary(anvil.spType, o.receiver,
            AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(anvil.spType, offset, o.pos), o.pos) else o.receiver
          return MSome(rhsOffset)
        }
      }
    }
    override def post_langastIRExpIndexing(o: AST.IR.Exp.Indexing): MOption[AST.IR.Exp] = {
      halt("Infeasible")
    }
  }

  @record class TempRenumberer(val anvil: Anvil, val map: HashMap[Z, Z]) extends MAnvilIRTransformer {
    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      val key = o.n
      map.get(key) match {
        case Some(n) => return MSome(o(n = n))
        case _ => halt(s"Infeasible: ${o.n}, ${o.tipe}, $map")
      }
    }

    override def post_langastIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      val key = o.lhs
      map.get(key) match {
        case Some(n) => return MSome(o(lhs = n))
        case _ => halt(s"Infeasible: ${o.lhs}, ${o.rhs.tipe}, $map")
      }
    }
  }

  @record class TempTypeRenumberer(val anvil: Anvil, val map: HashMap[(Z, AST.Typed), Z]) extends MAnvilIRTransformer {
    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      val key = (o.n, o.tipe)
      map.get(key) match {
        case Some(n) => return MSome(o(n = n))
        case _ => halt(s"Infeasible: ${o.n}, ${o.tipe}, $map")
      }
    }

    override def post_langastIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      val key = (o.lhs, o.rhs.tipe)
      map.get(key) match {
        case Some(n) => return MSome(o(lhs = n))
        case _ => halt(s"Infeasible: ${o.lhs}, ${o.rhs.tipe}, $map")
      }
    }
  }

  @record class CPSubstitutor(val anvil: Anvil, var cpSubstMap: HashMap[Z, Z]) extends MAnvilIRTransformer {
    override def transform_langastIRBasicBlock(o: AST.IR.BasicBlock): MOption[AST.IR.BasicBlock] = {
      val rOpt = extension.Debug.onError[MOption[AST.IR.BasicBlock]](
        super.transform_langastIRBasicBlock(o), (_: String) => { halt(o.prettyST(anvil.printer).render)})
      return rOpt
    }

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
        case in@Intrinsic.Store(AST.IR.Exp.Intrinsic(_: Intrinsic.Register), _, _, _, i@AST.IR.Exp.Int(t, cp, _), _, _, _) if t == anvil.cpType =>
          return MSome(o(intrinsic = in(rhs = i(value = cpSubstMap.get(cp).get))))
        case in@Intrinsic.Store(AST.IR.Exp.Intrinsic(_: Intrinsic.Register), _, _, _, rhs@AST.IR.Exp.Type(_, i@AST.IR.Exp.Int(t, cp, _), _, _), _, _, _) if t == anvil.cpType =>
          return MSome(o(intrinsic = in(rhs = rhs(exp = i(value = cpSubstMap.get(cp).get)))))
        case _ =>
      }
      return MNone()
    }

    override def post_langastIRJumpHalt(o: AST.IR.Jump.Halt): MOption[AST.IR.Jump] = {
      return MSome(AST.IR.Jump.Goto(errorLabel, o.pos))
    }

    override def post_langastIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      o.rhs match {
        case rhs: AST.IR.Exp.Int if rhs.tipe == anvil.cpType =>
          return MSome(o(rhs = rhs(value = cpSubstMap.get(rhs.value).get)))
        case rhs@AST.IR.Exp.Type(_, n: AST.IR.Exp.Int, _, _) if n.tipe == anvil.cpType =>
          return MSome(o(rhs = rhs(exp = n(value = cpSubstMap.get(n.value).get))))
        case _ => return MNone()
      }
    }

    override def post_langastIRStmtAssignGlobal(o: AST.IR.Stmt.Assign.Global): MOption[AST.IR.Stmt.Assign] = {
      o.rhs match {
        case rhs: AST.IR.Exp.Int if rhs.tipe == anvil.cpType =>
          return MSome(o(rhs = rhs(value = cpSubstMap.get(rhs.value).get)))
        case rhs@AST.IR.Exp.Type(_, n: AST.IR.Exp.Int, _, _) if n.tipe == anvil.cpType =>
          return MSome(o(rhs = rhs(exp = n(value = cpSubstMap.get(n.value).get))))
        case _ => return MNone()
      }
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
          name == ISZ("org", "sireum", "anvil", "Runtime", "Ext")
      var changed = F
      var stmts = ISZ[AST.IR.Stmt]()
      for (stmt <- o.stmts) {
        stmt match {
          case stmt@AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.Apply, pos) if isConversions(rhs.owner) =>
            val objectOps = ops.StringOps(rhs.owner(rhs.owner.size - 1))
            val idOps = ops.StringOps(rhs.id)
            assert(rhs.args.size == 1)
            var arg = rhs.args(0)
            if (idOps.s == "z2u") {
              val cond = AST.IR.Exp.Binary(AST.Typed.b, AST.IR.Exp.Int(AST.Typed.z, 0, pos), AST.IR.Exp.Binary.Op.Le,
                arg, pos)
              stmts = stmts :+ AST.IR.Stmt.Assertume(F, cond, Some(AST.IR.ExpBlock(ISZ(), AST.IR.Exp.String(
                st"Out of bound ${rhs.tipe} value".render, pos))), pos)
              stmts = stmts :+ stmt(rhs = AST.IR.Exp.Type(F, rhs.args(0), displayIndexType, pos))
            } else if (idOps.s == "u2z") {
              stmts = stmts :+ stmt(rhs = AST.IR.Exp.Type(F, rhs.args(0), AST.Typed.z, pos))
            } else if (idOps.startsWith("u2RawU32")) {
              val (t, mask) = (AST.Typed.u32, AST.IR.Exp.Int(AST.Typed.u32, 0xFFFFFFFF, pos))
              var r: AST.IR.Exp = AST.IR.Exp.Binary(t, AST.IR.Exp.Type(F, arg, t, pos), AST.IR.Exp.Binary.Op.And,
                mask, pos)
              r = AST.IR.Exp.Type(F, r, rhs.tipe.asInstanceOf[AST.Typed.Name], pos)
              stmts = stmts :+ stmt(rhs = r)
            }  else if (idOps.startsWith("toRaw")) {
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
                    case _ => halt(s"TODO: ${stmt.prettyST(AST.IR.Printer.Empty()).render}")
                  }
                case string"ISB" => halt(s"TODO: ${stmt.prettyST(AST.IR.Printer.Empty()).render}")
                case string"MSB" => halt(s"TODO: ${stmt.prettyST(AST.IR.Printer.Empty()).render}")
                case _ =>
                  if (idOps.s == "toCodePoints") {
                    halt(s"TODO: ${stmt.prettyST(AST.IR.Printer.Empty()).render}")
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
                      arg = AST.IR.Exp.Type(F, arg, rhs.tipe.asInstanceOf[AST.Typed.Name], pos)
                      if (anvil.isSigned(arg.tipe) && anvil.isSigned(rhs.tipe) &&
                        anvil.typeByteSize(arg.tipe) < anvil.typeByteSize(rhs.tipe)) {
                        val n = AST.IR.Exp.Int(rhs.tipe,
                          (anvil.typeByteSize(rhs.tipe) - anvil.typeByteSize(arg.tipe)) * 8, pos)
                        arg = AST.IR.Exp.Binary(rhs.tipe, arg, AST.IR.Exp.Binary.Op.Shl, n, pos)
                        arg = AST.IR.Exp.Binary(rhs.tipe, arg, AST.IR.Exp.Binary.Op.Shr, n, pos)
                      }
                      stmts = stmts :+ stmt(rhs = arg)
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

  @record class RuntimeCheckInserter(val anvil: Anvil, val maxTemp: Z) extends MAnvilIRTransformer {
    override def post_langastIRStmtBlock(o: AST.IR.Stmt.Block): MOption[AST.IR.Stmt] = {
      if (!anvil.config.runtimeCheck) {
        return MNone()
      }
      var changed = F
      var stmts = ISZ[AST.IR.Stmt]()
      for (stmt <- o.stmts) {
        def addIndexingCheck(receiver: AST.IR.Exp, index: AST.IR.Exp, pos: message.Position): Unit = {
          val indexType = receiver.tipe.asInstanceOf[AST.Typed.Name].args(0)
          val min = anvil.minIndex(indexType)
          val lo = AST.IR.Exp.Int(indexType, min, pos)
          val size = maxTemp
          stmts = stmts :+ AST.IR.Stmt.Assign.Temp(size, AST.IR.Exp.FieldVarRef(receiver, "size", AST.Typed.z, pos), pos)
          val hi = AST.IR.Exp.Temp(size, AST.Typed.z, pos)
          if (min != 0) {
            stmts = stmts :+ AST.IR.Stmt.Assign.Temp(size,
              AST.IR.Exp.Binary(AST.Typed.z, hi, AST.IR.Exp.Binary.Op.Sub, lo, pos), pos)
          }
          var hil = index
          if (hil.tipe != AST.Typed.z) {
            hil = AST.IR.Exp.Type(F, hil, AST.Typed.z, pos)
          }
          changed = T
          stmts = stmts :+ AST.IR.Stmt.Assertume(T, AST.IR.Exp.Binary(AST.Typed.b, lo,
            AST.IR.Exp.Binary.Op.Le, index, pos), Some(AST.IR.ExpBlock(ISZ(),
            AST.IR.Exp.String(st"Index out of bounds (low)".render, pos))), pos)
          stmts = stmts :+ AST.IR.Stmt.Assertume(T, AST.IR.Exp.Binary(AST.Typed.b, hil,
            AST.IR.Exp.Binary.Op.Le, hi, pos), Some(AST.IR.ExpBlock(ISZ(),
            AST.IR.Exp.String(st"Index out of bounds (high)".render, pos))), pos)
          stmts = stmts :+ stmt
        }
        stmt match {
          case stmt: AST.IR.Stmt.Assign.Index => addIndexingCheck(stmt.receiver, stmt.index, stmt.pos)
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
                }
                addRangeCheck()
              case rhs: AST.IR.Exp.Unary if rhs.tipe != AST.Typed.b => addRangeCheck()
              case rhs: AST.IR.Exp.Indexing => addIndexingCheck(rhs.exp, rhs.index, pos)
              case _ => stmts = stmts :+ stmt
            }
          case _ => stmts = stmts :+ stmt
        }
      }
      return if (changed) MSome(o(stmts = stmts)) else MNone()
    }
  }

  @record class IntTransformer(val anvil: Anvil) extends MAnvilIRTransformer {
    override def post_langastIRExpInt(o: AST.IR.Exp.Int): MOption[AST.IR.Exp] = {
      val n: U64 = conversions.Z.toU64(if (o.value < 0) o.value + anvil.pow(2, 64) else o.value)
      val v = IRSimulator.Value.fromRawU64(anvil, n, o.tipe).value
      return if (v != o.value) MSome(o(value = v)) else MNone()
    }
  }

  @record class FloatEqualityTransformer(val anvil: Anvil) extends MAnvilIRTransformer {
    override def post_langastIRExpBinary(o: AST.IR.Exp.Binary): MOption[AST.IR.Exp] = {
      val ct: AST.Typed.Name = o.tipe match {
        case AST.Typed.f32 => AST.Typed.u32
        case AST.Typed.f64 => AST.Typed.u64
        case _ => return MNone()
      }
      if (o.op == AST.IR.Exp.Binary.Op.Eq || o.op == AST.IR.Exp.Binary.Op.Ne) {
        return MSome(o(
          left = AST.IR.Exp.Type(F, o.left, ct, o.left.pos),
          right = AST.IR.Exp.Type(F, o.right, ct, o.right.pos)))
      }
//      if (o.op == AST.IR.Exp.Binary.Op.FpEq) {
//        return MSome(o(op = AST.IR.Exp.Binary.Op.Eq))
//      }
//      if (o.op == AST.IR.Exp.Binary.Op.FpNe) {
//        return MSome(o(op = AST.IR.Exp.Binary.Op.Ne))
//      }
      return MNone()
    }
  }

  @datatype class TempScalarOrSpLV(val anvil: Anvil, val cfg: Graph[Z, Unit]) extends MonotonicDataflowFramework.Basic[(Z, AST.Typed)] {
    @strictpure def isForward: B = F
    @strictpure def isLUB: B = T
    @strictpure def iota: HashSSet[(Z, AST.Typed)] = HashSSet.empty
    @strictpure def init: HashSSet[(Z, AST.Typed)] = HashSSet.empty
    @strictpure def toScalar(t: AST.Typed): AST.Typed = if (anvil.isScalar(t)) t else anvil.spType
    @pure def genGround(g: AST.IR.Stmt.Ground): HashSSet[(Z, AST.Typed)] = {
      val tc = TempCollector(F, HashSMap.empty)
      g match {
        case g: AST.IR.Stmt.Assign.Temp => tc.transform_langastIRExp(g.rhs)
        case _ => tc.transform_langastIRStmtGround(g)
      }
      return HashSSet ++ (for (pair <- tc.r.entries; t <- pair._2.elements) yield (pair._1, toScalar(t)))
    }
    @pure def killGround(g: AST.IR.Stmt.Ground): HashSSet[(Z, AST.Typed)] = {
      g match {
        case g: AST.IR.Stmt.Assign.Temp => return HashSSet.empty[(Z, AST.Typed)] + (g.lhs, toScalar(g.rhs.tipe))
        case AST.IR.Stmt.Intrinsic(in: Intrinsic.TempLoad) => return HashSSet.empty[(Z, AST.Typed)] + (in.temp, toScalar(in.tipe))
        case _ => return HashSSet.empty
      }
    }
    @pure def genJump(j: AST.IR.Jump): HashSSet[(Z, AST.Typed)] = {
      val tc = TempCollector(F, HashSMap.empty)
      tc.transform_langastIRJump(j)
      return HashSSet ++ (for (pair <- tc.r.entries; t <- pair._2.elements) yield (pair._1, toScalar(t)))
    }
    @strictpure def killJump(j: AST.IR.Jump): HashSSet[(Z, AST.Typed)] = HashSSet.empty
  }

  @record class LocalCollector(var r: HashSSet[(String, AST.Typed)]) extends MAnvilIRTransformer {
    override def post_langastIRExpLocalVarRef(o: AST.IR.Exp.LocalVarRef): MOption[AST.IR.Exp] = {
      r = r + (o.id, o.tipe)
      return MNone()
    }
  }

  @record class StringCollector(var r: HashSSet[AST.IR.Exp.String]) extends MAnvilIRTransformer {
    override def post_langastIRExpString(o: AST.IR.Exp.String): MOption[AST.IR.Exp] = {
      r = r + o
      return MNone()
    }
  }

  @record class ExpSubstitutor(val m: HashMap[AST.IR.Exp, AST.IR.Exp]) extends MAnvilIRTransformer {
    override def pre_langastIRExp(o: AST.IR.Exp): MAnvilIRTransformer.PreResult[AST.IR.Exp] = {
      m.get(o) match {
        case Some(e) => return MAnvilIRTransformer.PreResult(F, MSome(e))
        case _ => return MAnvilIRTransformer.PreResult(T, MNone())
      }
    }
  }

  @record class LocalTempSubstutitor(val m: HashSMap[String, Z]) extends MAnvilIRTransformer {
    override def post_langastIRExpLocalVarRef(o: AST.IR.Exp.LocalVarRef): MOption[AST.IR.Exp] = {
      m.get(o.id) match {
        case Some(n) => return MSome(AST.IR.Exp.Temp(n, o.tipe, o.pos))
        case _ =>
      }
      return MNone()
    }

    override def post_langastIRStmtAssignLocal(o: AST.IR.Stmt.Assign.Local): MOption[AST.IR.Stmt.Assign] = {
      m.get(o.lhs) match {
        case Some(n) => return MSome(AST.IR.Stmt.Assign.Temp(n, o.rhs, o.pos))
        case _ =>
      }
      return MNone()
    }
  }

  @datatype class LocalDeclLV(val cfg: Graph[Z, Unit]) extends MonotonicDataflowFramework.Basic[(String, AST.Typed)] {
    @strictpure def isForward: B = F
    @strictpure def isLUB: B = T
    @strictpure def iota: HashSSet[(String, AST.Typed)] = HashSSet.empty
    @strictpure def init: HashSSet[(String, AST.Typed)] = HashSSet.empty
    @pure def genGround(g: AST.IR.Stmt.Ground): HashSSet[(String, AST.Typed)] = {
      val lc = LocalCollector(HashSSet.empty)
      g match {
        case g: AST.IR.Stmt.Assign.Local =>
          lc.transform_langastIRExp(g.rhs)
          lc.r = lc.r + (g.lhs, g.tipe)
        case _ => lc.transform_langastIRStmtGround(g)
      }
      return lc.r
    }
    @pure def killGround(g: AST.IR.Stmt.Ground): HashSSet[(String, AST.Typed)] = {
      g match {
        case g: AST.IR.Stmt.Decl if !g.undecl =>
          return HashSSet.empty[(String, AST.Typed)] ++ (for (slot <- g.locals) yield (slot.id, slot.tipe))
        case _ => return HashSSet.empty
      }
    }
    @pure def genJump(j: AST.IR.Jump): HashSSet[(String, AST.Typed)] = {
      val tc = LocalCollector(HashSSet.empty)
      tc.transform_langastIRJump(j)
      return tc.r
    }
    @strictpure def killJump(j: AST.IR.Jump): HashSSet[(String, AST.Typed)] = HashSSet.empty
  }

  @datatype class AnvilIRPrinter(val anvil: Anvil, val ipAlloc: IpAlloc) extends AST.IR.Printer {
    @strictpure def exp(e: AST.IR.Exp): Option[ST] = {
      e match {
        case e: AST.IR.Exp.Temp if anvil.config.splitTempSizes => Some(tempST(anvil, e.tipe, e.n))
        case _ =>
          val sign: String = if (anvil.isSigned(e.tipe)) ".S" else ".U"
          val op: String = e match {
            case e: AST.IR.Exp.Binary => s"${e.op}$sign"
            case e: AST.IR.Exp.Int => if (e.value >= 0) s"Add$sign" else s"Sub$sign"
            case AST.IR.Exp.Intrinsic(_: Intrinsic.Indexing) => "Indexing"
            case _ => s"Add$sign"
          }
          ipAlloc.allocMap.get(IpAlloc.Ext.exp(e)) match {
            case Some(n) =>
              assert(op != "", s"$e")
              Some(st"${e.prettyRawST(this)} /* IP#$n $op */")
            case _ => None()
          }
      }
    }
    @strictpure def stmt(stmt: AST.IR.Stmt): Option[ST] = stmt match {
      case stmt: AST.IR.Stmt.Assign.Temp if anvil.config.splitTempSizes =>
        Some(st"${tempST(anvil, stmt.rhs.tipe, stmt.lhs)} = ${stmt.rhs.prettyST(this)}")
      case AST.IR.Stmt.Intrinsic(in: Intrinsic.RegisterAssign) if in.isInc =>
        ipAlloc.allocMap.get(IpAlloc.Ext.exp(in.value)) match {
          case Some(n) =>
            val op: String = in.value match {
              case v: AST.IR.Exp.Int if v.value < 0 => "Sub"
              case _ => "Add"
            }
            Some(st"${stmt.prettyRawST(this)} /* IP#$n $op.U */")
          case _ => None()
        }
      case _ => None()
    }
    @strictpure def jump(j: AST.IR.Jump): Option[ST] = None()
  }

  @datatype class TempVector(val unsigneds: ISZ[Z], val signeds: HashSMap[Z, Z], val fp32Count: Z, val fp64Count: Z) {
    @strictpure def combine(other: TempVector, f: (Z, Z) => Z @pure): TempVector = TempVector(
      unsigneds = for (pair <- ops.ISZOps(unsigneds).zip(other.unsigneds)) yield f(pair._1, pair._2),
      signeds = HashSMap.empty[Z, Z] ++ (for (entry <- signeds.entries) yield (entry._1, f(entry._2, other.signeds.get(entry._1).get))),
      fp32Count = f(fp32Count, other.fp32Count),
      fp64Count = f(fp64Count, other.fp64Count)
    )
    @strictpure def max(other: TempVector): TempVector = combine(other, (n: Z, m: Z) => if (n < m) m else n)
    @strictpure def unsignedCount(bitWidth: Z): Z = {
      assert(1 <= bitWidth & bitWidth <= 64)
      unsigneds(bitWidth - 1)
    }
    @strictpure def setUnsignedCount(bitWidth: Z, count: Z): TempVector = {
      assert(1 <= bitWidth & bitWidth <= 64)
      val thiz = this
      thiz(unsigneds = thiz.unsigneds((bitWidth - 1) ~> count))
    }
    @strictpure def signedCount(bitWidth: Z): Z = {
      assert(bitWidth == 8 | bitWidth == 16 | bitWidth == 32 | bitWidth == 64)
      signeds.get(bitWidth).get
    }
    @strictpure def setSignedCount(bitWidth: Z, count: Z): TempVector = {
      assert(bitWidth == 8 | bitWidth == 16 | bitWidth == 32 | bitWidth == 64)
      val thiz = this
      thiz(signeds = thiz.signeds + bitWidth ~> count)
    }
    @strictpure def incUnsigned(bitWidth: Z): TempVector = setUnsignedCount(bitWidth, unsignedCount(bitWidth) + 1)
    @strictpure def incSigned(bitWidth: Z): TempVector = setSignedCount(bitWidth, signedCount(bitWidth) + 1)
    @strictpure def setFP32Count(count: Z): TempVector = {
      val thiz = this
      thiz(fp32Count = count)
    }
    @strictpure def setFP64Count(count: Z): TempVector = {
      val thiz = this
      thiz(fp64Count = count)
    }
    @strictpure def incFP32(): TempVector = setFP32Count(fp32Count + 1)
    @strictpure def incFP64(): TempVector = setFP64Count(fp64Count + 1)
    @strictpure def typeCount(anvil: Anvil, tipe: AST.Typed): Z = {
      val t: AST.Typed = if (anvil.isScalar(tipe)) tipe else anvil.spType
      t match {
        case AST.Typed.f32 => fp32Count
        case AST.Typed.f64 => fp64Count
        case _ => if (anvil.isSigned(t)) signedCount(anvil.typeBitSize(t)) else unsignedCount(anvil.typeBitSize(t))
      }
    }
    @pure def incType(anvil: Anvil, tipe: AST.Typed): TempVector = {
      var r = this
      val t: AST.Typed = if (anvil.isScalar(tipe)) tipe else anvil.spType
      t match {
        case AST.Typed.f32 => r = r.incFP32()
        case AST.Typed.f64 => r = r.incFP64()
        case _ =>
          if (anvil.isSigned(t)) {
            r = r.incSigned(anvil.typeBitSize(t))
          } else {
            r = r.incUnsigned(anvil.typeBitSize(t))
          }
      }
      return r
    }
    @pure def incParams(anvil: Anvil, m: HashSMap[String, Anvil.VarInfo]): TempVector = {
      var r = this
      if (anvil.config.tempLocal) {
        for (idInfo <- m.entries if !ignoredTempLocal.contains(idInfo._1) && anvil.isScalar(idInfo._2.tipe)) {
          r = r.incType(anvil, idInfo._2.tipe)
        }
      } else {
        for (info <- m.values) {
          r = r.incType(anvil, info.tipe)
        }
      }
      return r
    }
    @memoize def maxCount: Z = {
      var r: Z = fp32Count
      if (r < fp64Count) {
        r = fp64Count
      }
      for (u <- unsigneds if r < u) {
        r = u
      }
      for (s <- signeds.values if r < s) {
        r = s
      }
      return r
    }
    @memoize def totalCount: Z = {
      var r: Z = fp32Count + fp64Count
      for (u <- unsigneds) {
        r = r + u
      }
      for (s <- signeds.values) {
        r = r + s
      }
      return r
    }
    @pure def setType(anvil: Anvil, tipe: AST.Typed, n: Z): TempVector = {
      val count = n + 1
      val t: AST.Typed = if (anvil.isScalar(tipe)) tipe else anvil.spType
      t match {
        case AST.Typed.f32 if count > fp32Count => return setFP32Count(count)
        case AST.Typed.f64 if count > fp64Count => return setFP64Count(count)
        case _ =>
          val i = anvil.typeBitSize(t)
          if (anvil.isSigned(t)) {
            if (signedCount(i) < count) {
              return setSignedCount(i, count)
            }
          } else {
            if (unsignedCount(i) < count) {
              return setUnsignedCount(i, count)
            }
          }
      }
      return this
    }
    @pure override def string: String = {
      var sts = ISZ[ST]()
      sts = sts :+ st"${(for (i <- unsigneds.indices if unsigneds(i) != 0) yield st"$$${i + 1}U = ${unsigneds(i)}", ", ")}"
      sts = sts :+ st"${(for (pair <- signeds.entries if pair._2 != 0) yield st"$$${pair._1}S = ${pair._2}", ", ")}"
      var fpOpt = Option.none[ST]()
      if (fp32Count > 0) {
        fpOpt = Some(st"$$FP32 = $fp32Count")
      }
      if (fp64Count > 0) {
        val fp64ST = st"$$FP64 = $fp64Count"
        fpOpt match {
          case Some(fp) => fpOpt = Some(st"$fp, $fp64ST")
          case _ => fpOpt = Some(fp64ST)
        }
      }
      fpOpt match {
        case Some(fp) => sts = sts :+ fp
        case _ =>
      }
      val r =
        st"""{
            |  ${(sts, ", ")}
            |}"""
      return r.render
    }
  }

  object TempVector {
    @strictpure def empty: TempVector = TempVector(ISZ.create(64, 0),
      HashSMap.empty[Z, Z] ++ (for (i <- ISZ(8, 16, 32, 64)) yield (i, 0)), 0, 0)
  }

  @record class ScalarLocalTempCounter(val anvil: Anvil, var r: TempVector) extends MAnvilIRTransformer {
    override def post_langastIRStmtDecl(o: AST.IR.Stmt.Decl): MOption[AST.IR.Stmt.Ground] = {
      if (o.undecl) {
        return MNone()
      }
      for (l <- o.locals if anvil.isScalar(l.tipe)) {
        r = r.incType(anvil, l.tipe)
      }
      return MNone()
    }
  }

  @record class TempIncrementer(val anvil: Anvil, val maxLocalTemps: TempVector) extends MAnvilIRTransformer {
    @strictpure def maxLocalTemp(tipe: AST.Typed): Z = {
      if (anvil.config.splitTempSizes) {
        val t: AST.Typed = if (anvil.isScalar(tipe)) tipe else anvil.spType
        t match {
          case AST.Typed.f32 => maxLocalTemps.fp32Count
          case AST.Typed.f64 => maxLocalTemps.fp64Count
          case _ =>
            if (anvil.isSigned(t)) {
              maxLocalTemps.signedCount(anvil.typeBitSize(t))
            } else {
              maxLocalTemps.unsignedCount(anvil.typeBitSize(t))
            }
        }
      } else {
        maxLocalTemps.totalCount
      }
    }

    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      return MSome(o(n = maxLocalTemp(o.tipe) + o.n))
    }

    override def post_langastIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      return MSome(o(lhs = maxLocalTemp(o.rhs.tipe) + o.lhs))
    }

    override def postIntrinsicTempLoad(o: Intrinsic.TempLoad): MOption[Intrinsic.TempLoad] = {
      return MSome(o(temp = maxLocalTemp(o.tipe) + o.temp))
    }
  }

  @record class TempMaxCounter(val anvil: Anvil, var seen: HashSet[(Z, AST.Typed)], var r: TempVector) extends MAnvilIRTransformer {
    override def post_langastIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      val t: AST.Typed = if (anvil.config.splitTempSizes) o.tipe else AST.Typed.u64
      val key = (o.n, t)
      if (seen.contains(key)) {
        return MNone()
      }
      r = r.setType(anvil, t, key._1)
      seen = seen + key
      return MNone()
    }

    override def post_langastIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      val t: AST.Typed = if (anvil.config.splitTempSizes) o.rhs.tipe else AST.Typed.u64
      val key = (o.lhs, t)
      if (seen.contains(key)) {
        return MNone()
      }
      r = r.setType(anvil, t, key._1)
      seen = seen + key
      return MNone()
    }

    override def postIntrinsicTempLoad(o: Intrinsic.TempLoad): MOption[Intrinsic.TempLoad] = {
      val t: AST.Typed = if (anvil.config.splitTempSizes) o.tipe else AST.Typed.u64
      val key = (o.temp, t)
      if (seen.contains(key)) {
        return MNone()
      }
      r = r.setType(anvil, t, key._1)
      seen = seen + key
      return MNone()
    }
  }

  @record class IndexingCounter(var count: Z) extends MAnvilIRTransformer {
    override def postIntrinsicIndexing(o: Intrinsic.Indexing): MOption[Intrinsic.Indexing] = {
      count = count + 1
      return MNone()
    }
  }

  @record class IpCounter(val anvil: Anvil,
                          var ipMap: HashSMap[IpAlloc.Exp, Z],
                          var binopMap: HashSMap[(B, AST.IR.Exp.Binary.Op.Type), Z],
                          var indexing: Z) extends MAnvilIRTransformer {
    override def pre_langastIRExpBinary(o: AST.IR.Exp.Binary): MAnvilIRTransformer.PreResult[AST.IR.Exp] = {
      binExp(o)
      return MAnvilIRTransformer.PreResult_langastIRExpBinary
    }

    override def preIntrinsicIndexing(o: Intrinsic.Indexing): MAnvilIRTransformer.PreResult[Intrinsic.Indexing] = {
      ipMap = ipMap + IpAlloc.Ext.exp(AST.IR.Exp.Intrinsic(o)) ~> indexing
      indexing = indexing + 1
      return MAnvilIRTransformer.PreResultIntrinsicIndexing
    }

    def binExp(o: AST.IR.Exp): Unit = {
      o match {
        case o: AST.IR.Exp.Binary =>
          val t: AST.Typed = if (anvil.isScalar(o.tipe)) o.left.tipe else anvil.spType
          val key = (anvil.isSigned(t), o.op)
          val n = binopMap.get(key).getOrElseEager(0)
          ipMap = ipMap + IpAlloc.Ext.exp(o) ~> n
          binopMap = binopMap + key ~> (n + 1)
        case _ =>
      }
    }

    override def preIntrinsicCopy(o: Intrinsic.Copy): MAnvilIRTransformer.PreResult[Intrinsic.Copy] = {
      binExp(o.lhsOffset)
      return MAnvilIRTransformer.PreResultIntrinsicCopy
    }

    override def preIntrinsicTempLoad(o: Intrinsic.TempLoad): MAnvilIRTransformer.PreResult[Intrinsic.TempLoad] = {
      binExp(o.rhsOffset)
      return MAnvilIRTransformer.PreResultIntrinsicTempLoad
    }

    override def preIntrinsicLoad(o: Intrinsic.Load): MAnvilIRTransformer.PreResult[Intrinsic.Load] = {
      binExp(o.rhsOffset)
      return MAnvilIRTransformer.PreResultIntrinsicLoad
    }

    override def preIntrinsicStore(o: Intrinsic.Store): MAnvilIRTransformer.PreResult[Intrinsic.Store] = {
      binExp(o.lhsOffset)
      return MAnvilIRTransformer.PreResultIntrinsicStore
    }

    override def preIntrinsicRegisterAssign(o: Intrinsic.RegisterAssign): MAnvilIRTransformer.PreResult[Intrinsic.RegisterAssign] = {
      if (o.isInc) {
        val t: AST.Typed = if (o.isSP) anvil.spType else anvil.dpType
        val op: AST.IR.Exp.Binary.Op.Type = o.value match {
          case v: AST.IR.Exp.Int if v.value < 0 => AST.IR.Exp.Binary.Op.Sub
          case _ => AST.IR.Exp.Binary.Op.Add
        }
        val key = (anvil.isSigned(t), op)
        val n = binopMap.get(key).getOrElseEager(0)
        ipMap = ipMap + IpAlloc.Ext.exp(o.value) ~> n
        binopMap = binopMap + key ~> (n + 1)
      }
      return MAnvilIRTransformer.PreResultIntrinsicRegisterAssign
    }
  }

  @record class CyclesApprox(val anvil: Anvil, val copyBytes: Z, var cycles: Z) extends MAnvilIRTransformer {
    val useIP: B = anvil.config.useIP
    val xilinxIP: B = !anvil.config.noXilinxIp
    def updateCycles(n: Z): Unit = {
      if (n > cycles) {
        cycles = n
      }
    }
    override def post_langastIRExpBinary(o: AST.IR.Exp.Binary): MOption[AST.IR.Exp] = {
      o.op match {
        case AST.IR.Exp.Binary.Op.Add => if (useIP) {
          updateCycles(if (xilinxIP) 6 else 3)
        }
        case AST.IR.Exp.Binary.Op.Sub => if (useIP) {
          updateCycles(if (xilinxIP) 6 else 3)
        }
        case AST.IR.Exp.Binary.Op.Mul => if (useIP) {
          updateCycles(if (xilinxIP) 20 else 2)
        }
        case AST.IR.Exp.Binary.Op.Div => if (useIP) {
          updateCycles(70)
        }
        case AST.IR.Exp.Binary.Op.Rem => if (useIP) {
          updateCycles(70)
        }
        case _ =>
      }
      return MNone()
    }

    override def postIntrinsicIndexing(o: Intrinsic.Indexing): MOption[Intrinsic.Indexing] = {
      if (useIP) {
        updateCycles(4)
      }
      return MNone()
    }

    override def postIntrinsicLoad(o: Intrinsic.Load): MOption[Intrinsic.Load] = {
      if (useIP) {
        updateCycles(8)
      }
      return MNone()
    }

    override def postIntrinsicTempLoad(o: Intrinsic.TempLoad): MOption[Intrinsic.TempLoad] = {
      if (useIP) {
        updateCycles(8)
      }
      return MNone()
    }

    override def postIntrinsicStore(o: Intrinsic.Store): MOption[Intrinsic.Store] = {
      if (useIP) {
        updateCycles(10)
      }
      return MNone()
    }

    override def postIntrinsicCopy(o: Intrinsic.Copy): MOption[Intrinsic.Copy] = {
      anvil.config.memoryAccess match {
        case Anvil.Config.MemoryAccess.Default => updateCycles((copyBytes / anvil.config.copySize) + (copyBytes % anvil.config.copySize))
        case _ => updateCycles(copyBytes * 4)
      }
      return MNone()
    }
  }

  @record class WellFormedChecker extends MAnvilIRTransformer {
    override def postIntrinsicLoad(o: Intrinsic.Load): MOption[Intrinsic.Load] = {
      //halt("Intrinsic.Load should have been rewritten")
      return MNone()
    }
  }

  @datatype class IpAlloc(val allocMap: HashSMap[IpAlloc.Exp, Z],
                          val binopAllocSizeMap: HashSMap[(B, AST.IR.Exp.Binary.Op.Type), Z],
                          val indexingAllocSize: Z)
  object IpAlloc {
    @sig trait Exp {
      @pure def ast: AST.IR.Exp
    }
    @ext("IpAlloc_Ext") object Ext {
      @pure def exp(e: AST.IR.Exp): IpAlloc.Exp = $
    }
  }

  @record class BinopDetector(var hasBinop: B) extends MAnvilIRTransformer {
    override def post_langastIRExpBinary(o: AST.IR.Exp.Binary): MOption[AST.IR.Exp] = {
      hasBinop = T
      return MNone()
    }
  }
  val kind: String = "Anvil"
  val exitLabel: Z = 0
  val errorLabel: Z = 1
  val startingLabel: Z = 3
  val returnLocalId: String = "$ret"
  val resultLocalId: String = "$res"
  val constructLocalId: String = "$new"
  val typeFieldId: String = "$type"
  val sizeFieldId: String = "$size"
  val sfCallerId: String = "$sfCaller"
  val sfCurrentId: String = "$sfCurrentId"
  val sfLocId: String = "$sfLoc"
  val sfDescId: String = "$sfDesc"
  val dataId: String = "$data"
  val testId: String = "$test"
  val testNumNamePad: ISZ[String] = ISZ("$testNumPad")
  val testNumName: ISZ[String] = ISZ("$testNum")
  val sfLocType: AST.Typed.Name = AST.Typed.u32
  val objInitId: String = "<objinit>"
  val newInitId: String = "<init>"
  val binopLeftId: String = "l"
  val binopRightId: String = "r"
  val memName: ISZ[String] = ISZ("$memory")
  val memTypeName: ISZ[String] = ISZ(typeFieldId)
  val memSizeName: ISZ[String] = ISZ(sizeFieldId)
  val displayId: String = "$display"
  val displayName: ISZ[String] = ISZ(displayId)
  val displayIndexType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "anvil", "PrinterIndex", "U"), ISZ())
  val displayType: AST.Typed.Name = AST.Typed.Name(AST.Typed.msName, ISZ(displayIndexType, AST.Typed.u8))
  val f32DigitIndexType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "anvil", "PrinterIndex", "I50"), ISZ())
  val f64DigitIndexType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "anvil", "PrinterIndex", "I320"), ISZ())
  val f32DigitBufferType: AST.Typed.Name = AST.Typed.Name(AST.Typed.msName, ISZ(f32DigitIndexType, AST.Typed.u8))
  val f64DigitBufferType: AST.Typed.Name = AST.Typed.Name(AST.Typed.msName, ISZ(f64DigitIndexType, AST.Typed.u8))
  val runtimeName: QName = AST.Typed.sireumName :+ "anvil" :+ "Runtime"
  val intrinsicName: QName = runtimeName :+ "Intrinsic"
  val mainAnnName: QName = AST.Typed.sireumName :+ "anvil" :+ "hls"
  val testAnnName: QName = AST.Typed.sireumName :+ "anvil" :+ "test"
  val readId: String = "read"
  val writeId: String = "write"
  val readAlignId: String = "readAlign"
  val writeAlignId: String = "writeAlign"
  val leftShiftId: String = "leftShift"
  val rightShiftId: String = "rightShift"
  val readName: QName = intrinsicName :+ readId
  val writeName: QName = intrinsicName :+ writeId
  val leftShiftName: QName = intrinsicName :+ leftShiftId
  val rightShiftName: QName = intrinsicName :+ rightShiftId
  val readBaseAddr: QName = intrinsicName :+ "readBaseAddr"
  val readOffset: QName = intrinsicName :+ "readOffset"
  val readLen: QName = intrinsicName :+ "readLen"
  val readRes: QName = intrinsicName :+ "readRes"
  val readRet: QName = intrinsicName :+ "readRet"
  val writeBaseAddr: QName = intrinsicName :+ "writeBaseAddr"
  val writeOffset: QName = intrinsicName :+ "writeOffset"
  val writeLen: QName = intrinsicName :+ "writeLen"
  val writeValue: QName = intrinsicName :+ "writeValue"
  val writeRet: QName = intrinsicName :+ "writeRet"
  val readAlignAddr: QName = intrinsicName :+ "readAlignAddr"
  val readAlignRes: QName = intrinsicName :+ "readAlignRes"
  val writeAlignAddr: QName = intrinsicName :+ "writeAlignAddr"
  val writeAlignValue: QName = intrinsicName :+ "writeAlignValue"

  val runtimePrintMethodTypeMap: HashSMap[String, AST.Typed.Fun] = HashSMap.empty[String, AST.Typed.Fun] +
    "printB" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.b), AST.Typed.u64) +
    "printC" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.c), AST.Typed.u64) +
    "printS64" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.s64), AST.Typed.u64) +
    "printU64" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.u64), AST.Typed.u64) +
    "printU64Hex" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.u64, AST.Typed.z), AST.Typed.u64) +
    "f32Digit" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(f32DigitBufferType, f32DigitIndexType, AST.Typed.f32), AST.Typed.u64) +
    "f64Digit" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(f64DigitBufferType, f64DigitIndexType, AST.Typed.f64), AST.Typed.u64) +
    "printF32_2" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.f32), AST.Typed.u64) +
    "printF64_2" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.f64), AST.Typed.u64) +
    "printString" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, AST.Typed.string), AST.Typed.u64) +
    "load" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType), displayIndexType) +
    "printStackTrace" ~> AST.Typed.Fun(AST.Purity.Impure, F, ISZ(displayType, displayIndexType, displayIndexType, displayIndexType, displayIndexType, displayIndexType), AST.Typed.unit)

  val ignoreGlobalInits: HashSet[QName] = HashSet.empty[QName] + displayName + memTypeName + memSizeName + testNumName
  val syntheticMethodIds: HashSet[String] = HashSet.empty[String] + objInitId + newInitId + testId
  val ignoredTempLocal: HashSet[String] = HashSet.empty[String] + sfLocId + sfDescId + sfCallerId + sfCurrentId + s"$resultLocalId$dataId"
  val spType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "SP"), ISZ())

  @strictpure def tempST(anvil: Anvil, tipe: AST.Typed, n: Z): ST = {
    val t: AST.Typed =
      if (anvil.config.splitTempSizes) if (anvil.isScalar(tipe)) tipe else anvil.spType
      else AST.Typed.u64
    tempST2(anvil.isFP(t), anvil.isSigned(t), anvil.typeBitSize(t), n)
  }

  @strictpure def tempST2(isFP: B, isSigned: B, bitSize: Z, n: Z): ST = {
    if (isFP) st"$$${bitSize}F.$n"
    else st"$$$bitSize${if (isSigned) "S" else "U"}.$n"
  }

  @pure def indexing(os: OffsetSubsitutor,
                     receiver: AST.IR.Exp,
                     index: AST.IR.Exp,
                     pos: message.Position): AST.IR.Exp = {
    val anvil = os.anvil
    val receiverType = receiver.tipe.asInstanceOf[AST.Typed.Name]
    val indexType = receiverType.args(0)
    val elementType = receiverType.args(1)
    val min = anvil.minIndex(indexType)
    var maskOpt = Option.none[Z]()
    var idx: AST.IR.Exp = os.transform_langastIRExp(index).getOrElse(index) match {
      case indexMask: AST.IR.Exp.Binary if indexMask.op == AST.IR.Exp.Binary.Op.And && indexMask.right.isInstanceOf[AST.IR.Exp.Int] =>
        maskOpt = Some(indexMask.right.asInstanceOf[AST.IR.Exp.Int].value)
        indexMask.left
      case i => i
    }
    val rcv = os.transform_langastIRExp(receiver).getOrElse(receiver)
    if (idx.tipe != anvil.spType) {
      idx = AST.IR.Exp.Type(F, idx, anvil.spType, idx.pos)
    }
    val indexOffset: AST.IR.Exp = if (min == 0) idx else AST.IR.Exp.Binary(
      anvil.spType, idx, AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(anvil.spType, min, idx.pos), idx.pos)
    val elementSize = anvil.typeByteSize(elementType)
    var dataOffset = anvil.typeShaSize + anvil.typeByteSize(AST.Typed.z)
    if (anvil.config.alignAxi4 && !anvil.isScalar(elementType)) {
      dataOffset = anvil.pad64(dataOffset)
    }
    if (anvil.config.useIP) {
      return AST.IR.Exp.Intrinsic(Intrinsic.Indexing(rcv, dataOffset, indexOffset, maskOpt, elementSize, anvil.spType, pos))
    } else {
      val baseDataOffset = AST.IR.Exp.Binary(anvil.spType, rcv, AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(anvil.spType,
        dataOffset, receiver.pos), receiver.pos)
      val elementOffset: AST.IR.Exp = if (elementSize == 1) indexOffset else AST.IR.Exp.Binary(anvil.spType,
        indexOffset, AST.IR.Exp.Binary.Op.Mul, AST.IR.Exp.Int(anvil.spType, anvil.typeByteSize(elementType),
          idx.pos), idx.pos)
      return AST.IR.Exp.Binary(anvil.spType, baseDataOffset, AST.IR.Exp.Binary.Op.Add, elementOffset, receiver.pos)
    }
  }

  @pure def postProcessStackTrace(procDescMap: HashSMap[U32, String], display: String): Option[String] = {
    var lines = ISZ[String]()
    var changed = F
    for (line <- ops.StringOps(display).split((c: C) => c == '\n')) {
      val lineOps = ops.StringOps(line)
      val i = lineOps.lastIndexOf(':')
      var replaced = F
      if (lineOps.startsWith("꧐") && lineOps.lastIndexOf(':') > 0) {
        val desc = lineOps.substring(1, i)
        U32(s"0x$desc") match {
          case Some(n) =>
            procDescMap.get(n) match {
              case Some(s) =>
                Z(lineOps.substring(i + 1, line.size)) match {
                  case Some(ln) =>
                    replaced = T
                    changed = T
                    lines = lines :+ s"  $s$ln)"
                  case _ =>
                }
              case _ =>
            }
          case _ =>
        }
      }
      if (!replaced) {
        lines = lines :+ line
      }
    }
    return if (changed) Some(st"${(lines, "\n")}".render) else None()
  }

  @pure def programMaxTemps(anvil: Anvil, p: AST.IR.Program): TempVector = {
    val tmc = TempMaxCounter(anvil, HashSet.empty, TempVector.empty)
    tmc.transform_langastIRProgram(p)
    return tmc.r
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

  @pure def maxIPs(anvil: Anvil, p: AST.IR.Procedure): IpAlloc = {
    var binopMap = HashSMap.empty[(B, AST.IR.Exp.Binary.Op.Type), Z]
    var indexing: Z = 0
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    for (b <- body.blocks) {
      val ic = IpCounter(anvil, HashSMap.empty, HashSMap.empty, 0)
      ic.transform_langastIRBasicBlock(b)
      if (indexing < ic.indexing) {
        indexing = ic.indexing
      }
      for (k <- binopMap.keySet.union(ic.binopMap.keySet).elements) {
        val v1 = binopMap.get(k).getOrElseEager(0)
        val v2 = ic.binopMap.get(k).getOrElseEager(0)
        binopMap = binopMap + k ~> (if (v1 < v2) v2 else v1)
      }
    }
    return IpAlloc(HashSMap.empty, binopMap, indexing)
  }

  @pure def ipAlloc(anvil: Anvil, p: AST.IR.Procedure, opMax: Z): IpAlloc = {
    val max = maxIPs(anvil, p)
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var r = HashSMap.empty[IpAlloc.Exp, Z]
    var binopAllocMap = HashSMap.empty[(B, AST.IR.Exp.Binary.Op.Type), ISZ[Z]]
    var indexingAlloc = ISZ[Z]()
    for (b <- body.blocks) {
      def allocate(ic: IpCounter): Unit = {
        @pure def getFirstAvailable(s: ISZ[Z]): Z = {
          if (opMax <= 0) {
            var min: Z = 0
            for (i <- 1 until s.size) {
              if (min > s(i)) {
                min = i
              }
            }
            return min
          }
          for (j <- s.indices) {
            if (s(j) < opMax) {
              return j
            }
          }
          return s.size
        }
        val bam = binopAllocMap
        val ia = indexingAlloc
        for (entry <- ic.ipMap.entries) {
          val (ipe, n) = entry
          def binop(t: AST.Typed, op: AST.IR.Exp.Binary.Op.Type): Unit = {
            val key = (anvil.isSigned(t), op)
            var alloc = getFirstAvailable(bam.get(key).getOrElseEager(ISZ()))
            alloc = alloc + n
            if (opMax <= 0) {
              alloc = alloc % max.binopAllocSizeMap.get(key).get
            }
            var s = binopAllocMap.get(key).getOrElseEager(ISZ())
            while (s.size <= alloc) {
              s = s :+ 0
            }
            r = r + ipe ~> alloc
            binopAllocMap = binopAllocMap + key ~> s(alloc ~> (s(alloc) + 1))
          }
          ipe.ast match {
            case e: AST.IR.Exp.Binary =>
              val t: AST.Typed = if (anvil.isScalar(e.tipe)) e.left.tipe else anvil.spType
              binop(t, e.op)
            case AST.IR.Exp.Intrinsic(_: Intrinsic.Indexing) =>
              var alloc = getFirstAvailable(ia)
              alloc = alloc + n
              if (opMax <= 0) {
                alloc = alloc % max.indexingAllocSize
              }
              var s = indexingAlloc
              while (s.size <= alloc) {
                s = s :+ 0
              }
              r = r + ipe ~> alloc
              indexingAlloc = s(alloc ~> (s(alloc) + 1))
            case e: AST.IR.Exp.Int => binop(e.tipe, if (e.value < 0) AST.IR.Exp.Binary.Op.Sub else AST.IR.Exp.Binary.Op.Add)
            case e => binop(e.tipe, AST.IR.Exp.Binary.Op.Add)
          }
        }
      }

      val ic = IpCounter(anvil, HashSMap.empty, HashSMap.empty, 0)
      ic.transform_langastIRBasicBlock(b)
      allocate(ic)

    }
    return IpAlloc(r, HashSMap ++ (for (e <- binopAllocMap.entries) yield (e._1, e._2.size)), indexingAlloc.size)
  }

  val nonTempGlobals: HashSet[QName] = HashSet.empty[QName] + memName + memTypeName + memSizeName + testNumName +
    testNumNamePad

  @strictpure def isTempGlobal(anvil: Anvil, tipe: AST.Typed, name: ISZ[String]): B =
    anvil.config.tempGlobal && anvil.isScalar(tipe) && !nonTempGlobals.contains(name)

  @strictpure def binopSignGlobalName(op: AST.IR.Exp.Binary.Op.Type, isSigned: B): ISZ[String] =
    ISZ("org", "sireum", "anvil", s"${'$'}$op${if (isSigned) "S" else "U" }")

  @pure def isIntrinsicGlobalVar(name: QName): B = {
    if (name.size <= intrinsicName.size) {
      return false
    }
    for (i <- 0 until intrinsicName.size if name(i) != intrinsicName(i)) {
      return false
    }
    return true
  }
}