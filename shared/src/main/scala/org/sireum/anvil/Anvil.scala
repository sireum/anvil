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
import org.sireum.alir.TypeSpecializer
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Reporter
import org.sireum.U32._

object Anvil {

  @datatype class Config(val projectName: String,
                         val defaultBitWidth: Z,
                         val maxStringSize: Z,
                         val maxArraySize: Z,
                         val customArraySizes: HashMap[AST.Typed, Z],
                         val customConstants: HashMap[QName, AST.Exp])

  object Config {
    @strictpure def empty(projectName: String): Config =
      Config(projectName, 64, 100, 100, HashMap.empty, HashMap.empty)
  }

  @record class TempCollector(var r: HashSSet[Z]) extends AST.MIRTransformer {
    override def postIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      r = r + o.n
      return MNone()
    }
  }

  @record class GroundOffsetTransformer(val localOffsetMap: HashMap[String, Z],
                                        var tempExpMap: HashMap[Z, AST.IR.Exp]) extends AST.MIRTransformer {
    override def postIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      tempExpMap.get(o.n) match {
        case Some(e) =>
          tempExpMap = tempExpMap -- ISZ(o.n)
          return MSome(e)
        case _ => halt(s"Infeasible: ${o.n}, $tempExpMap")
      }
    }
  }

  val kind: String = "Anvil"
  val returnLocalId: String = "$ret"
  val resultLocalId: String = "$res"

  def synthesize(fresh: lang.IRTranslator.Fresh, th: TypeHierarchy, owner: QName, id: String, config: Config, reporter: Reporter): HashSMap[ISZ[String], ST] = {
    val tsr = TypeSpecializer.specialize(th, ISZ(TypeSpecializer.EntryPoint.Method(owner :+ id)), HashMap.empty,
      reporter)
    if (tsr.extMethods.nonEmpty) {
      reporter.error(None(), kind, s"@ext methods are not supported")
    }
    if (reporter.hasError) {
      return HashSMap.empty
    }
    return Anvil(th, tsr, owner, id, config).synthesize(fresh, reporter)
  }
}

import Anvil._

@datatype class Anvil(val th: TypeHierarchy,
                      val tsr: TypeSpecializer.Result,
                      val owner: QName,
                      val id: String,
                      val config: Config) {

  val spType: AST.Typed =
    if (config.defaultBitWidth == 8) {
      AST.Typed.s8
    } else if (config.defaultBitWidth == 16) {
      AST.Typed.s16
    } else if (config.defaultBitWidth == 32) {
      AST.Typed.s32
    } else if (config.defaultBitWidth == 64) {
      AST.Typed.s64
    } else {
      halt(s"Infeasible: ${config.defaultBitWidth}")
    }
  val cpType: AST.Typed = AST.Typed.u64

  def synthesize(fresh: lang.IRTranslator.Fresh, reporter: Reporter): HashSMap[ISZ[String], ST] = {
    val threeAddressCode = T

    val irt = lang.IRTranslator(threeAddressCode = T, th = tsr.typeHierarchy, fresh = fresh)

    val mp: (AST.IR.MethodContext, AST.IR.Program) = {
      var globals = ISZ[AST.IR.Global]()
      var procedures = ISZ[AST.IR.Procedure]()

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
        val objInitId = "<objinit>"
        val name = owner :+ objInitId
        val objInit = irt.translateMethodH(F, None(), owner, objInitId, ISZ(), ISZ(),
          AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.unit), pos, Some(AST.Body(stmts, ISZ())))
        var body = objInit.body.asInstanceOf[AST.IR.Body.Block]
        body = body(block = body.block(stmts = AST.IR.Stmt.Block(ISZ(
          AST.IR.Stmt.If(AST.IR.Exp.GlobalVarRef(name, AST.Typed.b, pos),
            AST.IR.Stmt.Block(ISZ(AST.IR.Stmt.Return(None(), pos)), pos),
            AST.IR.Stmt.Block(ISZ(), pos), pos),
          AST.IR.Stmt.Assign.Global(F, name, AST.Typed.b, AST.IR.Exp.Bool(T, pos), pos)
        ), pos) +: body.block.stmts))
        val p = objInit(body = irt.toBasic(body, objInit.pos))
        procedures = procedures :+ p
      }
      var mainOpt = Option.none[AST.IR.Procedure]()
      for (ms <- tsr.methods.values; m <- ms.elements) {
        val p = irt.translateMethod(T, None(), m.info.owner, m.info.ast)
        procedures = procedures :+ p
        if (m.info.owner == owner && m.info.ast.sig.id.value == id) {
          mainOpt = Some(p)
        }
      }
      (mainOpt.get.context, AST.IR.Program(threeAddressCode, globals, procedures))
    }

    val mainContext = mp._1
    var program = mp._2

    var r = HashSMap.empty[ISZ[String], ST]
    r = r + ISZ("ir", "1-program.sir") ~> program.prettyST

    program = transformProgram(irt.fresh, program)
    r = r + ISZ("ir", "2-program-transformed.sir") ~> program.prettyST

    var procedureMap = HashSMap.empty[AST.IR.MethodContext, AST.IR.Procedure]
    var procedureSizeMap = HashMap.empty[AST.IR.MethodContext, Z]
    var callResultOffsetMap = HashMap.empty[String, Z]
    program = {
      for (p <- program.procedures) {
        val (maxOffset, p2, m) = transformOffset(p)
        callResultOffsetMap = callResultOffsetMap ++ m.entries
        procedureMap = procedureMap + p2.context ~> p2
        procedureSizeMap = procedureSizeMap + p2.context ~> maxOffset
      }
      program(procedures = procedureMap.values)
    }
    r = r + ISZ("ir", "3-program-offset.sir") ~> program.prettyST

    program = {
      val main = procedureMap.get(mainContext).get
      program(procedures = ISZ(main(body = main.body.asInstanceOf[AST.IR.Body.Basic](blocks =
        mergeProcedures(main, procedureMap, procedureSizeMap, callResultOffsetMap)))))
    }
    r = r + ISZ("ir", "4-program-merged.sir") ~> program.prettyST

    r = r ++ HwSynthesizer(this).printProgram(program).entries

    return r
  }

  def transformApplyResult(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]

    var m = HashMap.empty[Z, AST.IR.Stmt.Ground]
    var bm = HashMap.empty[Z, AST.IR.Stmt.Ground]
    var em = HashMap.empty[Z, AST.IR.Stmt.Ground]
    for (b <- body.blocks; g <- b.grounds) {
      g match {
        case g: AST.IR.Stmt.Expr if g.exp.methodType.ret != AST.Typed.unit =>
          em = em + b.label ~> AST.IR.Stmt.Decl(F, T, p.context, ISZ(
            AST.IR.Stmt.Decl.Local(callResultId(g.exp.id, g.exp.pos), g.exp.tipe)), g.pos)
          bm = bm + b.jump.asInstanceOf[AST.IR.Jump.Goto].label ~> AST.IR.Stmt.Decl(T, T, p.context, ISZ(
            AST.IR.Stmt.Decl.Local(callResultId(g.exp.id, g.exp.pos), g.exp.tipe)), g.pos)
        case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
          val e = g.rhs.asInstanceOf[AST.IR.Exp.Apply]
          em = em + b.label ~> AST.IR.Stmt.Decl(F, T, p.context, ISZ(
            AST.IR.Stmt.Decl.Local(callResultId(e.id, e.pos), e.tipe)), g.pos)
          m = m + g.lhs ~> AST.IR.Stmt.Decl(T, T, p.context, ISZ(
            AST.IR.Stmt.Decl.Local(callResultId(e.id, e.pos), e.tipe)), g.pos)
        case _ =>
      }
    }
    var newBlocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var newGrounds = ISZ[AST.IR.Stmt.Ground]()
      bm.get(b.label) match {
        case Some(g) => newGrounds = newGrounds :+ g
        case _ =>
      }
      for (g <- b.grounds) {
        newGrounds = newGrounds :+ g
        val tc = TempCollector(HashSSet.empty)
        tc.transformIRStmtGround(g)
        for (n <- tc.r.elements) {
          m.get(n) match {
            case Some(g) => newGrounds = newGrounds :+ g
            case _ =>
          }
        }
      }
      b.jump match {
        case j: AST.IR.Jump.Goto =>
          em.get(j.label) match {
            case Some(g) => newGrounds = newGrounds :+ g
            case _ =>
          }
        case _ =>
      }
      newBlocks = newBlocks :+ b(grounds = newGrounds)
    }
    return p(body = body(blocks = newBlocks))
  }

  def transformProgram(fresh: lang.IRTranslator.Fresh, program: AST.IR.Program): AST.IR.Program = {
    @pure def transform(p: AST.IR.Procedure): AST.IR.Procedure = {
      var r = transformApplyResult(p)
      return r
    }
    return program(procedures = ops.ISZOps(program.procedures).mParMap(transform _))
  }

  @memoize def callResultId(id: String, pos: message.Position): String = {
    return s"$id$resultLocalId@[${pos.beginLine},${pos.endLine}].${sha3(pos.string)}"
  }

  def mergeProcedures(main: AST.IR.Procedure,
                      procedureMap: HashSMap[AST.IR.MethodContext, AST.IR.Procedure],
                      procedureSizeMap: HashMap[AST.IR.MethodContext, Z],
                      callResultOffsetMap: HashMap[String, Z]): ISZ[AST.IR.BasicBlock] = {
    var seen = HashSet.empty[AST.IR.MethodContext]
    var work = ISZ[AST.IR.Procedure](main)
    var mergedBlocks = ISZ[AST.IR.BasicBlock]()
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.Procedure]()
      for (p <- work) {
        seen = seen + p.context
        var addBeginningMap = HashSMap.empty[Z, ISZ[AST.IR.Stmt.Ground]]
        var blocks = ISZ[AST.IR.BasicBlock]()
        for (b <- p.body.asInstanceOf[AST.IR.Body.Basic].blocks) {
          def processInvoke(g: AST.IR.Stmt.Ground, lhsOpt: Option[Z], e: AST.IR.Exp.Apply, label: Z): Unit = {
            val mc = AST.IR.MethodContext(e.isInObject, e.owner, e.id, e.methodType)
            val called = procedureMap.get(mc).get
            if (!seen.contains(mc)) {
              next = next :+ called
            }
            val spAdd = procedureSizeMap.get(p.context).get
            var grounds = ISZ[AST.IR.Stmt.Ground](
              AST.IR.Stmt.Intrinsic(Intrinsic.StackPointerInc(spAdd, e.pos))
            )
            var locals = ISZ[AST.IR.Stmt.Decl.Local](
              AST.IR.Stmt.Decl.Local(returnLocalId, cpType)
            )
            if (p.tipe.ret != AST.Typed.unit) {
              locals = locals :+ AST.IR.Stmt.Decl.Local(resultLocalId, spType)
            }
            for (param <- ops.ISZOps(called.paramNames).zip(called.tipe.args)) {
              locals = locals :+ AST.IR.Stmt.Decl.Local(param._1, param._2)
            }
            grounds = grounds :+ AST.IR.Stmt.Decl(F, T, called.context, locals, e.pos)
            grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
              AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
              T, typeByteSize(cpType), AST.IR.Exp.Int(cpType, label, e.pos), st"$returnLocalId@0 = $label", cpType, e.pos
            ))
            if (p.tipe.ret != AST.Typed.unit) {
              val n = callResultOffsetMap.get(callResultId(e.id, e.pos)).get - spAdd
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeByteSize(cpType), e.pos), e.pos),
                T, typeByteSize(spType),
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, n, e.pos), e.pos),
                st"$resultLocalId@${typeByteSize(cpType)} = $n", spType, e.pos))
            }
            var paramOffset: Z = typeByteSize(cpType) + typeByteSize(spType)
            for (param <- ops.ISZOps(ops.ISZOps(called.paramNames).zip(mc.t.args)).zip(e.args)) {
              val ((pid, pt), parg) = param
              val t: AST.Typed = if (isScalar(pt)) pt else spType
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, paramOffset, e.pos), e.pos),
                T, typeByteSize(t), parg, st"$pid = ${parg.prettyST}", t, parg.pos))
              paramOffset = paramOffset + typeByteSize(pt)
            }
            var bgrounds = ISZ[AST.IR.Stmt.Ground](
              AST.IR.Stmt.Decl(T, T, called.context, for (i <- locals.size - 1 to 0 by -1) yield locals(i), e.pos),
              AST.IR.Stmt.Intrinsic(Intrinsic.StackPointerInc(-spAdd, e.pos))
            )
            lhsOpt match {
              case Some(lhs) =>
                bgrounds = AST.IR.Stmt.Intrinsic(Intrinsic.Load(lhs, AST.IR.Exp.Int(cpType, 0, g.pos), F,
                  typeByteSize(cpType), st"$$$lhs = $returnLocalId", spType, g.pos)) +: bgrounds
              case _ =>
            }
            addBeginningMap = addBeginningMap + label ~> bgrounds
            blocks = blocks :+ b(grounds = grounds,
              jump = AST.IR.Jump.Goto(called.body.asInstanceOf[AST.IR.Body.Basic].blocks(0).label, e.pos))
          }

          b.jump match {
            case j: AST.IR.Jump.Goto if b.grounds.size == 1 =>
              b.grounds(0) match {
                case g: AST.IR.Stmt.Expr => processInvoke(g, None(), g.exp, j.label)
                case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
                  processInvoke(g, Some(g.lhs), g.rhs.asInstanceOf[AST.IR.Exp.Apply], j.label)
                case _ =>
              }
            case j: AST.IR.Jump.Return =>
              var addGrounds = ISZ[AST.IR.Stmt.Ground]()
              j.expOpt match {
                case Some(exp) =>
                  if (isScalar(exp.tipe)) {
                    addGrounds = addGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
                      AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, exp.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeByteSize(cpType), exp.pos), exp.pos),
                      T, typeByteSize(spType), exp, st"$resultLocalId = ${exp.prettyST}", spType, exp.pos))
                  } else {
                    addGrounds = addGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(
                      AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, exp.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeByteSize(cpType), exp.pos), exp.pos),
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
    val last: AST.IR.BasicBlock = {
      val expOpt: Option[AST.IR.Exp] =
        if (main.tipe.ret == AST.Typed.unit) None()
        else Some(AST.IR.Exp.Int(spType, typeByteSize(cpType), main.pos))
      AST.IR.BasicBlock(0, ISZ(), AST.IR.Jump.Return(expOpt, main.pos))
    }
    return mergedBlocks :+ last
  }

  def transformOffset(proc: AST.IR.Procedure): (Z, AST.IR.Procedure, HashMap[String, Z]) = {
    val body = proc.body.asInstanceOf[AST.IR.Body.Basic]
    val blocks = body.blocks
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- blocks) yield (b.label, b))
    var blockLocalOffsetMap = HashMap.empty[Z, (Z, HashMap[String, Z])]
    var maxOffset: Z = typeByteSize(cpType) + typeByteSize(spType)
    var callResultIdOffsetMap = HashMap.empty[String, Z]
    var tempExpMap = HashMap.empty[Z, AST.IR.Exp]
    val isMain = proc.context.owner == owner && proc.context.id == id
    if (isMain) {
      maxOffset = maxOffset + typeByteSize(proc.tipe.ret)
    }
    {
      var m = HashMap.empty[String, Z]
      var offset: Z = maxOffset
      for (param <- ops.ISZOps(proc.paramNames).zip(proc.tipe.args)) {
        val (id, t) = param
        m = m + id ~> offset
        offset = offset + (if (isScalar(t)) typeByteSize(t) else typeByteSize(spType) + (if (isMain) typeByteSize(t) else 0))
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
              val mult: Z = if (g.undecl) -1 else 1
              for (l <- g.locals) {
                if (g.undecl) {
                  m = m -- ISZ(l.id)
                } else {
                  m = m + l.id ~> offset
                }
                offset = offset + (if (isScalar(l.tipe)) typeByteSize(l.tipe) else typeByteSize(spType)) * mult
              }
              if (maxOffset < offset) {
                maxOffset = offset
              }
              grounds = grounds :+ g
            case _ =>
              g match {
                case AST.IR.Stmt.Assign.Local(copy, _, lhs, t, rhs, pos) =>
                  val localOffset = m.get(lhs).get
                  if (copy) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(
                      AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, rhs.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, rhs.pos), rhs.pos),
                      typeByteSize(t), typeByteSize(rhs.tipe), rhs, st"$lhs = ${rhs.prettyST}", t, rhs.tipe, pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
                      AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, rhs.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, rhs.pos), rhs.pos),
                      T, typeByteSize(t), rhs, st"$lhs = ${rhs.prettyST}", t, pos))
                  }
                case AST.IR.Stmt.Assign.Temp(n, rhs, pos) =>
                  def rest(): Unit = {
                    val got = GroundOffsetTransformer(m, tempExpMap)
                    val newRhs = got.transformIRExp(rhs).getOrElse(rhs)
                    tempExpMap = got.tempExpMap
                    val temp = tempExpMap.size
                    tempExpMap = tempExpMap + n ~> AST.IR.Exp.Temp(temp, rhs.tipe, pos)
                    grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, newRhs, pos)
                  }
                  rhs match {
                    case rhs: AST.IR.Exp.Int => tempExpMap = tempExpMap + n ~> rhs
                    case rhs: AST.IR.Exp.Bool => tempExpMap = tempExpMap + n ~> rhs
                    case rhs: AST.IR.Exp.F32 => tempExpMap = tempExpMap + n ~> rhs
                    case rhs: AST.IR.Exp.F64 => tempExpMap = tempExpMap + n ~> rhs
                    case rhs: AST.IR.Exp.R => tempExpMap = tempExpMap + n ~> rhs
                    case rhs: AST.IR.Exp.String => tempExpMap = tempExpMap + n ~> rhs
                    case rhs: AST.IR.Exp.EnumElementRef => halt(s"TODO: $rhs")
                    case rhs: AST.IR.Exp.Temp =>
                      tempExpMap = tempExpMap + n ~> tempExpMap.get(rhs.n).get
                      tempExpMap = tempExpMap -- ISZ(rhs.n)
                    case rhs: AST.IR.Exp.LocalVarRef =>
                      val localOffset = m.get(rhs.id).get
                      val temp = tempExpMap.size
                      tempExpMap = tempExpMap + n ~> AST.IR.Exp.Temp(temp, rhs.tipe, pos)
                      val t: AST.Typed = if (isScalar(rhs.tipe)) rhs.tipe else spType
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Load(temp,
                        AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, rhs.pos)),
                          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, rhs.pos), rhs.pos),
                        isSigned(t), typeByteSize(t), rhs.prettyST, t, rhs.pos))
                    case _: AST.IR.Exp.FieldVarRef => rest()
                    case _: AST.IR.Exp.GlobalVarRef => rest()
                    case _: AST.IR.Exp.Indexing => rest()
                    case _: AST.IR.Exp.Select => rest()
                    case _: AST.IR.Exp.Apply => rest()
                    case _: AST.IR.Exp.Binary => rest()
                    case rhs: AST.IR.Exp.Construct =>
                      val constructOffset = offset
                      val rhsSize = typeByteSize(rhs.tipe)
                      offset = offset + rhsSize
                      val got = GroundOffsetTransformer(m, tempExpMap)
                      val newRhs = got.transformIRExp(rhs).getOrElse(rhs)
                      tempExpMap = got.tempExpMap
                      val temp = tempExpMap.size
                      tempExpMap = tempExpMap + n ~> AST.IR.Exp.Temp(temp, rhs.tipe, pos)
                      grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, newRhs, pos)
                      halt("TODO")
                    case _: AST.IR.Exp.Type => rest()
                    case _: AST.IR.Exp.Unary => rest()
                    case _: AST.IR.Exp.If => halt(s"Infeasible: $rhs")
                    case _: AST.IR.Exp.Intrinsic => halt(s"Infeasible: $rhs")
                  }
                case _ =>
                  val got = GroundOffsetTransformer(m, tempExpMap)
                  grounds = grounds :+ got.transformIRStmtGround(g).getOrElse(g)
                  tempExpMap = got.tempExpMap
              }
              g match {
                case g: AST.IR.Stmt.Expr if g.exp.methodType.ret != AST.Typed.unit =>
                  val id = callResultId(g.exp.id, g.exp.pos)
                  callResultIdOffsetMap = callResultIdOffsetMap + id ~> m.get(id).get
                  tempExpMap = tempExpMap -- (for (arg <- g.exp.args) yield arg.asInstanceOf[AST.IR.Exp.Temp].n)
                case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
                  val e = g.rhs.asInstanceOf[AST.IR.Exp.Apply]
                  val id = callResultId(e.id, e.pos)
                  callResultIdOffsetMap = callResultIdOffsetMap + id ~> m.get(id).get
                case _ =>
              }
          }
        }
        val jump: AST.IR.Jump = {
          val got = GroundOffsetTransformer(m, tempExpMap)
          val j = got.transformIRJump(b.jump).getOrElse(b.jump)
          tempExpMap = got.tempExpMap
          j
        }
        blockMap = blockMap + b.label ~> b(grounds = grounds, jump = jump)
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

  @memoize def getClassFields(t: AST.Typed.Name): HashSMap[String, AST.Typed] = {
    val info = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
    val sm = TypeChecker.buildTypeSubstMap(t.ids, None(), info.ast.typeParams, t.args, message.Reporter.create).get
    var r = HashSMap.empty[String, AST.Typed]
    for (v <- info.vars.values) {
      r = r + v.ast.id.value ~> v.typedOpt.get.subst(sm)
    }
    return r
  }

  @memoize def getMaxArraySize(t: AST.Typed.Name): Z = {
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
      case t: AST.Typed.Name =>
        if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
          var r: Z = 4 // type sha
          r = r + 4 // .size
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
                var r: Z = 4 // type sha
                for (ft <- getClassFields(t).values) {
                  r = r + typeByteSize(ft)
                }
                return r
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

  def sha3(s: String): U32 = {
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
      case _ => return isSubZ(t)
    }
    return T
  }

  @memoize def isSigned(t: AST.Typed): B = {
    t match {
      case AST.Typed.b => return F
      case AST.Typed.c => return F
      case AST.Typed.z => return T
      case AST.Typed.f32 => return T
      case AST.Typed.f64 => return T
      case AST.Typed.r => return T
      case _ => return subZOpt(t).get.ast.isSigned
    }
  }

  @memoize def shouldCopy(t: AST.Typed): B = {
    if (isScalar(t)) {
      return F
    }
    t match {
      case t: AST.Typed.Name =>
        t.ids match {
          case AST.Typed.msName => return T
          case AST.Typed.isName =>
          case _ =>
        }
        th.typeMap.get(t.ids) match {
          case Some(info: TypeInfo.Adt) => return !info.ast.isDatatype
          case Some(info: TypeInfo.Sig) => return !info.ast.isImmutable
          case _ =>
        }
      case _ =>
    }
    return F
  }
}