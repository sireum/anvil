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
import org.sireum.lang.ast.{IR, MIRTransformer}

object Anvil {

  @datatype class Config(val projectName: String,
                         val memory: Z,
                         val defaultBitWidth: Z,
                         val maxStringSize: Z,
                         val maxArraySize: Z,
                         val customArraySizes: HashMap[AST.Typed, Z],
                         val customConstants: HashMap[QName, AST.Exp])

  object Config {
    @strictpure def empty(projectName: String): Config =
      Config(projectName, 512 * 1024, 64, 100, 100, HashMap.empty, HashMap.empty)
  }

  @record class TempCollector(var r: HashSSet[Z]) extends AST.MIRTransformer {
    override def postIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      r = r + o.n
      return MNone()
    }

    override def postIRExpIntrinsicType(o: AST.IR.Exp.Intrinsic.Type): MOption[AST.IR.Exp.Intrinsic.Type] = {
      o match {
        case _: Intrinsic.StackPointer =>
        case _ =>
      }
      return MNone()
    }

    override def postIRStmtIntrinsicType(o: AST.IR.Stmt.Intrinsic.Type): MOption[AST.IR.Stmt.Intrinsic.Type] = {
      o match {
        case o: Intrinsic.Copy =>
          transformIRExp(o.lhsOffset)
          transformIRExp(o.rhs)
        case o: Intrinsic.StoreScalar =>
          transformIRExp(o.lhsOffset)
          transformIRExp(o.rhs)
        case o: Intrinsic.Load =>
          transformIRExp(o.rhsOffset)
        case _: Intrinsic.Decl =>
        case _: Intrinsic.StackPointerInc =>
      }
      return MNone()
    }
  }

  @datatype class GlobalInfo(val isScalar: B,
                             val offset: Z,
                             val size: Z,
                             val dataSize: Z,
                             val tipe: AST.Typed,
                             val pos: message.Position)

  @record class TempExpSubstitutor(val substMap: HashMap[Z, AST.IR.Exp]) extends AST.MIRTransformer {
    override def postIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      substMap.get(o.n) match {
        case Some(e) => return MSome(e)
        case _ =>
          halt(s"Infeasible: ${o.n}, $substMap")
      }
    }
  }

  @record class TempRenumberer(val map: HashMap[Z, Z]) extends AST.MIRTransformer {
    override def postIRExpTemp(o: AST.IR.Exp.Temp): MOption[AST.IR.Exp] = {
      map.get(o.n) match {
        case Some(n) => return MSome(o(n = n))
        case _ =>
          halt(s"Infeasible: ${o.n}, $map")
      }
    }

    override def postIRStmtAssignTemp(o: AST.IR.Stmt.Assign.Temp): MOption[AST.IR.Stmt.Assign] = {
      map.get(o.lhs) match {
        case Some(n) => return MSome(o(lhs = n))
        case _ =>
          halt(s"Infeasible: ${o.lhs}, $map")
      }
    }
  }

  @record class AccessPathCollector(var accessPaths: HashSet[ISZ[String]]) extends AST.MIRTransformer {
    override def preIRExp(o: IR.Exp): AST.MIRTransformer.PreResult[IR.Exp] = {
      accessPaths = accessPaths ++ AccessPathCollector.computeAccessPathsExp(o).elements
      return AST.MIRTransformer.PreResult(continu = F, resultOpt = MNone())
    }
  }

  object AccessPathCollector {
    @strictpure def computeAccessPath(e: AST.IR.Exp, suffix: ISZ[String]): ISZ[String] = e match {
      case e: AST.IR.Exp.FieldVarRef => computeAccessPath(e.receiver, e.id +: suffix)
      case e: AST.IR.Exp.Indexing => computeAccessPath(e.exp, ISZ())
      case e: AST.IR.Exp.LocalVarRef => st"${(e.context.owner :+ e.context.id :+ e.id, ".")}".render +: suffix
      case e: AST.IR.Exp.GlobalVarRef => st"${(e.name, ".")}".render +: suffix
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
          case _: AST.IR.Exp.Intrinsic => halt("Infeasible")
          case _: AST.IR.Exp.If => halt("Infeasible")
        }
      }
      rec(exp)
      return r
    }
  }

  @record class CPSubstitutor(var cpSubstMap: HashMap[Z, Z]) extends AST.MIRTransformer {
    override def postIRBasicBlock(o: AST.IR.BasicBlock): MOption[AST.IR.BasicBlock] = {
      return MSome(o(label = cpSubstMap.get(o.label).get))
    }

    override def postIRJumpIf(o: AST.IR.Jump.If): MOption[AST.IR.Jump] = {
      return MSome(o(thenLabel = cpSubstMap.get(o.thenLabel).get, elseLabel = cpSubstMap.get(o.elseLabel).get))
    }

    override def postIRJumpGoto(o: AST.IR.Jump.Goto): MOption[AST.IR.Jump] = {
      return MSome(o(label = cpSubstMap.get(o.label).get))
    }

    override def postIRStmtIntrinsic(o: AST.IR.Stmt.Intrinsic): MOption[AST.IR.Stmt.Ground] = {
      o.intrinsic match {
        case in@Intrinsic.StoreScalar(AST.IR.Exp.Intrinsic(_: Intrinsic.StackPointer), _, _, i@AST.IR.Exp.Int(_, cp, _), _, _, _) =>
          return MSome(o(intrinsic = in(rhs = i(value = cpSubstMap.get(cp).get))))
        case _ =>
      }
      return MNone()
    }
  }

  val kind: String = "Anvil"
  val returnLocalId: String = "$ret"
  val resultLocalId: String = "$res"
  val typeShaSize: Z = 4

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

    val mq: (AST.IR.MethodContext, AST.IR.Program, Z, HashSMap[ISZ[String], GlobalInfo]) = {
      var globals = ISZ[AST.IR.Global]()
      var procedures = ISZ[AST.IR.Procedure]()
      var globalSize: Z = 0

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

    var r = HashSMap.empty[ISZ[String], ST]
    r = r + ISZ("ir", "1-program.sir") ~> program.prettyST

    program = transformProgram(irt.fresh, program)
    r = r + ISZ("ir", "2-program-transformed.sir") ~> program.prettyST

    var procedureMap = HashSMap.empty[AST.IR.MethodContext, AST.IR.Procedure]
    var procedureSizeMap = HashMap.empty[AST.IR.MethodContext, Z]
    var callResultOffsetMap = HashMap.empty[String, Z]
    program = {
      for (p <- program.procedures) {
        val (maxOffset, p2, m) = transformOffset(globalMap, p)
        callResultOffsetMap = callResultOffsetMap ++ m.entries
        procedureMap = procedureMap + p2.context ~> p2
        procedureSizeMap = procedureSizeMap + p2.context ~> maxOffset
      }
      program(procedures = procedureMap.values)
    }
    r = r + ISZ("ir", "3-program-offset.sir") ~> program.prettyST

    val main = procedureMap.get(mainContext).get
    program = {
      val p = main(body = main.body.asInstanceOf[AST.IR.Body.Basic](blocks =
        mergeProcedures(main, procedureMap, procedureSizeMap, callResultOffsetMap)))
      program(procedures = ISZ(p))
    }
    r = r + ISZ("ir", "4-program-merged.sir") ~> program.prettyST

    program = {
      @strictpure def isSPInc(g: AST.IR.Stmt.Ground): B = g match {
        case g: AST.IR.Stmt.Intrinsic => g.intrinsic.isInstanceOf[Intrinsic.StackPointerInc]
        case _ => F
      }
      var p = program.procedures(0)
      p = transformSplitTest(fresh, p, isSPInc _)
      p = transformCP(p)
      program(procedures = ISZ(p))
    }

    val maxRegisters: Z = {
      val tc = TempCollector(HashSSet.empty)
      tc.transformIRProgram(program)
      tc.r.elements.size
    }
    val header: ST = {
      var offset: Z = typeByteSize(cpType)
      val resOpt: Option[ST] =
        if (main.tipe.ret != AST.Typed.unit) {
          offset = offset + typeByteSize(spType) + typeByteSize(main.tipe.ret)
          Some(
            st"- $$res (*(SP + ${typeByteSize(cpType)})) = ${globalSize + typeByteSize(cpType) + typeByteSize(spType)} (signed, size = ${typeByteSize(spType)}, data-size = ${typeByteSize(main.tipe.ret)})")
        } else {
          None()
        }
      var paramsST = ISZ[ST]()
      for (param <- ops.ISZOps(main.paramNames).zip(main.tipe.args)) {
        if (!isScalar(param._2)) {
          paramsST = paramsST :+ st"- for parameter ${param._1}: *(SP + $offset) = ${globalSize + offset + typeByteSize(spType)} (signed, size = ${typeByteSize(spType)}, data-size = ${typeByteSize(param._2)})"
          offset = offset + typeByteSize(spType) + typeByteSize(param._2)
        } else {
          offset = offset + typeByteSize(param._2)
        }
      }
      st"""/*
          |   Note that globalSize = $globalSize, and initially:
          |   - register SP (stack pointer) = $globalSize (signed, byte size = ${typeByteSize(spType)})
          |   - register CP (code pointer) = 1 (unsigned, byte size = ${typeByteSize(cpType)})
          |   - max registers (beside SP and CP) = $maxRegisters
          |   - $$ret (*SP) = 0 (signed, byte size = ${typeByteSize(cpType)})
          |   $resOpt
          |   ${(paramsST, "\n")}
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
          |   decl/undecl and alloc/dealloc are the same except alloc/dealloc may have data-size for
          |   class/trait/IS/MS types.
          | */"""

    }

    r = r + ISZ("ir", "5-program-reordered.sir") ~>
      st"""$header
          |${program.prettyST}"""

    r = r ++ HwSynthesizer(this).printProcedure(id, program.procedures(0), globalSize, maxRegisters).entries

    return r
  }

  def transformEmptyBlock(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    for (b <- body.blocks) {
      var map = HashMap.empty[Z, Z]
      for (target <- b.jump.targets) {
        val b2 = blockMap.get(target).get
        if (b2.grounds.isEmpty) {
          b2.jump match {
            case j: AST.IR.Jump.Goto => map = map + target ~> j.label
            case _ =>
          }
        }
      }
      if (map.nonEmpty) {
        blockMap = blockMap -- map.keys
        val jump: AST.IR.Jump = b.jump match {
          case j: AST.IR.Jump.If => j(thenLabel = map.get(j.thenLabel).getOrElse(j.thenLabel),
            elseLabel = map.get(j.elseLabel).getOrElse(j.elseLabel))
          case j: AST.IR.Jump.Goto => j(label = map.get(j.label).get)
          case j => j
        }
        blockMap = blockMap + b.label ~> b(jump = jump)
      }
    }
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
    var cpSubstMap = HashMap.empty[Z, Z] + 0 ~> 0 + 1 ~> 1
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
      if (b.label >= 2) {
        cpSubstMap = cpSubstMap + b.label ~> cpSubstMap.size
      }
    }
    return CPSubstitutor(cpSubstMap).transformIRProcedure(p(body = body(blocks = blocks))).getOrElse(p)
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
              substMap = substMap + g.lhs ~> TempExpSubstitutor(substMap).transformIRExp(g.rhs).getOrElse(g.rhs)
            case g: AST.IR.Stmt.Assign.Local => writeAccessPaths = writeAccessPaths +
              ISZ(st"${(g.context.owner :+ g.context.id :+ g.lhs, ".")}".render)
            case g: AST.IR.Stmt.Assign.Field =>
              writeAccessPaths = writeAccessPaths + AccessPathCollector.computeAccessPath(g.receiver, ISZ(g.id))
            case g: AST.IR.Stmt.Assign.Index =>
              writeAccessPaths = writeAccessPaths + AccessPathCollector.computeAccessPath(g.receiver, ISZ())
            case g: AST.IR.Stmt.Assign.Global => writeAccessPaths = writeAccessPaths + ISZ(st"${(g.name, ".")}".render)
            case _ =>
          }
        }

        def computeReads(g: AST.IR.Stmt.Ground): Unit = {
          val rc = AccessPathCollector(readAccessPaths)
          g match {
            case _: AST.IR.Stmt.Assign.Temp =>
            case g: AST.IR.Stmt.Assign => rc.transformIRExp(g.rhs)
            case _ => rc.transformIRStmtGround(g)
          }
          readAccessPaths = rc.accessPaths
        }

        var i = 0
        while (i < b.grounds.size) {
          val ground = b.grounds(i)
          val g = TempExpSubstitutor(substMap).transformIRStmtGround(ground).getOrElse(ground)
          computeWrites(g)
          computeReads(g)
          if (areReadWritePathsDisallowed(readAccessPaths, writeAccessPaths)) {
            introBlock(g.pos)
            computeWrites(g)
            computeReads(g)
            if (areReadWritePathsDisallowed(readAccessPaths, writeAccessPaths)) {
              grounds = grounds :+ ground
              introBlock(g.pos)
              i = i + 1
            }
            readAccessPaths = HashSet.empty[ISZ[String]]
            writeAccessPaths = HashSet.empty[ISZ[String]]
          } else {
            grounds = grounds :+ ground
            i = i + 1
          }
        }
        b.jump match {
          case j: AST.IR.Jump.If =>
            val rc = AccessPathCollector(readAccessPaths)
            rc.transformIRExp(TempExpSubstitutor(substMap).transformIRExp(j.cond).getOrElse(j.cond))
            readAccessPaths = rc.accessPaths
            if (readAccessPaths.intersect(writeAccessPaths).nonEmpty) {
              introBlock(j.pos)
            }
            blocks = blocks :+ block(grounds = grounds, jump = j)
          case _ =>
            blocks = blocks :+ block(grounds = grounds, jump = b.jump)
        }
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
    return p(body = body(blocks = blocks))
  }

  def transformApplyResult(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
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
          case _ =>
            grounds = grounds :+ g
            val tc = TempCollector(HashSSet.empty)
            tc.transformIRStmtGround(g)
            for (temp <- tc.r.elements) {
              undeclMap.get(temp) match {
                case Some(undecl) =>
                  grounds = grounds :+ undecl
                  undeclMap = undeclMap -- ISZ(temp)
                case _ =>
              }
            }
        }
      }
      blocks = blocks :+ b(grounds = grounds)
    }
    @strictpure def isInvoke(g: AST.IR.Stmt.Ground): B = g match {
      case AST.IR.Stmt.Assign.Temp(_, _: AST.IR.Exp.Apply, _) => T
      case _: AST.IR.Stmt.Expr => T
      case _ => F
    }
    return transformSplitTest(fresh, p(body = body(blocks = blocks)), isInvoke _)
  }

  def transformProgram(fresh: lang.IRTranslator.Fresh, program: AST.IR.Program): AST.IR.Program = {
    @pure def transform(p: AST.IR.Procedure): AST.IR.Procedure = {
      var r = p
      r = transformApplyResult(fresh, r)
      r = transformEmptyBlock(r)
      r = transformTemp(r)
      r = transformTempCompress(r);
      {
        var cont = T
        while (cont) {
          val r2 = transformEmptyBlock(transformSplitReadWrite(fresh, r))
          cont = r2.body.asInstanceOf[AST.IR.Body.Basic].blocks.size != r.body.asInstanceOf[AST.IR.Body.Basic].blocks.size
          r = r2
        }
      }
      return r
    }

    return program(procedures = ops.ISZOps(program.procedures).mParMap(transform _))
  }

  @memoize def callResultId(id: String, pos: message.Position): String = {
    return s"$id$resultLocalId@[${pos.beginLine},${pos.beginColumn}].${sha3(pos.string)}"
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
            grounds = grounds :+ AST.IR.Stmt.Decl(F, T, F, called.context, locals, e.pos)
            grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
              AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
              T, typeByteSize(cpType), AST.IR.Exp.Int(cpType, label, e.pos), st"$returnLocalId@0 = $label", cpType, e.pos
            ))
            if (called.tipe.ret != AST.Typed.unit) {
              val n = callResultOffsetMap.get(callResultId(e.id, e.pos)).get - spAdd
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeByteSize(cpType), e.pos), e.pos),
                T, typeByteSize(spType),
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, n, e.pos), e.pos),
                st"$resultLocalId@${typeByteSize(cpType)} = $n", spType, e.pos))
            }
            var paramOffset: Z = typeByteSize(cpType)
            val isMain = called.owner == owner && called.id == id
            if (called.tipe.ret != AST.Typed.unit) {
              paramOffset = paramOffset + typeByteSize(spType)
              if (isMain) {
                paramOffset = paramOffset + typeByteSize(p.tipe.ret)
              }
            }
            for (param <- ops.ISZOps(ops.ISZOps(called.paramNames).zip(mc.t.args)).zip(e.args)) {
              val ((pid, pt), parg) = param
              val t: AST.Typed = if (isScalar(pt)) pt else spType
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, paramOffset, e.pos), e.pos),
                T, typeByteSize(t), parg, st"$pid = ${parg.prettyST}", t, parg.pos))
              paramOffset = paramOffset + typeByteSize(t)
              if (isMain && !isScalar(pt)) {
                paramOffset = paramOffset + typeByteSize(pt)
              }
            }
            var bgrounds = ISZ[AST.IR.Stmt.Ground](
              AST.IR.Stmt.Decl(T, T, F, called.context, for (i <- locals.size - 1 to 0 by -1) yield locals(i), e.pos),
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
                case _ => blocks = blocks :+ b
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

  def transformTemp(proc: AST.IR.Procedure): AST.IR.Procedure = {
    val body = proc.body.asInstanceOf[AST.IR.Body.Basic]
    val blocks = body.blocks
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- blocks) yield (b.label, b))
    var tempSubstMap = HashMap.empty[Z, HashMap[Z, AST.IR.Exp]] + blocks(0).label ~> HashMap.empty
    var work = ISZ[AST.IR.BasicBlock](blocks(0))
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.BasicBlock]()
      for (b <- work) {
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        var substMap = tempSubstMap.get(b.label).get
        for (g <- b.grounds) {
          def rest(): Unit = {
            grounds = grounds :+ TempExpSubstitutor(substMap).transformIRStmtGround(g).getOrElse(g)
          }

          g match {
            case g: AST.IR.Stmt.Assign.Temp =>
              g.rhs match {
                case rhs: AST.IR.Exp.Bool => substMap = substMap + g.lhs ~> rhs
                case rhs: AST.IR.Exp.Int => substMap = substMap + g.lhs ~> rhs
                case rhs: AST.IR.Exp.F32 => substMap = substMap + g.lhs ~> rhs
                case rhs: AST.IR.Exp.F64 => substMap = substMap + g.lhs ~> rhs
                case rhs: AST.IR.Exp.R => substMap = substMap + g.lhs ~> rhs
                case rhs: AST.IR.Exp.String => substMap = substMap + g.lhs ~> rhs
                case rhs: AST.IR.Exp.EnumElementRef => substMap = substMap + g.lhs ~> rhs
                case rhs: AST.IR.Exp.Temp => substMap = substMap + g.lhs ~> substMap.get(rhs.n).get
                case rhs: AST.IR.Exp.Unary =>
                  substMap = substMap + g.lhs ~> rhs(exp = TempExpSubstitutor(substMap).transformIRExp(rhs.exp).getOrElse(rhs.exp))
                case rhs: AST.IR.Exp.Type =>
                  substMap = substMap + g.lhs ~> rhs(exp = TempExpSubstitutor(substMap).transformIRExp(rhs.exp).getOrElse(rhs.exp))
                case rhs: AST.IR.Exp.Binary =>
                  val tes = TempExpSubstitutor(substMap)
                  substMap = substMap + g.lhs ~> rhs(left = tes.transformIRExp(rhs.left).getOrElse(rhs.left),
                    right = tes.transformIRExp(rhs.right).getOrElse(rhs.right))
                case _: AST.IR.Exp.Intrinsic => halt("Infeasible")
                case _: AST.IR.Exp.If => halt("Infeasible")
                case _ =>
                  substMap = substMap + g.lhs ~> AST.IR.Exp.Temp(g.lhs, g.rhs.tipe, g.pos)
                  rest()
              }
            case _ => rest()
          }
        }
        val jump = TempExpSubstitutor(substMap).transformIRJump(b.jump).getOrElse(b.jump)
        blockMap = blockMap + b.label ~> b(grounds = grounds, jump = jump)
        for (target <- jump.targets) {
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
    return proc(body = body(blocks = blockMap.values))
  }

  def transformTempCompress(proc: AST.IR.Procedure): AST.IR.Procedure = {
    val tc = TempCollector(HashSSet.empty)
    tc.transformIRProcedure(proc)
    val temps = tc.r.elements
    var tempMap = HashMap.empty[Z, Z]
    for (i <- temps.indices) {
      tempMap = tempMap + temps(i) ~> i
    }
    return TempRenumberer(tempMap).transformIRProcedure(proc).getOrElse(proc)
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
    }
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
              var locals = ISZ[Intrinsic.Decl.Local]()
              val mult: Z = if (g.undecl) -1 else 1
              for (l <- g.locals) {
                val (size, dataSize): (Z, Z) =
                  if (isScalar(l.tipe)) (typeByteSize(l.tipe), 0)
                  else (typeByteSize(spType), if (g.isAlloc) typeByteSize(l.tipe) else 0)
                if (g.undecl) {
                  locals = locals :+ Intrinsic.Decl.Local(m.get(l.id).get, size, dataSize, l.id, l.tipe)
                  m = m -- ISZ(l.id)
                } else {
                  m = m + l.id ~> offset
                  locals = locals :+ Intrinsic.Decl.Local(offset, size, dataSize, l.id, l.tipe)
                }
                offset = offset + (if (isScalar(l.tipe)) typeByteSize(l.tipe) else typeByteSize(spType) +
                  (if (g.isAlloc) typeByteSize(l.tipe) else 0)) * mult
              }
              if (maxOffset < offset) {
                maxOffset = offset
              }
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(g.undecl, g.isAlloc, locals, g.pos))
            case _ =>
              g match {
                case AST.IR.Stmt.Assign.Global(_, name, tipe, rhs, pos) =>
                  val globalOffset = AST.IR.Exp.Int(spType, globalMap.get(name).get.offset, pos)
                  if (isScalar(tipe)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(globalOffset, isSigned(tipe),
                      typeByteSize(tipe), rhs, g.prettyST, tipe, g.pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(globalOffset, typeByteSize(tipe),
                      typeByteSize(rhs.tipe), rhs, g.prettyST, tipe, rhs.tipe, g.pos))
                  }
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
                case AST.IR.Stmt.Assign.Index(_, receiver, idx, rhs, pos) =>
                  val seqType = receiver.tipe.asInstanceOf[AST.Typed.Name]
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
                  var index = idx
                  if (index.tipe != spType) {
                    index = AST.IR.Exp.Type(F, index, spType, index.pos)
                  }
                  val indexOffset: AST.IR.Exp = if (min == 0) index else AST.IR.Exp.Binary(
                    spType, index, AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, min, index.pos), index.pos)
                  val elementSize = typeByteSize(elementType)
                  val elementOffset: AST.IR.Exp = if (elementSize == 1) indexOffset else AST.IR.Exp.Binary(spType,
                    indexOffset, AST.IR.Exp.Binary.Op.Mul, AST.IR.Exp.Int(spType, typeByteSize(elementType),
                      index.pos), index.pos)
                  val receiverOffset = AST.IR.Exp.Binary(spType, receiver, AST.IR.Exp.Binary.Op.Add, elementOffset, pos)
                  if (isScalar(elementType)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.StoreScalar(receiverOffset,
                      isSigned(elementType), typeByteSize(elementType), rhs, g.prettyST, elementType, g.pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(receiverOffset, typeByteSize(elementType),
                      typeByteSize(rhs.tipe), rhs, g.prettyST, elementType, rhs.tipe, g.pos))
                  }
                case AST.IR.Stmt.Assign.Temp(n, rhs, pos) =>
                  rhs match {
                    case rhs: AST.IR.Exp.LocalVarRef =>
                      val localOffset = m.get(rhs.id).get
                      val temp = n
                      val t: AST.Typed = if (isScalar(rhs.tipe)) rhs.tipe else spType
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Load(temp,
                        AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.StackPointer(spType, rhs.pos)),
                          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, rhs.pos), rhs.pos),
                        isSigned(t), typeByteSize(t), g.prettyST, rhs.tipe, rhs.pos))
                    case rhs: AST.IR.Exp.FieldVarRef =>
                      if (isSeq(rhs.receiver.tipe)) {
                        assert(rhs.id == "size")
                        val temp = n
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Load(
                          temp, AST.IR.Exp.Binary(spType, rhs.receiver,
                            AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, typeShaSize, rhs.pos), rhs.pos),
                          T, typeByteSize(rhs.tipe), g.prettyST, rhs.tipe, rhs.pos))
                      } else {
                        halt(s"TODO: $rhs")
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
                      var index = rhs.index
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
                      val rhsOffset = AST.IR.Exp.Binary(spType, rhs.exp, AST.IR.Exp.Binary.Op.Add, elementOffset, rhs.exp.pos)
                      if (isScalar(elementType)) {
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Load(temp, rhsOffset,
                          isSigned(elementType), typeByteSize(elementType), g.prettyST, elementType, g.pos))
                      } else {
                        grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, rhsOffset, g.pos)
                      }
                    case rhs: AST.IR.Exp.GlobalVarRef =>
                      val temp = n
                      val globalOffset = AST.IR.Exp.Int(spType, globalMap.get(rhs.name).get.offset, rhs.pos)
                      if (isScalar(rhs.tipe)) {
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Load(temp, globalOffset, isSigned(rhs.tipe),
                          typeByteSize(rhs.tipe), g.prettyST, rhs.tipe, g.pos))
                      } else {
                        grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, globalOffset, rhs.pos)
                      }
                    case _: AST.IR.Exp.If => halt(s"Infeasible: $rhs")
                    case _: AST.IR.Exp.Intrinsic => halt(s"Infeasible: $rhs")
                    case _ => grounds = grounds :+ g
                  }
                case _ => grounds = grounds :+ g
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
        blockMap = blockMap + b.label ~> b(grounds = grounds)
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

  @memoize def isSeq(t: AST.Typed): B = {
    t match {
      case t: AST.Typed.Name => return t.ids == AST.Typed.isName || t.ids == AST.Typed.msName
      case _ =>
    }
    return F
  }
}