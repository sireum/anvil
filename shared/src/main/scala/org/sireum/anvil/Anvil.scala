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
import org.sireum.alir.{ControlFlowGraph, TypeSpecializer}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Reporter
import org.sireum.U32._
import org.sireum.U8._
import org.sireum.anvil.PrinterIndex.U._
import org.sireum.anvil.Util._

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
                         val printSize: Z,
                         val copySize: Z,
                         val erase: B) {
    val shouldPrint: B = printSize > 0
  }

  object Config {
    @strictpure def empty(projectName: String): Config =
      Config(projectName, 512 * 1024, 64, 100, 100, HashMap.empty, HashMap.empty, F, 1, F, 0, 8, F)
  }

  @sig trait Output {
    def add(isFinal: B, path: => ISZ[String], content: => ST): Unit
  }

  @datatype class VarInfo(val isScalar: B,
                          val offset: Z,
                          val size: Z,
                          val dataSize: Z,
                          val tipe: AST.Typed,
                          val pos: message.Position) {
    @strictpure def totalSize: Z = size + dataSize
  }

  @datatype class IR(val anvil: Anvil,
                     val procedure: AST.IR.Procedure,
                     val maxRegisters: Z,
                     val globalInfoMap: HashSMap[QName, VarInfo])

  def synthesize(isTest: B, fresh: lang.IRTranslator.Fresh, th: TypeHierarchy, name: QName, config: Config,
                 output: Output, reporter: Reporter): Unit = {
    generateIR(isTest, fresh, th, name, config, output, reporter) match {
      case Some(ir) => HwSynthesizer(ir.anvil).printProcedure(ir.procedure.id, ir.procedure, output, ir.maxRegisters)
      case _ =>
    }
  }

  def generateIR(isTest: B, fresh: lang.IRTranslator.Fresh, th: TypeHierarchy, name: QName, config: Config,
                 output: Output, reporter: Reporter): Option[IR] = {
    assert(config.memory > 0 && config.memory % 8 == 0, s"Memory configuration has to be a positive integer multiples of 8")
    var entryPoints = ISZ[TypeSpecializer.EntryPoint]()
    for (info <- th.nameMap.values) {
      info match {
        case info: Info.Method if info.owner == name || info.name == name =>
          for (ann <- info.ast.sig.annotations) {
            if (ann.name == mainAnnName && !isTest) {
              entryPoints = entryPoints :+ TypeSpecializer.EntryPoint.Method(info.name)
            } else if (ann.name == testAnnName && isTest) {
              entryPoints = entryPoints :+ TypeSpecializer.EntryPoint.Method(info.name)
            }
          }
        case _ =>
      }
    }
    val tsr = TypeSpecializer.specialize(th, entryPoints, HashMap.empty, reporter)
    if (tsr.extMethods.nonEmpty) {
      reporter.error(None(), kind, s"@ext methods are not supported")
    }
    if (reporter.hasError) {
      return None()
    }
    fresh.setTemp(0)
    fresh.setLabel(startingLabel)
    return Anvil(th, tsr, name, config, 0).generateIR(isTest, fresh, output, reporter)
  }

}

import Anvil._

@datatype class Anvil(val th: TypeHierarchy,
                      val tsr: TypeSpecializer.Result,
                      val owner: QName,
                      val config: Config,
                      val numOfLocs: Z) {

  val typeShaType: AST.Typed.Name = AST.Typed.u32
  val typeShaSize: Z = typeByteSize(typeShaType)
  val spType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "SP"), ISZ())
  val cpType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "CP"), ISZ())
  val dpType: AST.Typed.Name = AST.Typed.Name(ISZ("org", "sireum", "DP"), ISZ())
  val dpMask: Z = {
    val size = anvil.Runtime.Ext.z2u(config.printSize)
    var r = u"2"
    while (r < size) {
      r = r << u"1"
    }
    r = r - u"1"
    anvil.Runtime.Ext.u2z(r)
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
    ISZ("ir", "procedures", s"$procedureId-${sha3Type(pType)}", s"$stage-$pass-$id.sir")

  def generateIR(isTest: B, fresh: lang.IRTranslator.Fresh, output: Output, reporter: Reporter): Option[IR] = {
    val threeAddressCode = T

    val irt = lang.IRTranslator(threeAddressCode = threeAddressCode, threeAddressCodeLit = F,
      th = tsr.typeHierarchy, fresh = fresh)

    var stage: Z = 0

    val mq: (AST.IR.MethodContext, AST.IR.Program, Z, HashSMap[ISZ[String], VarInfo]) = {
      var globals = ISZ[AST.IR.Global]()
      var procedures = ISZ[AST.IR.Procedure]()
      var globalSize: Z = 0

      var startOpt = Option.none[AST.IR.Procedure]()
      var testProcs = ISZ[AST.IR.Procedure]()
      var mainProcs = ISZ[AST.IR.Procedure]()
      for (ms <- tsr.methods.values; m <- ms.elements) {
        val receiverOpt: Option[AST.Typed] = m.receiverOpt match {
          case Some(t) => Some(t)
          case _ => None()
        }
        val p = irt.translateMethod(F, receiverOpt, m.info.owner, m.info.ast)
        procedures = procedures :+ p
        procedureMod(p.context) match {
          case PMod.Main =>
            if (!isTest) {
              startOpt = Some(p)
            }
            if (p.context.isInObject) {
              if (th.nameMap.get(p.context.owner :+ p.context.id).get.asInstanceOf[Info.Method].ast.sig.typeParams.nonEmpty) {
                reporter.error(Some(p.pos), kind, s"@anvil.hls methods cannot have type parameters")
              }
            } else {
              reporter.error(Some(p.pos), kind, s"@anvil.hls methods should be object/top-level methods")
            }
            mainProcs = mainProcs :+ p
          case PMod.Test =>
            testProcs = testProcs :+ p
            if (p.context.isInObject) {
              if (th.nameMap.get(p.context.owner :+ p.context.id).get.asInstanceOf[Info.Method].ast.sig.typeParams.nonEmpty) {
                reporter.error(Some(p.pos), kind, s"@anvil.test methods cannot have type parameters")
              }
              if (p.context.t.args.nonEmpty) {
                reporter.error(Some(p.pos), kind, s"@anvil.test methods cannot have parameters")
              }
              if (p.context.t.isByName) {
                reporter.error(Some(p.pos), kind, s"@anvil.test methods should have an empty parameter list")
              }
              if (p.context.t.ret != AST.Typed.unit) {
                reporter.error(Some(p.pos), kind, s"@anvil.test methods should return Unit")
              }
            } else {
              reporter.error(Some(p.pos), kind, s"@anvil.test methods should be object/top-level methods")
            }
          case PMod.None =>
        }
      }
      if (isTest) {
        if (testProcs.isEmpty) {
          reporter.error(None(), kind, st"Could not find @anvil.test methods in ${(owner, ".")}".render)
          return None()
        }
        val pos = testProcs(0).pos
        val tempNum = 0
        var stmts = ISZ[AST.IR.Stmt](
          AST.IR.Stmt.Assign.Temp(tempNum, AST.IR.Exp.GlobalVarRef(testNumName, AST.Typed.z, pos), pos)
        )
        val temp = AST.IR.Exp.Temp(tempNum, AST.Typed.z, pos)
        val zero = AST.IR.Exp.Int(AST.Typed.z, 0, pos)
        var i: Z = 0
        for (p <- testProcs) {
          stmts = stmts :+ AST.IR.Stmt.If(
            AST.IR.Exp.Binary(
              AST.Typed.b,
              AST.IR.Exp.Binary(AST.Typed.z, temp, AST.IR.Exp.Binary.Op.Lt, zero, pos),
              AST.IR.Exp.Binary.Op.Or,
              AST.IR.Exp.Binary(AST.Typed.z, temp, AST.IR.Exp.Binary.Op.Eq, AST.IR.Exp.Int(AST.Typed.z, i, pos), pos),
              pos),
            AST.IR.Stmt.Block(ISZ(
              AST.IR.Stmt.Expr(AST.IR.Exp.Apply(T, p.context.owner, p.context.id, ISZ(), p.tipe, AST.Typed.unit, pos))
            ), pos), AST.IR.Stmt.Block(ISZ(), pos), pos)
          i = i + 1
        }
        val test = AST.IR.Procedure(T, ISZ(), ISZ(), testId, ISZ(),
          AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.unit),
          AST.IR.Body.Block(AST.IR.Stmt.Block(stmts, pos)), pos)
        procedures = test +: procedures
        startOpt = Some(test)
      } else {
        if (startOpt.isEmpty) {
          reporter.error(None(), kind, st"Could not find @anvil.hls methods in ${(owner, ".")}".render)
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
      if (config.stackTrace) {
        globals = globals :+ AST.IR.Global(typeShaType, memTypeName, startOpt.get.pos)
        globals = globals :+ AST.IR.Global(AST.Typed.z, memSizeName, startOpt.get.pos)
      }
      if (isTest) {
        globals = globals :+ AST.IR.Global(AST.Typed.z, testNumName, startOpt.get.pos)
      }
      if (config.shouldPrint) {
        globals = globals :+ AST.IR.Global(displayType, displayName, startOpt.get.pos)
        for (id <- runtimeMethodTypeMap.keys) {
          val info = th.nameMap.get(runtimeName :+ id).get.asInstanceOf[Info.Method]
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
      var globalMap = HashSMap.empty[ISZ[String], VarInfo]
      val spSize = typeByteSize(spType)
      for (g <- globals) {
        val size = typeByteSize(g.tipe)
        if (!isScalar(g.tipe)) {
          globalMap = globalMap + g.name ~> VarInfo(F, globalSize, spSize, size, g.tipe, g.pos)
          globalSize = globalSize + spSize
        } else {
          globalMap = globalMap + g.name ~> VarInfo(T, globalSize, size, 0, g.tipe, g.pos)
        }
        globalSize = globalSize + size
      }
      (startOpt.get.context, AST.IR.Program(threeAddressCode, globals, procedures), globalSize, globalMap)
    }

    val startContext = mq._1
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
    val anvil = Anvil(th, tsr, owner, config, numOfLocs + 1)

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

        proc = anvil.transformStackTraceDesc(proc)
        output.add(F, irProcedurePath(proc.id, proc.tipe, stage, pass, "stack-frame-desc"), proc.prettyST)
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

    val main = procedureMap.get(startContext).get
    program = {
      val p = transformMainStackFrame(main)(body = main.body.asInstanceOf[AST.IR.Body.Basic](blocks =
        anvil.mergeProcedures(main, fresh, procedureMap, procedureSizeMap, callResultOffsetMap, maxRegisters)))
      output.add(F, irProcedurePath(p.id, p.tipe, stage, 0, "merged"), p.prettyST)
      program(procedures = ISZ(p))
    }
    output.add(F, ISZ("ir", s"$stage-merged.sir"), program.prettyST)

    stage = stage + 1

    program = {
      var p = program.procedures(0)
      var pass: Z = 0

      @strictpure def isRegisterInc(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = g match {
        case AST.IR.Stmt.Intrinsic(in: Intrinsic.RegisterAssign) if in.isInc =>
          grounds.isEmpty ||
            ops.ISZOps(grounds).exists((ground: AST.IR.Stmt.Ground) => !ground.isInstanceOf[AST.IR.Stmt.Decl])
        case _ => F
      }

      p = anvil.transformSplitTest(F, fresh, p, isRegisterInc _)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "register-inc"), p.prettyST)
      pass = pass + 1

      @strictpure def isCopy(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = g match {
        case AST.IR.Stmt.Intrinsic(_: Intrinsic.Copy) => T
        case _ => F
      }

      p = anvil.transformSplitTest(F, fresh, p, isCopy _)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-copy"), p.prettyST)
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
      var globalParamSTs = ISZ[ST]()
      for (entry <- anvil.procedureParamInfo(PBox(main))._2.entries) {
        globalParamSTs = globalParamSTs :+ st"- parameter ${entry._1}: ${entry._2.tipe} @[offset = ${entry._2.offset}, size = ${entry._2.size}, data-size = ${entry._2.dataSize}]"
      }
      for (pair <- globalMap.entries) {
        val (name, info) = pair
        globalParamSTs = globalParamSTs :+ st"- global ${(name, ".")}: ${info.tipe} @[offset = ${info.offset}, size = ${info.size}, data-size = ${info.dataSize}]"
      }
      st"""/*
          |   Note that globalSize = $globalSize, max registers (beside SP and CP) = $maxRegisters, and initially:
          |   - register CP (code pointer) = 3 (${anvil.signedString(cpType)}, byte size = ${anvil.typeByteSize(cpType)})
          |   - register SP (stack pointer) = $globalSize (${anvil.signedString(spType)}, byte size = ${anvil.typeByteSize(spType)})
          |   - register DP (display pointer) = 0 (${anvil.signedString(dpType)}, byte size = ${anvil.typeByteSize(dpType)})
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
    return Some(IR(anvil, program.procedures(0), maxRegisters, globalMap))
  }

  @pure def transformBlock(stage: Z, output: Output, p: AST.IR.Procedure): AST.IR.Procedure = {
    var pass: Z = 0
    var r = p

    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "initial"), r.prettyST)
    pass = pass + 1

    r = ConversionsTransformer(this).transform_langastIRProcedure(r).getOrElse(r)
    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "conversions"), r.prettyST)
    pass = pass + 1

    r = if (p.owner == runtimeName) r else RuntimeCheckInserter(this).transform_langastIRProcedure(r).getOrElse(r)
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
    var map = HashMap.empty[Z, AST.IR.Jump]
    for (b <- body.blocks if b.grounds.isEmpty) {
      b.jump match {
        case j: AST.IR.Jump.Goto => map = map + b.label ~> j
        case j@AST.IR.Jump.Intrinsic(_: Intrinsic.GotoLocal) => map = map + b.label ~> j
        case _ =>
      }
    }
    if (map.isEmpty) {
      return p
    }
    def getTarget(l: Z): Z = {
      map.get(l) match {
        case Some(AST.IR.Jump.Goto(l2, _)) => return getTarget(l2)
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
        case j: AST.IR.Jump.Goto =>
          val l = getTarget(j.label)
          map.get(l) match {
            case Some(j2) => j2
            case _ => j(label = l)
          }
        case j: AST.IR.Jump.Return => j
        case j: AST.IR.Jump.Intrinsic => j
        case j: AST.IR.Jump.Halt => j
      }
      blockMap = blockMap + b.label ~> b(jump = jump)
    }
    blockMap = blockMap -- ((for (labelIncomings <- countNumOfIncomingJumps(blockMap.values).entries
                                  if labelIncomings._2 == 0) yield labelIncomings._1) -- ISZ(0, 1, body.blocks(0).label))
    return p(body = body(blocks = blockMap.values))
  }

  def transformSplitTempJump(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      if (b.grounds.isEmpty) {
        blocks = blocks :+ b
      } else {
        val tc = TempCollector(HashSSet.empty)
        tc.transform_langastIRJump(b.jump)
        if (tc.r.nonEmpty) {
          val label = fresh.label()
          blocks = blocks :+ b(jump = AST.IR.Jump.Goto(label, b.jump.pos))
          blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(), b.jump)
        } else {
          blocks = blocks :+ b
        }
      }
    }
    return p(body = body(blocks = blocks))
  }

  def transformSplitTest(goto: B, fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure,
                         test: (ISZ[AST.IR.Stmt.Ground], AST.IR.Stmt.Ground) => B @pure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      if (b.grounds.size <= 1) {
        if (goto && !b.jump.isInstanceOf[AST.IR.Jump.Goto]) {
          val n = fresh.label()
          blocks = blocks :+ AST.IR.BasicBlock(b.label, b.grounds, AST.IR.Jump.Goto(n, b.jump.pos))
          blocks = blocks :+ AST.IR.BasicBlock(n, ISZ(), b.jump)
        } else {
          blocks = blocks :+ b
        }
      } else {
        var block = b
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        for (g <- b.grounds) {
          if (test(grounds, g)) {
            val n = fresh.label()
            if (grounds.isEmpty) {
              blocks = blocks :+ AST.IR.BasicBlock(block.label, ISZ(g), AST.IR.Jump.Goto(n, g.pos))
            } else {
              val m = fresh.label()
              blocks = blocks :+ AST.IR.BasicBlock(block.label, grounds, AST.IR.Jump.Goto(m, g.pos))
              blocks = blocks :+ AST.IR.BasicBlock(m, ISZ(g), AST.IR.Jump.Goto(n, g.pos))
            }
            grounds = ISZ()
            if (goto && !b.jump.isInstanceOf[AST.IR.Jump.Goto]) {
              val l = fresh.label()
              blocks = blocks :+ AST.IR.BasicBlock(n, ISZ(), AST.IR.Jump.Goto(l, block.jump.pos))
              block = AST.IR.BasicBlock(l, ISZ(), block.jump)
            } else {
              block = AST.IR.BasicBlock(n, grounds, block.jump)
            }
          } else {
            grounds = grounds :+ g
          }
        }
        blocks = blocks :+ block(grounds = grounds)
      }
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

  def transformMergeDecl(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blockMap = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    val m = countNumOfIncomingJumps(body.blocks)
    for (b <- body.blocks) {
      b.jump match {
        case j: AST.IR.Jump.Goto if m.get(j.label) == Some(1) && ops.ISZOps(b.grounds).
          forall((g: AST.IR.Stmt.Ground) => g.isInstanceOf[AST.IR.Stmt.Decl]) =>
          val b2 = blockMap.get(j.label).get
          blockMap = blockMap + b.label ~> b(grounds = b.grounds ++ b2.grounds, jump = b2.jump)
          blockMap = blockMap -- ISZ(b2.label)
        case _ =>
      }
    }
    return p(body = body(blocks = blockMap.values))
  }

  def transformConstruct(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    var body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()

    for (b <- body.blocks) {
      var block = b
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case g@AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.Construct, _) =>
            val decl = AST.IR.Stmt.Decl(F, T, T, p.context, ISZ(
              AST.IR.Stmt.Decl.Local(constructResultId(rhs.pos), rhs.tipe)), g.pos)
            grounds = grounds :+ decl
            grounds = grounds :+ g
            val label = fresh.label()
            blocks = blocks :+ block(block.label, grounds, AST.IR.Jump.Goto(label, g.pos))
            grounds = ISZ()
            block = block(label, grounds, block.jump)
            val temp = AST.IR.Exp.Temp(g.lhs, rhs.tipe, rhs.pos)
            if (rhs.tipe.ids == AST.Typed.isName || rhs.tipe.ids == AST.Typed.msName) {
              val indexType = rhs.tipe.args(0)
              val min: Z = indexType match {
                case AST.Typed.z => 0
                case _ =>
                  val subz = subZOpt(indexType).get.ast
                  if (subz.isIndex) subz.min
                  else if (subz.isZeroIndex) 0
                  else subz.min
              }
              for (i <- rhs.args.indices) {
                val arg = rhs.args(i)
                grounds = grounds :+ AST.IR.Stmt.Assign.Index(temp, AST.IR.Exp.Int(indexType, min + i, arg.pos), arg,
                  arg.pos)
              }
            } else {
              val info = th.typeMap.get(rhs.tipe.ids).get.asInstanceOf[TypeInfo.Adt]
              val sm = TypeChecker.buildTypeSubstMap(rhs.tipe.ids, None(), info.ast.typeParams, rhs.tipe.args,
                message.Reporter.create).get
              for (pair <- ops.ISZOps(info.ast.params).zip(rhs.args)) {
                grounds = grounds :+ AST.IR.Stmt.Assign.Field(temp, pair._1.id.value,
                  pair._1.tipe.typedOpt.get.subst(sm), pair._2, pair._2.pos)
              }
            }
            if (classInit(rhs.tipe).nonEmpty) {
              grounds = grounds :+ AST.IR.Stmt.Expr(AST.IR.Exp.Apply(F, rhs.tipe.ids, newInitId,
                ISZ(temp), AST.Typed.Fun(AST.Purity.Impure, F, ISZ(rhs.tipe), AST.Typed.unit), AST.Typed.unit, rhs.pos))
            }
          case _ => grounds = grounds :+ g
        }
      }
      blocks = blocks :+ block(grounds = grounds)
    }
    body = body(blocks = blocks)

    val exit = MBox(HashSMap.empty[Z, ISZ[HashSSet[Z]]])
    TempLV(ControlFlowGraph.buildBasic(body)).compute(body, MBox(HashSMap.empty[Z, ISZ[HashSSet[Z]]]), exit)
    var blockMap = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))

    def rec(label: Z, i: Z, temp: Z, undecl: AST.IR.Stmt.Decl): Unit = {
      val b = blockMap.get(label).get
      for (j <- i until b.grounds.size) {
        val g = b.grounds(j)
        val tc = TempCollector(HashSSet.empty)
        tc.transform_langastIRStmtGround(g)
        if (tc.r.contains(temp) && !exit.value.get(b.label).get(i).contains(temp)) {
          val bgOps = ops.ISZOps(b.grounds)
          blockMap = blockMap + label ~> b(grounds = (bgOps.slice(0, j + 1) :+ undecl) ++ bgOps.slice(j + 1, b.grounds.size))
          return
        }
      }
      for (target <- b.jump.targets) {
        rec(target, 0, temp, undecl)
      }
    }

    for (b <- body.blocks) {
      for (i <- b.grounds.indices) {
        val g = b.grounds(i)
        g match {
          case AST.IR.Stmt.Assign.Temp(temp, rhs: AST.IR.Exp.Construct, _) =>
            val undecl = AST.IR.Stmt.Decl(T, T, T, p.context, ISZ(
              AST.IR.Stmt.Decl.Local(constructResultId(rhs.pos), rhs.tipe)), g.pos)
            rec(b.label, i + 1, temp, undecl)
          case _ =>
        }
      }
    }
    return p(body = body(blocks = blockMap.values))
  }

  def transformApplyConstructResult(p: AST.IR.Procedure): AST.IR.Procedure = {
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

    return p(body = body(blocks = blocks))
  }

  def transformGlobalVarRef(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      var block = b
      for (g <- b.grounds) {
        g match {
          case g@AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.GlobalVarRef, pos) if !ignoreGlobalInits.contains(rhs.name) =>
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

  def transformStackTraceDesc(p: AST.IR.Procedure): AST.IR.Procedure = {
    if (!config.stackTrace) {
      return p
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val sfCallerOffset = procedureParamInfo(PBox(p))._2.get(sfCallerId).get.offset + typeShaSize + typeByteSize(AST.Typed.z)
    val first = body.blocks(0)
    val desc = conversions.String.toU8is(procedureDesc(p))
    var grounds = ISZ[AST.IR.Stmt.Ground]()
    for (i <- desc.indices) {
      val offset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, p.pos)),
        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, i + sfCallerOffset, p.pos), p.pos)
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(offset, F, 1,
        AST.IR.Exp.Int(AST.Typed.u8, desc(i).toZ, p.pos), st"'${ops.COps(conversions.U32.toC(conversions.U8.toU32(desc(i)))).escapeString}'", AST.Typed.u8, p.pos))
    }
    return p(body = body(blocks = body.blocks(0 ~> first(grounds = grounds ++ first.grounds))))
  }

  def transformMainStackFrame(p: AST.IR.Procedure): AST.IR.Procedure = {
    if (!config.stackTrace) {
      return p
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var grounds = ISZ[AST.IR.Stmt.Ground]()
    grounds = grounds :+ AST.IR.Stmt.Assign.Local(p.context, sfCallerId, spType, AST.IR.Exp.Int(spType, 0, p.pos), p.pos)
    return p(body = body(blocks = body.blocks(0 ~> body.blocks(0)(grounds = grounds ++ body.blocks(0).grounds))))
  }

  def transformStackTraceLoc(p: AST.IR.Procedure): AST.IR.Procedure = {
    if (!config.stackTrace) {
      return p
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      var currentLine: Z = 0
      def assignLoc(pos: message.Position): Unit = {
        if (currentLine == pos.beginLine) {
          return
        }
        currentLine = pos.beginLine
        grounds = grounds :+ AST.IR.Stmt.Assign.Local(p.context, sfLocId, sfLocType,
          AST.IR.Exp.Int(sfLocType, currentLine, pos), pos)
      }
      for (g <- b.grounds) {
        assignLoc(g.pos)
        grounds = grounds :+ g
      }
      assignLoc(b.jump.pos)
      blocks = blocks :+ b(grounds = grounds)
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

      r = IntTransformer(this).transform_langastIRProcedure(r).getOrElse(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "int"), r.prettyST)
      pass = pass + 1

      r = transformStackTraceLoc(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "stack-trace-loc"), r.prettyST)
      pass = pass + 1

      r = transformHalt(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "halt"), r.prettyST)
      pass = pass + 1

      r = transformPrint(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "print"), r.prettyST)
      pass = pass + 1

      r = transformApplyConstructResult(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "apply-construct-result"), r.prettyST)
      pass = pass + 1

      r = transformEmptyBlock(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "empty-block"), r.prettyST)
      pass = pass + 1

      r = transformReduceTemp(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "reduce-temp"), r.prettyST)
      pass = pass + 1

//      r = transformReduceExp(r)
//      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "reduce-exp"), r.prettyST)
//      pass = pass + 1

      r = transformTempCompress(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "temp-compress"), r.prettyST)
      pass = pass + 1

      @pure def hasAssignTempUsage(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = {
        g match {
          case g: AST.IR.Stmt.Assign.Temp =>
            val tc = TempCollector(HashSSet.empty)
            tc.transform_langastIRExp(g.rhs)
            return tc.r.nonEmpty
          case _: AST.IR.Stmt.Assign => return T
          case _ => return F
        }
      }

      r = transformSplitTest(F, fresh, r, hasAssignTempUsage _)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-temp"), r.prettyST)
      pass = pass + 1

      r = transformSplitTempJump(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-temp-jump"), r.prettyST)
      pass = pass + 1

      r = transformConstruct(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "construct"), r.prettyST)
      pass = pass + 1

      //      r = transformSplitReadWrite(fresh, r)
//      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-read-write"), r.prettyST)
//      pass = pass + 1

      r = transformInstanceOf(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "instanceof"), r.prettyST)
      pass = pass + 1

      r = transformMergeDecl(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "merge-decl"), r.prettyST)
      pass = pass + 1

      @strictpure def isInvoke(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = g match {
        case AST.IR.Stmt.Assign.Temp(_, _: AST.IR.Exp.Apply, _) => T
        case _: AST.IR.Stmt.Expr => T
        case _ => F
      }

      r = transformSplitTest(T, fresh, r, isInvoke _)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-invoke"), r.prettyST)
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
    for (b <- blocks) {
      for (g <- b.grounds) {
        g match {
          case AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Intrinsic(Intrinsic.Register(T, _, _)), _, _, n: AST.IR.Exp.Int, _, _, _)) =>
            r = r + n.value ~> (r.get(n.value).get + 1)
          case _ =>
        }
      }
      for (target <- b.jump.targets) {
        r = r + target ~> (r.get(target).get + 1)
      }
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

            val paramInfo = procedureParamInfo(PBox(called))._2

            val returnInfo = paramInfo.get(returnLocalId).get
            var locals = ISZ[Intrinsic.Decl.Local](
              Intrinsic.Decl.Local(returnInfo.offset, returnInfo.totalSize, returnLocalId, returnInfo.tipe)
            )
            if (called.tipe.ret != AST.Typed.unit) {
              val resultInfo = paramInfo.get(resultLocalId).get
              locals = locals :+ Intrinsic.Decl.Local(resultInfo.offset, resultInfo.totalSize, resultLocalId,
                resultInfo.tipe)
            }
            if (config.stackTrace) {
              val sfCallerInfo = paramInfo.get(sfCallerId).get
              val sfDescInfo = paramInfo.get(sfDescId).get
              val sfLocInfo = paramInfo.get(sfLocId).get
              locals = locals :+ Intrinsic.Decl.Local(sfCallerInfo.offset, sfCallerInfo.totalSize, sfCallerId, sfCallerInfo.tipe)
              locals = locals :+ Intrinsic.Decl.Local(sfDescInfo.offset, sfDescInfo.totalSize, sfDescId, sfDescInfo.tipe)
              locals = locals :+ Intrinsic.Decl.Local(sfLocInfo.offset, sfLocInfo.totalSize, sfLocId, sfLocInfo.tipe)
            }
            for (param <- ops.ISZOps(called.paramNames).zip(called.tipe.args)) {
              val info = paramInfo.get(param._1).get
              locals = locals :+ Intrinsic.Decl.Local(info.offset, info.totalSize, param._1, param._2)
            }
            grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(F, F, locals, e.pos))
            grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
              AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
              isSigned(returnInfo.tipe), returnInfo.totalSize,
              AST.IR.Exp.Int(returnInfo.tipe, label, e.pos), st"$returnLocalId@0 = $label", returnInfo.tipe, e.pos
            ))
            if (called.tipe.ret != AST.Typed.unit) {
              val resultInfo = paramInfo.get(resultLocalId).get
              val n = callResultOffsetMap.get(callResultId(e.id, e.pos)).get - (spAdd + numOfRegisters * 8)
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, resultInfo.offset, e.pos), e.pos),
                isSigned(spType), typeByteSize(spType),
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, -n, e.pos), e.pos),
                st"$resultLocalId@${resultInfo.offset} = $n", spType, e.pos))
            }
            if (config.stackTrace) {
              val n = procedureParamInfo(PBox(p))._2.get(sfCallerId).get.offset -
                (spAdd + numOfRegisters * 8)
              val sfCallerInfo = paramInfo.get(sfCallerId).get
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, sfCallerInfo.offset, e.pos), e.pos),
                isSigned(spType), typeByteSize(spType),
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, -n, e.pos), e.pos),
                st"$sfCallerId@${sfCallerInfo.offset} = $n", spType, e.pos))
            }
            for (param <- ops.ISZOps(ops.ISZOps(called.paramNames).zip(mc.t.args)).zip(e.args)) {
              val ((pid, pt), parg) = param
              val t: AST.Typed = if (isScalar(pt)) pt else spType
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, paramInfo.get(pid).get.offset, e.pos), e.pos),
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
                  isSigned(spType), typeByteSize(spType), st"", t, g.pos))
                bgrounds = (rgrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(lhs, rhsOffset, F,
                  typeByteSize(t), st"$$$lhs = $returnLocalId", t, g.pos))) ++ bgrounds
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
                      typeByteSize(p.context.t.ret), copySize(exp), exp, st"$resultLocalId = ${exp.prettyST}",
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

  @pure def procedureDesc(proc: AST.IR.Procedure): String = {
    var uri = proc.pos.uriOpt.get
    val i = ops.StringOps(uri).lastIndexOf('/')
    if (i >= 0) {
      uri = ops.StringOps(uri).substring(i + 1, uri.size)
    }
    return st"${(proc.owner :+ proc.id, ".")} ($uri:".render
  }

  @memoize def procedureParamInfo(pbox: PBox): (Z, HashSMap[String, VarInfo]) = {
    val p = pbox.p
    var m = HashSMap.empty[String, VarInfo]
    var maxOffset: Z = 0
    m = m + returnLocalId ~> VarInfo(isScalar(cpType), maxOffset, typeByteSize(cpType), 0, cpType, p.pos)
    maxOffset = maxOffset + typeByteSize(cpType)

    val isMain = procedureMod(p.context) == PMod.Main
    if (p.tipe.ret != AST.Typed.unit) {
      val dataSize: Z = if (isMain) typeByteSize(p.tipe.ret) else 0
      val size = typeByteSize(spType)
      m = m + resultLocalId ~> VarInfo(isScalar(spType), maxOffset, size, dataSize, spType, p.pos)
      maxOffset = maxOffset + size + dataSize
    }

    if (config.stackTrace) {
      m = m + sfCallerId ~> VarInfo(isScalar(spType), maxOffset, typeByteSize(spType), 0, spType, p.pos)
      maxOffset = maxOffset + typeByteSize(spType)

      m = m + sfLocId ~> VarInfo(isScalar(sfLocType), maxOffset, typeByteSize(sfLocType), 0, sfLocType, p.pos)
      maxOffset = maxOffset + typeByteSize(sfLocType)

      val mdesc = procedureDesc(p)
      val mdescType = AST.Typed.Name(AST.Typed.isName, ISZ(AST.Typed.Name(ISZ(s"${mdesc.size}"), ISZ()), AST.Typed.u8))
      m = m + sfDescId ~> VarInfo(isScalar(mdescType), maxOffset, typeByteSize(mdescType), 0, mdescType, p.pos)
      maxOffset = maxOffset + typeByteSize(mdescType)
    }

    {
      for (param <- ops.ISZOps(p.paramNames).zip(p.tipe.args)) {
        val (id, t) = param
        val dataSize: Z = if (isMain && !isScalar(t)) typeByteSize(t) else 0
        val size: Z = if (isScalar(t)) typeByteSize(t) else typeByteSize(spType)
        m = m + id ~> VarInfo(isScalar(t), maxOffset, size, dataSize, t, p.pos)
        maxOffset = maxOffset + size + dataSize
      }
    }

    return (maxOffset, m)
  }

  def transformOffset(globalMap: HashSMap[ISZ[String], VarInfo],
                      proc: AST.IR.Procedure): (Z, AST.IR.Procedure, HashMap[String, Z]) = {
    val body = proc.body.asInstanceOf[AST.IR.Body.Basic]
    val blocks = body.blocks
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- blocks) yield (b.label, b))
    var blockLocalOffsetMap = HashMap.empty[Z, (Z, HashMap[String, Z])]
    var callResultIdOffsetMap = HashMap.empty[String, Z]
    val offsetParamInfo = procedureParamInfo(PBox(proc))
    var maxOffset = offsetParamInfo._1
    blockLocalOffsetMap = blockLocalOffsetMap + blocks(0).label ~> (maxOffset, HashMap.empty[String, Z] ++
      (for (entry <- offsetParamInfo._2.entries) yield (entry._1, entry._2.offset)))
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
                      copySize(newRhs), newRhs, g.prettyST, tipe, newRhs.tipe, g.pos))
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
                    val lhsOffset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, newRhs.pos)),
                      AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, localOffset, newRhs.pos), newRhs.pos)
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(
                      AST.IR.Exp.Intrinsic(Intrinsic.Load(lhsOffset, isSigned(spType), typeByteSize(spType), st"", spType, pos)),
                      typeByteSize(t), copySize(newRhs), newRhs, st"$lhs = ${newRhs.prettyST}", t, newRhs.tipe, pos))
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
                      copySize(rhs), rhs, g.prettyST, ft, rhs.tipe, pos))
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
                      copySize(newRhs), newRhs, g.prettyST, elementType, newRhs.tipe, g.pos))
                  }
                case g@AST.IR.Stmt.Assign.Temp(n, rhs, pos) =>
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
                      val loffset = m.get(constructResultId(rhs.pos)).get
                      val lhsOffset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, loffset, g.pos),
                        g.pos)
                      grounds = grounds :+ g(rhs = lhsOffset)
                      val sha = sha3Type(rhs.tipe)
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

  def transformHalt(p: AST.IR.Procedure): AST.IR.Procedure = {
    if (!config.stackTrace || !config.shouldPrint) {
      return p
    }
    val id = "printStackTrace"
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      b.jump match {
        case _: AST.IR.Jump.Halt =>
          val pos = b.jump.pos
          blocks = blocks :+ b(grounds = b.grounds ++ ISZ[AST.IR.Stmt.Ground](
            AST.IR.Stmt.Assign.Temp(0, AST.IR.Exp.Type(F, AST.IR.Exp.LocalVarRef(T, p.context, sfCallerId, spType, pos),
              displayIndexType, pos), pos),
            AST.IR.Stmt.Assign.Temp(1, AST.IR.Exp.Apply(T, runtimeName, id, ISZ(
              AST.IR.Exp.GlobalVarRef(displayName, displayType, pos),
              AST.IR.Exp.Intrinsic(Intrinsic.Register(F, dpType, pos)),
              AST.IR.Exp.Int(spType, 0, pos),
              AST.IR.Exp.Int(dpType, dpMask, pos),
              AST.IR.Exp.Int(displayIndexType, spTypeByteSize, pos),
              AST.IR.Exp.Int(displayIndexType, typeByteSize(sfLocType), pos),
              AST.IR.Exp.Int(displayIndexType, typeByteSize(AST.Typed.z), pos),
              AST.IR.Exp.Temp(0, displayIndexType, pos)
            ), runtimeMethodTypeMap.get(id).get, AST.Typed.u64, pos), pos),
            AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, T,
              AST.IR.Exp.Type(F, AST.IR.Exp.Temp(1, AST.Typed.u64, pos), dpType, pos), pos))
          ))
        case _ => blocks = blocks :+ b
      }
    }
    return p(body = body(blocks = blocks))
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
                  anvil.Runtime.printU64Hex(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), value, n)
                  val u8ms = MSZ.create(n, u8"0")
                  for (i <- 0 until n) {
                    u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                  }
                  grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
                } else if (arg.tipe == AST.Typed.c) {
                  val buffer = MS.create[anvil.PrinterIndex.U, U8](4, u8"0")
                  val n = anvil.Runtime.printC(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask),
                    conversions.U32.toC(conversions.Z.toU32(arg.value))).toZ
                  val u8ms = MSZ.create(n, u8"0")
                  for (i <- 0 until n) {
                    u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                  }
                  grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
                } else {
                  val buffer = MS.create[anvil.PrinterIndex.U, U8](20, u8"0")
                  val n: Z =
                    if (isSigned(arg.tipe)) anvil.Runtime.printS64(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), conversions.Z.toS64(arg.value)).toZ
                    else anvil.Runtime.printU64(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), conversions.Z.toU64(arg.value)).toZ
                  val u8ms = MSZ.create(n, u8"0")
                  for (i <- 0 until n) {
                    u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                  }
                  grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
                }
              case arg: AST.IR.Exp.F32 =>
                val buffer = MS.create[anvil.PrinterIndex.U, U8](50, u8"0")
                val n = anvil.Runtime.printF32_2(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), arg.value).toZ
                val u8ms = MSZ.create(n, u8"0")
                for (i <- 0 until n) {
                  u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                }
                grounds = grounds ++ printStringLit(T, conversions.String.fromU8ms(u8ms), arg.pos)
              case arg: AST.IR.Exp.F64 =>
                val buffer = MS.create[anvil.PrinterIndex.U, U8](320, u8"0")
                val n = anvil.Runtime.printF64_2(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), arg.value).toZ
                val u8ms = MSZ.create(n, u8"0")
                for (i <- 0 until n) {
                  u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
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
                    val mt = runtimeMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.c =>
                    val id = "printC"
                    val mt = runtimeMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.z =>
                    val id = "printS64"
                    val mt = runtimeMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, AST.IR.Exp.Type(F, arg, AST.Typed.s64, pos)), mt, mt.ret, pos)
                  case AST.Typed.f32 =>
                    val id = "printF32_2"
                    val mt = runtimeMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.f64 =>
                    val id = "printF64_2"
                    val mt = runtimeMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case AST.Typed.string =>
                    val id = "printString"
                    val mt = runtimeMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, mt.ret, pos)
                  case t if subZOpt(t).nonEmpty =>
                    if (isBitVector(t)) {
                      val digits = AST.IR.Exp.Int(AST.Typed.z, typeByteSize(t) * 2, pos)
                      val id = "printU64Hex"
                      val mt = runtimeMethodTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.u64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.u64, pos)
                      }
                      AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, a, digits), mt, mt.ret, pos)
                    } else if (isSigned(t)) {
                      val id = "printS64"
                      val mt = runtimeMethodTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.s64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.s64, pos)
                      }
                      AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, a), mt, mt.ret, pos)
                    } else {
                      val id = "printU64"
                      val mt = runtimeMethodTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.u64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.u64, pos)
                      }
                      AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, a), mt, mt.ret, pos)
                    }
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
          case g@AST.IR.Stmt.Assign.Temp(lhs, rhs: AST.IR.Exp.Type, pos) if !isScalar(rhs.t) =>
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
                (ISZ(g(rhs = rhs.exp)),
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

  def transformMain(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure, globalSize: Z, globalMap: HashSMap[QName, VarInfo]): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var grounds = ISZ[AST.IR.Stmt.Ground](
      AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(T, F, AST.IR.Exp.Int(spType, globalSize, p.pos), p.pos))
    )
    if (config.stackTrace) {
      val memTypeInfo = globalMap.get(memTypeName).get
      val memSizeInfo = globalMap.get(memSizeName).get
      val sha3t = sha3Type(displayType)
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(typeShaType, memTypeInfo.offset, p.pos), isSigned(typeShaType), typeShaSize,
        AST.IR.Exp.Int(typeShaType, sha3t.toZ, p.pos), st"memory $typeFieldId ($displayType: 0x$sha3t)", typeShaType, p.pos))
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, memSizeInfo.offset, p.pos),
        isSigned(AST.Typed.z), typeByteSize(AST.Typed.z),
        AST.IR.Exp.Int(AST.Typed.z, config.memory, p.pos), st"memory $sizeFieldId", AST.Typed.z, p.pos))
    }
    if (config.shouldPrint) {
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, F, AST.IR.Exp.Int(dpType, 0, p.pos), p.pos))
      val displayInfo = globalMap.get(displayName).get
      val sha3t = sha3Type(displayType)
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(typeShaType, displayInfo.offset + typeByteSize(spType), p.pos), isSigned(typeShaType), typeShaSize,
        AST.IR.Exp.Int(typeShaType, sha3t.toZ, p.pos), st"$displayId.$typeFieldId ($displayType: 0x$sha3t)", typeShaType, p.pos))
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, displayInfo.offset + typeByteSize(spType) + typeByteSize(typeShaType), p.pos),
        isSigned(AST.Typed.z), typeByteSize(AST.Typed.z),
        AST.IR.Exp.Int(AST.Typed.z, dpMask + 1, p.pos), st"$displayId.size", AST.Typed.z, p.pos))
    }
    for (ge <- globalMap.entries) {
      val (name, info) = ge
      if (!info.isScalar) {
        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Int(spType, info.offset, p.pos), isSigned(spType), typeByteSize(spType),
          AST.IR.Exp.Int(spType, info.offset + typeByteSize(spType), p.pos), st"data address of ${(name, ".")} (size = ${typeByteSize(info.tipe)})", spType, p.pos))
      }
    }
    val paramInfo = procedureParamInfo(PBox(p))._2
    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
      AST.IR.Exp.Int(cpType, globalSize + paramInfo.get(returnLocalId).get.offset, p.pos), isSigned(cpType), typeByteSize(cpType),
      AST.IR.Exp.Int(cpType, 0, p.pos), st"$returnLocalId", cpType, p.pos))
    if (p.tipe.ret != AST.Typed.unit) {
      val offset = paramInfo.get(resultLocalId).get.offset
      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, offset, p.pos), isSigned(spType), typeByteSize(spType),
        AST.IR.Exp.Int(spType, offset + typeByteSize(spType), p.pos), st"data address of $resultLocalId (size = ${typeByteSize(p.tipe.ret)})", spType, p.pos))
    }
    for (pid <- p.paramNames) {
      val info = paramInfo.get(pid).get
      if (!isScalar(info.tipe)) {
        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Int(spType, info.offset, p.pos), isSigned(spType), typeByteSize(spType),
          AST.IR.Exp.Int(spType, info.offset + typeByteSize(spType), p.pos), st"data address of $pid (size = ${typeByteSize(info.tipe)})", spType, p.pos))
      }
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
    if (t == AST.Typed.string || isSeq(t)) {
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
    val indexType = t.args(0)
    indexType match {
      case AST.Typed.Name(ISZ(index), _) =>
        Z(index) match {
          case Some(size) => return size
          case _ =>
        }
      case _ =>
    }
    subZOpt(indexType) match {
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
        if (t.ids.size == 1 && t.args.isEmpty && Z(t.ids(0)).nonEmpty) {
          return 8
        }
        if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
          var r: Z = 4 // type sha
          r = r + typeByteSize(AST.Typed.z) // .size
          val et = t.args(1)
          if (et == AST.Typed.b) {
            r = r + getMaxArraySize(t)
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

  @strictpure def sha3Type(t: AST.Typed): U32 = sha3(t.string)

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
      case AST.Typed.Name(ISZ(index), ISZ()) if Z(index).nonEmpty =>
      case _ => return isSubZ(t)
    }
    return T
  }

  @strictpure def signedString(t: AST.Typed): String = if (isSigned(t)) "signed" else "unsigned"

  @pure def copySize(exp: AST.IR.Exp): AST.IR.Exp = {
    val t = exp.tipe
    assert(!isScalar(t))
    val pos = exp.pos
    if (t == AST.Typed.string || (isSeq(t) && !config.erase)) {
      val (sizeType, sizeOffset) = classSizeFieldOffsets(t.asInstanceOf[AST.Typed.Name])._2.get("size").get
      val elementByteSize: Z = if (t == AST.Typed.string) 1 else typeByteSize(t.asInstanceOf[AST.Typed.Name].args(1))
      var elementSize: AST.IR.Exp = AST.IR.Exp.Type(F,
        AST.IR.Exp.Intrinsic(Intrinsic.Load(
          AST.IR.Exp.Binary(spType, exp, AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, sizeOffset, pos), pos),
          isSigned(sizeType), typeByteSize(sizeType), st"", sizeType, pos)),
        spType, pos)
      if (elementByteSize != 1) {
        elementSize = AST.IR.Exp.Binary(spType, elementSize, AST.IR.Exp.Binary.Op.Mul,
          AST.IR.Exp.Int(spType, elementByteSize, pos), pos)
      }
      return AST.IR.Exp.Binary(AST.Typed.u64, elementSize, AST.IR.Exp.Binary.Op.Add,
        AST.IR.Exp.Int(AST.Typed.u64, typeShaSize + typeByteSize(AST.Typed.z), pos), pos)
    } else {
      return AST.IR.Exp.Int(AST.Typed.u64, typeByteSize(t), pos)
    }
  }

  @memoize def minMaxOpt(t: AST.Typed): (Option[Z], Option[Z]) = {
    t match {
      case AST.Typed.z =>
      case AST.Typed.Name(ISZ(index), ISZ()) if Z(index).nonEmpty => return (Some(0), None())
      case _ =>
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
    if (!isScalar(t)) {
      return F
    }
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
      case AST.Typed.Name(ISZ(index), ISZ()) if Z(index).nonEmpty => return F
      case _ =>
        subZOpt(t) match {
          case Some(info) => return info.ast.isSigned
          case _ => halt(s"Infeasible: $t")
        }

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
      case AST.Typed.Name(ISZ(index), ISZ()) if Z(index).nonEmpty => return 0
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
      case info: TypeInfo.Adt if !info.ast.isRoot => r = r :+ sha3Type(t).toZ
      case _ =>
        for (ct <- tsr.typeImpl.descendantsOf(t).elements) {
          th.typeMap.get(ct.ids).get match {
            case info: TypeInfo.Adt if !info.ast.isRoot => r = r :+ sha3Type(ct).toZ
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

  @memoize def getAnnotations(context: AST.IR.MethodContext): ISZ[AST.Annotation] = {
    if (syntheticMethodIds.contains(context.id)) {
      return ISZ()
    }
    if (context.isInObject) {
      return th.nameMap.get(context.owner :+ context.id).get.asInstanceOf[Info.Method].ast.sig.annotations
    } else {
      th.typeMap.get(context.owner).get match {
        case info: TypeInfo.Adt => return info.methods.get(context.id).get.ast.sig.annotations
        case _ => return ISZ()
      }
    }
  }

  @memoize def procedureMod(context: AST.IR.MethodContext): PMod.Type = {
    for (ann <- getAnnotations(context)) {
      if (ann.name == mainAnnName) {
        return PMod.Main
      }
      if (ann.name == testAnnName) {
        return PMod.Test
      }
    }
    return PMod.None
  }

  @memoize def procedureGlobalParamPrefix(context: AST.IR.MethodContext): QName = {
    var r = context.owner
    if (!context.isInObject) {
      r = r :+ "this"
    }
    r = r :+ context.id
    return r
  }

}