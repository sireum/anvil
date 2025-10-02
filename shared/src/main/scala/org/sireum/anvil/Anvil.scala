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

  @datatype class Config(val nameOpt: Option[String],
                         val isFirstGen: B,
                         val memory: Z,
                         val defaultBitWidth: Z,
                         val maxStringSize: Z,
                         val maxArraySize: Z,
                         val customArraySizes: HashMap[AST.Typed, Z],
                         val customConstants: HashMap[QName, AST.Exp],
                         val stackTrace: B,
                         val runtimeCheck: B,
                         val printSize: Z,
                         val copySize: Z,
                         val erase: B,
                         val noXilinxIp: B,
                         val splitTempSizes: B,
                         val tempGlobal: B,
                         val tempLocal: B,
                         val memoryAccess: Config.MemoryAccess.Type,
                         val baseAddress: Z,
                         val alignAxi4: B,
                         val ipMax: Z,
                         val ipSubroutine: B,
                         val cpMax: Z,
                         val genVerilog: B,
                         val simOpt: Option[Config.Sim]) {
    val shouldPrint: B = printSize > 0
    val useIP: B = ipMax >= 0
    val separateCP: B = cpMax > 0
    val padObject64: B = alignAxi4 || memoryAccess == Config.MemoryAccess.BramAxi4 || memoryAccess == Config.MemoryAccess.Ddr
  }

  object Config {

    @enum object MemoryAccess {
      "Default"
      "BramNative"
      "BramAxi4"
      "Ddr"
    }

    @datatype class Sim(val threads: Z, val cycles: Z)

    @strictpure def empty: Config =
      Config(
        nameOpt = None(),
        isFirstGen = T,
        memory = 512 * 1024,
        defaultBitWidth = 64,
        maxStringSize = 100,
        maxArraySize = 100,
        customArraySizes = HashMap.empty,
        customConstants = HashMap.empty,
        stackTrace = F,
        runtimeCheck = F,
        printSize = 0,
        copySize = 8,
        erase = F,
        noXilinxIp = F,
        splitTempSizes = F,
        tempGlobal = T,
        tempLocal = F,
        memoryAccess = Config.MemoryAccess.Default,
        alignAxi4 = F,
        baseAddress = 0,
        ipMax = 0,
        ipSubroutine = F,
        cpMax = 0,
        genVerilog = F,
        simOpt = None())
  }

  @sig trait Output {
    def sbtVersion: String
    def add(isFinal: B, path: => ISZ[String], content: => ST): Unit
    def addPerm(isFinal: B, path: => ISZ[String], content: => ST, mask: String): Unit
  }

  @datatype class VarInfo(val isScalar: B,
                          val loc: Z,
                          val size: Z,
                          val dataSize: Z,
                          val tipe: AST.Typed,
                          val pos: message.Position) {
    @strictpure def totalSize: Z = size + dataSize
  }

  @datatype class IR(val anvil: Anvil,
                     val name: String,
                     val program: AST.IR.Program,
                     val maxRegisters: TempVector,
                     val globalSize: Z,
                     val globalInfoMap: HashSMap[QName, VarInfo],
                     val globalTemps: Z,
                     val procDescMap: HashSMap[U32, String])

  def synthesize(isTest: B, fresh: lang.IRTranslator.Fresh, th: TypeHierarchy, name: QName, config: Config,
                 output: Output, reporter: Reporter): Option[IR] = {
    val rOpt = generateIR(isTest, fresh, th, name, config, output, reporter)
    rOpt match {
      case Some(ir) => HwSynthesizer2(ir.anvil).printProcedure(ir.name, ir.program, output, ir.maxRegisters, ir.globalInfoMap)
      case _ =>
    }
    return rOpt
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
    if (config.alignAxi4) {
      entryPoints = entryPoints :+ TypeSpecializer.EntryPoint.Method(intrinsicName :+ "read")
      entryPoints = entryPoints :+ TypeSpecializer.EntryPoint.Method(intrinsicName :+ "write")
    }
    val tsr = TypeSpecializer.specialize(th, entryPoints, HashMap.empty, reporter)
    if (reporter.hasError) {
      return None()
    }
    fresh.setTemp(0)
    fresh.setLabel(startingLabel)
    return Anvil(tsr.typeHierarchy, tsr, name, config, 0).generateIR(isTest, fresh, output, reporter)
  }

}

import Anvil._

@datatype class Anvil(val th: TypeHierarchy,
                      val tsr: TypeSpecializer.Result,
                      val owner: QName,
                      val config: Config,
                      val numOfLocs: Z) {

  val printer: AST.IR.Printer = AnvilIRPrinter(this, IpAlloc(HashSMap.empty, HashSMap.empty, 0))
  val typeShaType: AST.Typed.Name = AST.Typed.u32
  val typeShaSize: Z = typeByteSize(typeShaType)
  val stringISType: AST.Typed.Name = AST.Typed.Name(AST.Typed.isName, ISZ(spType, AST.Typed.u8))
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

  @strictpure def spType: AST.Typed.Name = Util.spType

  @memoize def cpTypeByteSize: Z = {
    assert(numOfLocs != 0, "Number of locations for CP has not been initialized")
    val n = computeBitwidth(numOfLocs) + 1
    return if (n % 8 == 0) n / 8 else (n / 8) + 1
  }

  @strictpure def irProcedurePath(procedureId: String, pType: AST.Typed.Fun, stage: Z, pass: Z, id: String): ISZ[String] =
    ISZ("ir", "procedures", s"$procedureId-${sha3Type(pType)}", s"$stage-$pass-$id.sir")

  @memoize def isParam(mc: AST.IR.MethodContext, id: String): B = {
    id match {
      case Util.newInitId => return F
      case Util.objInitId => return F
      case string"this" => return T
      case _ =>
    }
    val params: ISZ[AST.Param] = if (mc.isInObject) {
      th.nameMap.get(mc.owner :+ mc.id) match {
        case Some(info: Info.Method) => info.ast.sig.params
        case _ => halt(s"Infeasible: $mc")
      }
    } else {
      th.typeMap.get(mc.owner) match {
        case Some(tinfo: TypeInfo.Adt) => tinfo.methods.get(id).get.ast.sig.params
        case Some(tinfo: TypeInfo.Sig) => tinfo.methods.get(id).get.ast.sig.params
        case _ => halt(s"Infeasible: $mc")
      }
    }
    for (p <- params if p.id.value == id) {
      return T
    }
    return F
  }

  def generateIR(isTest: B, fresh: lang.IRTranslator.Fresh, output: Output, reporter: Reporter): Option[IR] = {
    assert(config.baseAddress < config.memory)
    val threeAddressCode = T
    @strictpure def should3AC(e: AST.IR.Exp): B = e match {
      case _: AST.IR.Exp.Bool => F
      case _: AST.IR.Exp.Int => F
      case _: AST.IR.Exp.F32 => F
      case _: AST.IR.Exp.F64 => F
      case _: AST.IR.Exp.R => F
      case _: AST.IR.Exp.String => F
      case e: AST.IR.Exp.LocalVarRef => config.tempLocal ___>: !(isScalar(e.tipe) || isParam(e.context, e.id))
      case _ => T
    }

    val irt = lang.IRTranslator(
      spec = F,
      threeAddressCode = threeAddressCode,
      threeAddressExpF = should3AC _,
      th = tsr.typeHierarchy,
      fresh = fresh)
    val irtIntrinsic = lang.IRTranslator(
      spec = F,
      threeAddressCode = threeAddressCode,
      threeAddressExpF = (_: AST.IR.Exp) => F,
      th = tsr.typeHierarchy,
      fresh = fresh)

    var stage: Z = 0

    var testProcs = ISZ[AST.IR.Procedure]()
    var mainProcs = ISZ[AST.IR.Procedure]()

    val mq: (AST.IR.MethodContext, AST.IR.Program, Z, HashSMap[ISZ[String], VarInfo], Z) = {
      var globals = ISZ[AST.IR.Global]()
      var procedures = ISZ[AST.IR.Procedure]()

      var startOpt = Option.none[AST.IR.Procedure]()
      for (ms <- tsr.methods.values; m <- ms.elements) {
        val receiverOpt: Option[AST.Typed] = m.receiverOpt match {
          case Some(t) => Some(t)
          case _ => None()
        }
        val p = (if (m.info.owner == intrinsicName) irtIntrinsic else irt).
          translateMethod(F, receiverOpt, m.info.owner, m.info.ast)
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
        val tempL = AST.IR.Exp.Temp(tempNum + 1, AST.Typed.b, pos)
        val tempR = AST.IR.Exp.Temp(tempNum + 2, AST.Typed.b, pos)
        val zero = AST.IR.Exp.Int(AST.Typed.z, 0, pos)
        var i: Z = 0
        for (p <- testProcs) {
          stmts = stmts :+ AST.IR.Stmt.Assign.Temp(tempL.n, AST.IR.Exp.Binary(AST.Typed.b, temp, AST.IR.Exp.Binary.Op.Lt, zero, pos), pos)
          stmts = stmts :+ AST.IR.Stmt.Assign.Temp(tempR.n, AST.IR.Exp.Binary(AST.Typed.b, temp, AST.IR.Exp.Binary.Op.Eq, AST.IR.Exp.Int(AST.Typed.z, i, pos), pos), pos)
          stmts = stmts :+ AST.IR.Stmt.Assign.Temp(tempL.n, AST.IR.Exp.Binary(
            AST.Typed.b,
            AST.IR.Exp.Temp(tempL.n, AST.Typed.b, pos),
            AST.IR.Exp.Binary.Op.Or,
            AST.IR.Exp.Temp(tempR.n, AST.Typed.b, pos),
            pos), pos)
          stmts = stmts :+ AST.IR.Stmt.If(tempL,
            AST.IR.Stmt.Block(ISZ(
              AST.IR.Stmt.Expr(AST.IR.Exp.Apply(T, p.context.owner, p.context.id, ISZ(), p.tipe, pos))
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
      for (ts <- tsr.nameTypes.values; nt <- ts.elements) {
        val t = nt.tpe
        val stmts = classInit(t)
        if (stmts.nonEmpty) {
          val posOpt = th.typeMap.get(t.ids).get.posOpt
          val p = irt.translateMethodH(F, Some(t), t.ids, newInitId, ISZ(),
            ISZ(), AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.unit), posOpt.get,
            Some(AST.Body(stmts, ISZ())))
          procedures = procedures :+ p
        }
      }
      val startPos = startOpt.get.pos
      if (config.stackTrace) {
        globals = globals :+ AST.IR.Global(spType, memName, startPos)
        globals = globals :+ AST.IR.Global(typeShaType, memTypeName, startPos)
        globals = globals :+ AST.IR.Global(AST.Typed.z, memSizeName, startPos)
      }
      if (isTest) {
        val rem = typeByteSize(spType) + typeShaSize % 8
        if (config.alignAxi4 && config.stackTrace && rem != 0) {
          val fillerType: AST.Typed = rem match {
            case z"1" => AST.Typed.Name(AST.Typed.sireumName :+ "U56", ISZ())
            case z"2" => AST.Typed.Name(AST.Typed.sireumName :+ "U48", ISZ())
            case z"3" => AST.Typed.Name(AST.Typed.sireumName :+ "U40", ISZ())
            case z"4" => AST.Typed.u32
            case z"5" => AST.Typed.Name(AST.Typed.sireumName :+ "U24", ISZ())
            case z"6" => AST.Typed.u16
            case z"7" => AST.Typed.u8
            case _ => halt("Infeasible")
          }
          globals = globals :+ AST.IR.Global(fillerType, testNumNamePad, startPos)
        }
        globals = globals :+ AST.IR.Global(AST.Typed.z, testNumName, startPos)
      }
      if (config.shouldPrint) {
        globals = globals :+ AST.IR.Global(displayType, displayName, startPos)
        if (!config.isFirstGen) {
          globals = globals :+ AST.IR.Global(dpType, dpName, startPos)
        }
        for (id <- runtimePrintMethodTypeMap.keys) {
          val info = th.nameMap.get(runtimeName :+ id).get.asInstanceOf[Info.Method]
          procedures = procedures :+ irt.translateMethod(F, None(), info.owner, info.ast)
        }
      }
      if (config.stackTrace && !config.shouldPrint) {
        for (id <- ISZ("printStackTrace", "load")) {
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

      if (!config.isFirstGen) {
        for (p <- procedures) {
          val context = p.context.owner :+ p.context.id
          for (idt <- ops.ISZOps(p.paramNames).zip(p.tipe.args)) {
            var t = idt._2
            if (!isScalar(t)) {
              t = spType
            }
            globals = globals :+ AST.IR.Global(t, context :+ idt._1, p.pos)
          }
          val rt = p.tipe.ret
          if (rt != AST.Typed.unit) {
            globals = globals :+ AST.IR.Global(rt, context :+ resultLocalId, p.pos)
          }
        }
      }

      var globalMap = HashSMap.empty[ISZ[String], VarInfo]
      var globalTemps = 0
      var globalSize: Z = config.baseAddress
      for (g <- globals) {
        val size = typeByteSize(g.tipe)
        val scalar = isScalar(g.tipe)
        if (isTempGlobal(this, g.tipe, g.name)) {
          globalMap = globalMap + g.name ~> VarInfo(scalar, globalTemps, size, 0, g.tipe, g.pos)
          globalTemps = globalTemps + 1
        } else {
          globalMap = globalMap + g.name ~> VarInfo(scalar, globalSize, size, 0, g.tipe, g.pos)
          globalSize = globalSize + size
        }
      }

      def genTraitMethod(method: TypeSpecializer.SMethod): Unit = {
        val info: Info.Method = th.typeMap.get(method.owner).get match {
          case inf: TypeInfo.Sig =>
            if (!inf.ast.isExt) {
              return
            }
            inf.methods.get(method.id).get
          case inf: TypeInfo.Adt =>
            inf.methods.get(method.id).get
          case _ => halt("Infeasible")
        }
        def findMethod(receiver: AST.Typed.Name): Info.Method = {
          val adtInfo = tsr.typeHierarchy.typeMap.get(receiver.ids).get.asInstanceOf[TypeInfo.Adt]
          val adtSm =
            TypeChecker.buildTypeSubstMap(receiver.ids, None(), adtInfo.ast.typeParams, receiver.args, reporter).get
          val mInfo = adtInfo.methods.get(method.id).get
          val mt = mInfo.methodType.tpe.subst(adtSm)
          val rep = Reporter.create
          val th = tsr.typeHierarchy
          for (m <- tsr.methods.get(receiver.ids).get.elements if m.info.ast.sig.id.value == method.id) {
            val smOpt = TypeChecker.unify(th, None(), TypeChecker.TypeRelation.Equal, m.info.methodType.tpe, mt, rep)
            if (smOpt.nonEmpty) {
              return m.info
            }
          }
          halt(s"Infeasible: $method of $receiver}")
        }
        val receiver = method.receiverOpt.get
        val methodContext = AST.IR.MethodContext(F, info.owner, method.id, method.tpe(args = receiver +: method.tpe.args))
        var impls = ISZ[(Z, AST.Typed.Name, AST.IR.Exp)]()
        val pos = info.posOpt.get
        val paramNames: ISZ[String] = "this" +: (for (p <- info.ast.sig.params) yield p.id.value)
        fresh.setTemp(0)
        val label = fresh.label()
        val thiz = AST.IR.Exp.Temp(fresh.temp(), receiver, pos)
        for (t <- tsr.typeImpl.childrenOf(receiver).elements) {
          val adt = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
          adt.vars.get(method.id) match {
            case Some(_) =>
              impls = impls :+ (fresh.label(), t, AST.IR.Exp.FieldVarRef(thiz, method.id, method.tpe.ret, pos))
            case _ =>
              val minfo = findMethod(t)
              var args = ISZ[AST.IR.Exp]()
              val pt = minfo.ast.sig.funType(args = t +: minfo.ast.sig.funType.args)
              for (ptt <- ops.ISZOps(paramNames).zip(ops.ISZOps(methodContext.t.args).zip(pt.args))) {
                val (id, (paramType , argType)) = ptt
                val mpos = minfo.posOpt.get
                var arg: AST.IR.Exp = AST.IR.Exp.LocalVarRef(T, methodContext, id, paramType, mpos)
                if (argType != paramType) {
                  arg = AST.IR.Exp.Type(F, arg, argType.asInstanceOf[AST.Typed.Name], mpos)
                }
                args = args :+ arg
              }
              impls = impls :+ (fresh.label(), t, AST.IR.Exp.Apply(F, minfo.owner, method.id, args, pt, pos))
          }
        }
        var blocks = ISZ[AST.IR.BasicBlock](
          AST.IR.BasicBlock(label, ISZ(
            AST.IR.Stmt.Assign.Temp(thiz.n,
              AST.IR.Exp.LocalVarRef(T, methodContext, "this", methodContext.receiverType, pos), pos)
          ), AST.IR.Jump.Switch(
            AST.IR.Exp.FieldVarRef(thiz, typeFieldId, typeShaType, pos),
            for (impl <- impls) yield AST.IR.Jump.Switch.Case(
              AST.IR.Exp.Int(typeShaType, sha3Type(impl._2).toZ, pos), impl._1),
            None(), pos
          ))
        )
        val temp = fresh.temp()
        for (impl <- impls) {
          val (lbl, _, exp) = impl
          if (method.tpe.ret == AST.Typed.unit) {
            blocks = blocks :+ AST.IR.BasicBlock(lbl, ISZ(AST.IR.Stmt.Expr(exp.asInstanceOf[AST.IR.Exp.Apply])),
              AST.IR.Jump.Return(None(), exp.pos))
          } else {
            var r = exp
            if (methodContext.t.ret != exp.tipe) {
              r = AST.IR.Exp.Type(F, r, methodContext.t.ret.asInstanceOf[AST.Typed.Name], exp.pos)
            }
            blocks = blocks :+ AST.IR.BasicBlock(lbl, ISZ(
              AST.IR.Stmt.Assign.Temp(temp, r, exp.pos)
            ), AST.IR.Jump.Return(Some(AST.IR.Exp.Temp(temp, exp.tipe, exp.pos)), exp.pos))
          }
        }
        procedures = procedures :+ AST.IR.Procedure(F, ISZ(), method.owner, method.id, paramNames, methodContext.t,
          AST.IR.Body.Basic(blocks), pos)
      }

      for (method <- tsr.traitMethods.elements) {
        genTraitMethod(method)
      }

      globalSize = pad64(globalSize)

      (startOpt.get.context, AST.IR.Program(threeAddressCode, globals, procedures), globalSize, globalMap, globalTemps)
    }

    val startContext = mq._1
    var program = mq._2
    val globalSize = mq._3
    var globalMap = mq._4
    var globalTemps = mq._5
    val procDescMap = HashSMap.empty[U32, String] ++
      (for (p <- program.procedures) yield (sha3(procedureDesc(PBox(p))), procedureDesc(PBox(p))))

    output.add(F, ISZ("ir", s"$stage-initial.sir"), program.prettyST(printer))

    stage = stage + 1

    program = program(procedures = ops.ISZOps(program.procedures).mParMap(
      (p: AST.IR.Procedure) => transformBlock(stage, output, p)))

    program = program(procedures = for (p <- program.procedures) yield
      p(body = irt.toBasic(p.body.asInstanceOf[AST.IR.Body.Block], p.pos)))

    output.add(F, ISZ("ir", s"$stage-basic.sir"), program.prettyST(printer))

    stage = stage + 1

    program = transformBasicBlock(stage, fresh, program, output)
    output.add(F, ISZ("ir", s"$stage-transformed.sir"), program.prettyST(printer))

    stage = stage + 1

    val numOfLocs: Z = ops.ISZOps(for (p <- program.procedures)
      yield p.body.asInstanceOf[AST.IR.Body.Basic].blocks.size).foldLeft[Z]((r: Z, n: Z) => r + n, 0)
    val anvil = Anvil(th, tsr, owner, config, numOfLocs + 1)

    var procedureMap = HashSMap.empty[AST.IR.MethodContext, AST.IR.Procedure]
    var procedureSizeMap = HashMap.empty[AST.IR.MethodContext, Z]
    var callResultOffsetMap = HashMap.empty[String, Z]
    program = {
      for (p <- program.procedures) {
        var proc = p
        var pass: Z = 0

        if (config.tempLocal) {
          proc = anvil.transformTempNum(proc)
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "temp-num"), proc.prettyST(anvil.printer))
          pass = pass + 1

          proc = anvil.transformLocal(proc)
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "local"), proc.prettyST(anvil.printer))
          pass = pass + 1
        }

        val (maxOffset, p2, m) = anvil.transformOffset(globalMap, proc)
        callResultOffsetMap = callResultOffsetMap ++ m.entries
        proc = p2
        output.add(F, irProcedurePath(proc.id, proc.tipe, stage, pass, "offset"), proc.prettyST(anvil.printer))
        pass = pass + 1

        proc = anvil.transformStackTraceDesc(fresh, proc)
        output.add(F, irProcedurePath(proc.id, proc.tipe, stage, pass, "stack-frame-desc"), proc.prettyST(anvil.printer))
        pass = pass + 1

        procedureMap = procedureMap + proc.context ~> proc
        procedureSizeMap = procedureSizeMap + p2.context ~> maxOffset
      }
      program(procedures = procedureMap.values)
    }
    output.add(F, ISZ("ir", s"$stage-offset.sir"), program.prettyST(anvil.printer))

    stage = stage + 1

    val main = procedureMap.get(startContext).get
    if (config.isFirstGen) {
      program = {
        val p = transformMainStackFrame(main)(body = main.body.asInstanceOf[AST.IR.Body.Basic](blocks =
          anvil.mergeProcedures(main, fresh, procedureMap, procedureSizeMap, callResultOffsetMap)))
        output.add(F, irProcedurePath(p.id, p.tipe, stage, 0, "merged"), p.prettyST(anvil.printer))
        program(procedures = ISZ(p))
      }
      output.add(F, ISZ("ir", s"$stage-merged.sir"), program.prettyST(anvil.printer))
    }

    stage = stage + 1

    program = {
      var procedures = ISZ[AST.IR.Procedure]()
      for (i <- program.procedures.indices) {
        var p = program.procedures(i)
        var pass: Z = 0

        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "merged"), p.prettyST(anvil.printer))

        @strictpure def isRegisterInc(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = g match {
          case AST.IR.Stmt.Intrinsic(in: Intrinsic.RegisterAssign) if in.isInc =>
            grounds.isEmpty ||
              ops.ISZOps(grounds).exists((ground: AST.IR.Stmt.Ground) => !ground.isInstanceOf[AST.IR.Stmt.Decl])
          case _ => F
        }

        p = anvil.transformSplitTest(F, fresh, p, isRegisterInc _)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "register-inc"), p.prettyST(anvil.printer))
        pass = pass + 1

        @pure def isCopyStoreLoad(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = {
          g match {
            case AST.IR.Stmt.Intrinsic(_: Intrinsic.Copy) => return T
            case AST.IR.Stmt.Intrinsic(in: Intrinsic.Store) => return in.bytes > 1 && in.tipe != cpType
            case AST.IR.Stmt.Intrinsic(in: Intrinsic.TempLoad) => return in.bytes > 1 && in.tipe != cpType
            case _ => return F
          }
        }

        p = anvil.transformSplitTest(F, fresh, p, isCopyStoreLoad _)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-copy-store-load"), p.prettyST(anvil.printer))
        pass = pass + 1

        p = anvil.transformIndexing(fresh, p)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-indexing"), p.prettyST(anvil.printer))
        pass = pass + 1

        p = anvil.transformSCreate(fresh, p, programMaxTemps(anvil, AST.IR.Program(T, ISZ(), ISZ(p))))
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "s-create"), p.prettyST(anvil.printer))
        pass = pass + 1

        p = anvil.transformGotoLocal(fresh, p, programMaxTemps(anvil, AST.IR.Program(T, ISZ(), ISZ(p))))
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "goto-local"), p.prettyST(anvil.printer))
        pass = pass + 1

        val maxTemps = programMaxTemps(anvil, AST.IR.Program(T, ISZ(), ISZ(p)))

        p = anvil.transformIfLoadStoreCopyIntrinsic(fresh, p, maxTemps)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "load-store-copy"), p.prettyST(anvil.printer))
        pass = pass + 1

        config.memoryAccess match {
          case Anvil.Config.MemoryAccess.Default =>
            if (config.useIP) {
              p = anvil.transformCopyDefaultIp(fresh, p, maxTemps)
              output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "copy-access"), p.prettyST(anvil.printer))
              pass = pass + 1
            }

          case Anvil.Config.MemoryAccess.BramNative =>
          case Anvil.Config.MemoryAccess.BramAxi4 =>
          case Anvil.Config.MemoryAccess.Ddr =>
        }

        p = anvil.transformErase(fresh, p)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "erase"), p.prettyST(anvil.printer))
        pass = pass + 1

        if (p.context == main) {
          p = anvil.transformMain(fresh, p, globalSize, globalMap)
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "main"), p.prettyST(anvil.printer))
          pass = pass + 1
        }

        p = anvil.transformAssignTempLoad(fresh, p)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "assign-temp-load"), p.prettyST(anvil.printer))
        pass = pass + 1

        if (config.tempGlobal && config.ipSubroutine) {
          @pure def hasBinop(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = {
            val bd = BinopDetector(F)
            bd.transform_langastIRStmtGround(g)
            return bd.hasBinop
          }

          p = anvil.transformSplitTest(T, fresh, p, hasBinop _)
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-ips"), p.prettyST(anvil.printer))
          pass = pass + 1

          val pair = anvil.transformIpSubroutines(fresh, p, globalMap)
          globalTemps = globalTemps + pair._2.size - globalMap.size
          globalMap = pair._2
          p = pair._1
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "ip-subroutines"), p.prettyST(anvil.printer))
          pass = pass + 1
        }

        if (config.tempGlobal && config.alignAxi4) {
          @pure def isStoreLoadAlign(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = {
            g match {
              case AST.IR.Stmt.Intrinsic(_: Intrinsic.Store) => return T
              case AST.IR.Stmt.Intrinsic(_: Intrinsic.TempLoad) => return T
              case _ => return F
            }
          }

          p = anvil.transformSplitTest(F, fresh, p, isStoreLoadAlign _)
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "align-copy-store-load"), p.prettyST(anvil.printer))
          pass = pass + 1

          p = anvil.transformReadWriteAlign(fresh, p, procedureMap)
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "rw-align"), p.prettyST(anvil.printer))
          pass = pass + 1
        }

        if (!config.isFirstGen) {
          p = anvil.transformSecondGenSplit(fresh, p)
          output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "second-gen-split"), p.prettyST(anvil.printer))
          pass = pass + 1
        }

        p = anvil.transformEmptyBlock(p)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "empty-block"), p.prettyST(anvil.printer))
        pass = pass + 1

        p = anvil.transformCP(p)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "cp"), p.prettyST(anvil.printer))
        pass = pass + 1

        procedures = procedures :+ p
      }
      program(procedures = procedures)
    }

    {
      val emc = ExtMethodCollector(anvil, HashSMap.empty)
      emc.transform_langastIRProgram(program)
      for (pair <- emc.nameMap.entries) {
        val (name, poss) = pair
        for (pos <- poss) {
          reporter.error(Some(pos), kind, st"Extension method ${(name, ".")} is not currently handled".render)
        }
      }
    }

    val maxRegisters = programMaxTemps(anvil, program)

    val header: ST = {
      var globalParamSTs = ISZ[ST]()
      for (entry <- anvil.procedureParamInfo(PBox(main))._2.entries) {
        globalParamSTs = globalParamSTs :+ st"- parameter ${entry._1}: ${entry._2.tipe} @[offset = ${entry._2.loc}, size = ${entry._2.size}, data-size = ${entry._2.dataSize}]"
      }
      for (pair <- globalMap.entries) {
        val (name, info) = pair
        globalParamSTs = globalParamSTs :+ st"- global ${(name, ".")}: ${info.tipe} @[offset = ${info.loc}, size = ${info.size}, data-size = ${info.dataSize}]"
      }
      st"""/*
          |   Note that globalSize = $globalSize and maxRegisters = $maxRegisters
          |   Initially:
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

    val printer2: AST.IR.Printer =
      if (config.useIP) AnvilIRPrinter(anvil, ipAlloc(anvil, program.procedures(0), 10)) else anvil.printer
    output.add(F, ISZ("ir", s"$stage-reordered.sir"),
      st"""$header
          |${program.prettyST(printer2)}""")

    stage = stage + 1

    {
      val nlocs = program.procedures(0).body.asInstanceOf[AST.IR.Body.Basic].blocks.size
      val cpMax = pow(2, anvil.typeByteSize(cpType) * 8)
      assert(nlocs <= cpMax, s"nlocs ($nlocs) > cpMax (2 ** (${anvil.typeByteSize(cpType) * 8}) == $cpMax)")
    }

    val name: String = config.nameOpt match {
      case Some(id) => id
      case _ =>
        var id = st"${(for (p <- mainProcs) yield ops.StringOps(p.id).firstToUpper, "")}".render
        if (isTest) {
          id = s"${id}Test"
        }
        id
    }

    WellFormedChecker().transform_langastIRProcedure(program.procedures(0))

    return Some(IR(anvil, name, program, maxRegisters, globalSize, globalMap, globalTemps, procDescMap))
  }

  def transformReadWriteAlign(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure,
                              procedureMap: HashSMap[AST.IR.MethodContext, AST.IR.Procedure]): AST.IR.Procedure = {
    val ifType = AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.u64)
    @pure def intrinsicBlocks(name: QName): ISZ[AST.IR.BasicBlock] = {
      return procedureMap.get(AST.IR.MethodContext(T, intrinsicName, name(name.size - 1), ifType))
        .get.body.asInstanceOf[AST.IR.Body.Basic].blocks
    }
    val leftShiftBlocks = intrinsicBlocks(leftShiftName)
    val rightShiftBlocks = intrinsicBlocks(rightShiftName)
    val readBlocks = intrinsicBlocks(readName)
    val writeBlocks = intrinsicBlocks(writeName)

    @strictpure def toU64(e: AST.IR.Exp): AST.IR.Exp = if (e.tipe == AST.Typed.u64) e else AST.IR.Exp.Type(F, e,
      AST.Typed.u64, e.pos)

    @pure def updateIntrinsic(b: AST.IR.BasicBlock): ISZ[AST.IR.BasicBlock] = {
      b.jump match {
        case AST.IR.Jump.Return(Some(e: AST.IR.Exp.GlobalVarRef), _) =>
          return ISZ(b(jump = AST.IR.Jump.Intrinsic(Intrinsic.GotoGlobal(e.name, b.jump.pos))))
        case _ =>
          b.grounds match {
            case ISZ(AST.IR.Stmt.Expr(e)) if e.isInObject && e.owner == intrinsicName =>
              val pos = e.pos
              val intrinsicLabel: Z = e.id match {
                case `leftShiftId` => leftShiftBlocks(0).label
                case `rightShiftId` => rightShiftBlocks(0).label
                case `readAlignId` => return ISZ(b(grounds = ISZ(AST.IR.Stmt.Intrinsic(Intrinsic.AlignRw(T, pos)))))
                case `writeAlignId` => return ISZ(b(grounds = ISZ(AST.IR.Stmt.Intrinsic(Intrinsic.AlignRw(F, pos)))))
              }
              val label = fresh.label()
              val label2 = fresh.label()
              val retId = s"${e.id}Ret"
              return ISZ(
                AST.IR.BasicBlock(b.label, ISZ(AST.IR.Stmt.Assign.Global(intrinsicName :+ retId, AST.Typed.u64,
                    toU64(AST.IR.Exp.Int(cpType, label2, b.jump.pos)), pos)), AST.IR.Jump.Goto(label, pos)),
                AST.IR.BasicBlock(label, ISZ(), AST.IR.Jump.Goto(intrinsicLabel, pos)),
                AST.IR.BasicBlock(label2, ISZ(), b.jump)
              )
            case _ =>
          }
      }
      return ISZ(b)
    }

    @pure def updateRwIntrinsic(b: AST.IR.BasicBlock): ISZ[AST.IR.BasicBlock] = {
      @strictpure def wrapU64(n: Z): Z = if (n < 0) n + U64.Max.toZ else n
      b.grounds match {
        case ISZ(AST.IR.Stmt.Intrinsic(in: Intrinsic.TempLoad)) =>
          val pos = in.pos
          val label = fresh.label()
          val label2 = fresh.label()
          val grounds = ISZ[AST.IR.Stmt.Ground](
            AST.IR.Stmt.Assign.Global(readBaseAddr, AST.Typed.u64, toU64(in.base), pos),
            AST.IR.Stmt.Assign.Global(readOffset, AST.Typed.u64, AST.IR.Exp.Int(AST.Typed.u64, wrapU64(in.offset), pos), pos),
            AST.IR.Stmt.Assign.Global(readLen, AST.Typed.u64, AST.IR.Exp.Int(AST.Typed.u64, in.bytes, pos), pos),
            AST.IR.Stmt.Assign.Global(readRet, AST.Typed.u64, toU64(AST.IR.Exp.Int(cpType, label2, pos)), pos)
          )
          var rhs: AST.IR.Exp = AST.IR.Exp.GlobalVarRef(readRes, AST.Typed.u64, pos)
          if (in.tipe != AST.Typed.u64) {
            rhs = AST.IR.Exp.Type(F, rhs, in.tipe.asInstanceOf[AST.Typed.Name], pos)
          }
          return ISZ(
            b(grounds = grounds, jump = AST.IR.Jump.Goto(label, pos)),
            AST.IR.BasicBlock(label, ISZ(), AST.IR.Jump.Goto(readBlocks(0).label, pos)),
            AST.IR.BasicBlock(label2, ISZ(AST.IR.Stmt.Assign.Temp(in.temp, rhs, pos)), b.jump)
          )
        case ISZ(AST.IR.Stmt.Intrinsic(in: Intrinsic.Store)) =>
          val pos = in.pos
          val label = fresh.label()
          val label2 = fresh.label()
          val grounds = ISZ[AST.IR.Stmt.Ground](
            AST.IR.Stmt.Assign.Global(writeBaseAddr, AST.Typed.u64, toU64(in.base), pos),
            AST.IR.Stmt.Assign.Global(writeOffset, AST.Typed.u64, AST.IR.Exp.Int(AST.Typed.u64, wrapU64(in.offset), pos), pos),
            AST.IR.Stmt.Assign.Global(writeLen, AST.Typed.u64, AST.IR.Exp.Int(AST.Typed.u64, in.bytes, pos), pos),
            AST.IR.Stmt.Assign.Global(writeValue, AST.Typed.u64, toU64(in.rhs), pos),
            AST.IR.Stmt.Assign.Global(writeRet, AST.Typed.u64, toU64(AST.IR.Exp.Int(cpType, label2, pos)), pos)
          )
          return ISZ(
            b(grounds = grounds, jump = AST.IR.Jump.Goto(label, pos)),
            AST.IR.BasicBlock(label, ISZ(), AST.IR.Jump.Goto(writeBlocks(0).label, pos)),
            AST.IR.BasicBlock(label2, ISZ(), b.jump)
          )
        case _ =>
      }
      return ISZ(b)
    }

    val body = p.body.asInstanceOf[AST.IR.Body.Basic]

    var blocks = ISZ[AST.IR.BasicBlock]()

    for (b <- body.blocks; b2 <- updateRwIntrinsic(b)) {
      blocks = blocks :+ b2
    }
    for (b <- leftShiftBlocks; b2 <- updateIntrinsic(b)) {
      blocks = blocks :+ b2
    }
    for (b <- rightShiftBlocks; b2 <- updateIntrinsic(b)) {
      blocks = blocks :+ b2
    }
    for (b <- readBlocks; b2 <- updateIntrinsic(b)) {
      blocks = blocks :+ b2
    }
    for (b <- writeBlocks; b2 <- updateIntrinsic(b)) {
      blocks = blocks :+ b2
    }
    return p(body = body(blocks = blocks))
  }

  def transformAssignTempLoad(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var block = b
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case g: AST.IR.Stmt.Assign.Temp =>
            g.rhs match {
              case AST.IR.Exp.Intrinsic(in: Intrinsic.Load) =>
                grounds = grounds :+ AST.IR.Stmt.Intrinsic(
                  Intrinsic.TempLoad(g.lhs, in.base, in.offset, in.isSigned, in.bytes, in.comment, in.tipe, in.pos))
              case rhs@AST.IR.Exp.Type(_, AST.IR.Exp.Intrinsic(in: Intrinsic.Load), _, _) =>
                grounds = grounds :+ AST.IR.Stmt.Intrinsic(
                  Intrinsic.TempLoad(g.lhs, in.base, in.offset, in.isSigned, in.bytes, in.comment, in.tipe, in.pos))
                val label = fresh.label()
                blocks = blocks :+ b(grounds = grounds, jump = AST.IR.Jump.Goto(label, rhs.pos))
                grounds = ISZ(AST.IR.Stmt.Assign.Temp(g.lhs, rhs(exp = AST.IR.Exp.Temp(g.lhs, in.tipe, in.pos)), rhs.pos))
                block = AST.IR.BasicBlock(label, grounds, block.jump)
              case _ => grounds = grounds :+ g
            }
          case _ => grounds = grounds :+ g
        }
      }
      blocks = blocks :+ block(grounds = grounds)
    }
    return p(body = body(blocks = blocks))
  }

  @pure def transformBlock(stage: Z, output: Output, p: AST.IR.Procedure): AST.IR.Procedure = {
    var pass: Z = 0
    var r = p

    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "initial"), r.prettyST(printer))
    pass = pass + 1

    r = ConversionsTransformer(this).transform_langastIRProcedure(r).getOrElse(r)
    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "conversions"), r.prettyST(printer))
    pass = pass + 1

    val tc = TempCollector(T, HashSMap.empty)
    tc.transform_langastIRProcedure(r)
    var max: Z = 0
    for (k <- tc.r.keys if max < k) {
      max = k
    }
    r = if (p.owner == runtimeName) r else RuntimeCheckInserter(this, max + 1).transform_langastIRProcedure(r).getOrElse(r)
    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "runtime-check"), r.prettyST(printer))
    pass = pass + 1

    r = StmtFilter(this).transform_langastIRProcedure(r).getOrElse(r)
    output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "stmt-filter"), r.prettyST(printer))
    pass = pass + 1

    return r
  }

  def transformSecondGenCall(p: AST.IR.Procedure, procedureMap: HashSMap[AST.IR.MethodContext, AST.IR.Procedure]): AST.IR.Procedure = {
    if (config.isFirstGen) {
      return p
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      def addParamArgAssigns(e: AST.IR.Exp.Apply): ISZ[String] = {
        val mc = AST.IR.MethodContext(e.isInObject, e.owner, e.id, e.methodType)
        val called = procedureMap.get(mc).get
        val calledContext = e.owner :+ e.id
        for (pArg <- ops.ISZOps(ops.ISZOps(called.paramNames).zip(called.tipe.args)).zip(e.args)) {
          val ((id, t), arg) = pArg
          grounds = grounds :+ AST.IR.Stmt.Assign.Global(calledContext :+ id, if (isScalar(t)) t else spType, arg, arg.pos)
        }
        return calledContext
      }
      var jump = b.jump
      for (g <- b.grounds) {
        g match {
          case AST.IR.Stmt.Expr(e) =>
            addParamArgAssigns(e)
            grounds = grounds :+ AST.IR.Stmt.Expr(e(args = ISZ()))
          case g@AST.IR.Stmt.Assign.Temp(_, e: AST.IR.Exp.Apply, _) =>
            val context = addParamArgAssigns(e)
            grounds = grounds :+ AST.IR.Stmt.Expr(e(args = ISZ()))
            grounds = grounds :+ g(rhs = AST.IR.Exp.GlobalVarRef(context :+ resultLocalId, e.tipe, g.pos))
          case _ =>
            grounds = grounds :+ g
        }
      }
      jump match {
        case j@AST.IR.Jump.Return(Some(e), _) =>
          grounds = grounds :+ AST.IR.Stmt.Assign.Global(p.owner :+ p.id :+ resultLocalId, p.tipe.ret, e, j.pos)
          jump = j(expOpt = None())
        case _ =>
      }
      blocks = blocks :+ b(grounds = grounds, jump = jump)
    }
    return p(body = body(blocks = blocks))
  }

  def transformSecondGenSplit(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    if (config.isFirstGen) {
      return p
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      val ic = IpCounter(this, HashSMap.empty, HashSMap.empty, 0)
      ic.transform_langastIRBasicBlock(b)
      if (ic.ipMap.size > 1) {
        var groundss = ISZ[ISZ[AST.IR.Stmt.Ground]]()
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        var found = F
        for (g <- b.grounds) {
          g match {
            case AST.IR.Stmt.Intrinsic(_: Intrinsic.Decl) => grounds = grounds :+ g
            case _ =>
              if (found) {
                found = F
                groundss = groundss :+ grounds
                grounds = ISZ()
              }
              grounds = grounds :+ g
              found = T
          }
        }
        if (grounds.nonEmpty) {
          groundss = groundss :+ grounds
        }
        if (groundss.size <= 1) {
          blocks = blocks :+ b
        } else {
          var label = b.label
          var next = fresh.label()
          for (i <- 0 until groundss.size - 1) {
            val gs = groundss(i)
            blocks = blocks :+ AST.IR.BasicBlock(label, gs, AST.IR.Jump.Goto(next, gs(gs.size - 1).pos))
            label = next
            next = fresh.label()
          }
          blocks = blocks :+ AST.IR.BasicBlock(label, groundss(groundss.size - 1), b.jump)
        }
      } else {
        blocks = blocks :+ b
      }
    }
    return p(body = body(blocks = blocks))
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
            case Some(j2) =>
              j2 match {
                case _: AST.IR.Jump.Intrinsic => j(label = l)
                case _ => j2
              }
            case _ => j(label = l)
          }
        case j: AST.IR.Jump.Return => j
        case j: AST.IR.Jump.Intrinsic => j
        case j: AST.IR.Jump.Halt => j
      }
      blockMap = blockMap + b.label ~> b(jump = jump)
    }
    val delBlockLabels: ISZ[Z] = (for (labelIncomings <- countNumOfIncomingJumps(blockMap.values).entries
                                       if labelIncomings._2 == 0) yield labelIncomings._1) -- ISZ(0, 1, body.blocks(0).label)
    blockMap = blockMap -- delBlockLabels
    return p(body = body(blocks = blockMap.values))
  }

  def transformSplitTempJump(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      if (b.grounds.isEmpty) {
        blocks = blocks :+ b
      } else {
        val tc = TempCollector(F, HashSMap.empty)
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

  def transformGotoLocal(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure, maxTemps: TempVector): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    val cpt: AST.Typed = if (config.splitTempSizes) cpType else AST.Typed.u64
    val temp = maxTemps.typeCount(this, cpt)
    for (b <- body.blocks) {
      b.jump match {
        case AST.IR.Jump.Intrinsic(in: Intrinsic.GotoLocal) if b.grounds.nonEmpty || !in.isTemp =>
          val label = fresh.label()
          blocks = blocks :+ b(jump = AST.IR.Jump.Goto(label, in.pos))
          if (in.isTemp) {
            blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(), b.jump)
          } else {
            val label2 = fresh.label()
            blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp,
              AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, in.pos)), in.loc, isSigned(cpType),
              typeByteSize(cpType), st"", cpType, in.pos
            ))), AST.IR.Jump.Goto(label2, in.pos))
            blocks = blocks :+ AST.IR.BasicBlock(label2, ISZ(), b.jump)
          }
        case _ => blocks = blocks :+ b
      }
    }
    return p(body = body(blocks = blocks))
  }

  def transformIndexing(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      val ic = IndexingCounter(0)
      ic.transform_langastIRBasicBlock(b)
      if (ic.count > 1) {
        var label = b.label
        for (g <- b.grounds) {
          val next = fresh.label()
          blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(g), AST.IR.Jump.Goto(next, g.pos))
          label = next
        }
        blocks = blocks((blocks.size - 1) ~> blocks(blocks.size - 1)(jump = b.jump))
      } else {
        blocks = blocks :+ b
      }
    }
    return p(body = body(blocks = blocks))
  }

  def transformCP(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var cpSubstMap = HashMap.empty[Z, Z]
    for (i <- 0 until startingLabel) {
      cpSubstMap = cpSubstMap + i ~> i
    }

    for (b <- body.blocks) {
      if (b.label >= startingLabel) {
        cpSubstMap = cpSubstMap + b.label ~> cpSubstMap.size
      }
    }

    return CPSubstitutor(this, cpSubstMap).transform_langastIRProcedure(p).getOrElse(p)
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

  def transformString(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      val sc = StringCollector(HashSSet.empty)
      sc.transform_langastIRBasicBlock(b)
      if (sc.r.nonEmpty) {
        var temp = nextBlockTemp(b)
        var stringTempMap = HashMap.empty[AST.IR.Exp, AST.IR.Exp]
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        for (str <- sc.r.elements) {
          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, str, str.pos)
          stringTempMap = stringTempMap + str ~> AST.IR.Exp.Temp(temp, stringISType, str.pos)
          temp = temp + 1
        }
        val label = fresh.label()
        blocks = blocks :+ AST.IR.BasicBlock(b.label, grounds, AST.IR.Jump.Goto(label, b.grounds(0).pos))
        blocks = blocks :+ ExpSubstitutor(stringTempMap).transform_langastIRBasicBlock(b(label = label)).get
      } else {
        blocks = blocks :+ b
      }
    }
    return p(body = body(blocks = blocks))
  }

  @strictpure def isConstruct(e: AST.IR.Exp): B = e match {
    case _: AST.IR.Exp.Construct => T
    case _: AST.IR.Exp.String => T
    case e: AST.IR.Exp.Apply if e.id == "create" =>
      e.owner match {
        case AST.Typed.isName => T
        case AST.Typed.msName => T
        case AST.Typed.iszName => T
        case AST.Typed.mszName => T
        case _ => F
      }
    case _ => F
  }

  def transformConstruct(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    var body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()

    for (b <- body.blocks) {
      var block = b
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case g@AST.IR.Stmt.Assign.Temp(_, rhs, _) if isConstruct(rhs) =>
            val allocType: AST.Typed = rhs match {
              case rhs: AST.IR.Exp.String => allocTypeNamed(T, rhs.value.size)
              case _ => rhs.tipe
            }
            val decl = AST.IR.Stmt.Decl(F, T, T, p.context, ISZ(
              AST.IR.Stmt.Decl.Local(constructResultId(rhs.pos), allocType)), g.pos)
            grounds = grounds :+ decl
            grounds = grounds :+ g
            val label = fresh.label()
            blocks = blocks :+ block(block.label, grounds, AST.IR.Jump.Goto(label, g.pos))
            grounds = ISZ()
            block = block(label, grounds, block.jump)
            val temp = AST.IR.Exp.Temp(g.lhs, if (rhs.tipe == AST.Typed.string) stringISType else rhs.tipe, rhs.pos)
            val t = rhs.tipe.asInstanceOf[AST.Typed.Name]
            rhs match {
              case rhs: AST.IR.Exp.Construct =>
                if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
                  val indexType = t.args(0)
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
                    ISZ(temp), AST.Typed.Fun(AST.Purity.Impure, F, ISZ(rhs.tipe), AST.Typed.unit), rhs.pos))
                }
              case rhs: AST.IR.Exp.String =>
                val u8is = conversions.String.toU8is(rhs.value)
                for (i <- u8is.indices) {
                  val arg = AST.IR.Exp.Int(AST.Typed.u8, u8is(i).toZ, rhs.pos)
                  grounds = grounds :+ AST.IR.Stmt.Assign.Index(temp, AST.IR.Exp.Int(spType, i, arg.pos), arg, arg.pos)
                }
              case _ =>
            }

          case _ => grounds = grounds :+ g
        }
      }
      blocks = blocks :+ block(grounds = grounds)
    }
    body = body(blocks = blocks)

    val exit = MBox(HashSMap.empty[Z, ISZ[HashSSet[(Z, AST.Typed)]]])
    @pure def exitContainsTemp(label: Z, i: Z, temp: Z): B = {
      for (t <- exit.value.get(label).get(i).elements if t._1 == temp) {
        return T
      }
      return F
    }
    TempScalarOrSpLV(this, ControlFlowGraph.buildBasic(body)).compute(body, MBox(HashSMap.empty[Z, ISZ[HashSSet[(Z, AST.Typed)]]]), exit)
    var blockMap = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))

    def rec(label: Z, i: Z, temp: Z, undecl: AST.IR.Stmt.Decl): Unit = {
      val b = blockMap.get(label).get
      for (j <- i until b.grounds.size) {
        val g = b.grounds(j)
        val tc = TempCollector(F, HashSMap.empty)
        tc.transform_langastIRStmtGround(g)
        if (tc.r.contains(temp) && !exitContainsTemp(b.label, i, temp)) {
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
          case AST.IR.Stmt.Assign.Temp(temp, rhs, _) =>
            var shouldUndecl = F
            val allocType: AST.Typed = rhs match {
              case _: AST.IR.Exp.Construct =>
                shouldUndecl = T
                rhs.tipe
              case rhs: AST.IR.Exp.String =>
                shouldUndecl = T
                allocTypeNamed(T, rhs.value.size)
              case _=>
                rhs.tipe
            }
            if (shouldUndecl) {
              val undecl = AST.IR.Stmt.Decl(T, T, T, p.context, ISZ(
                AST.IR.Stmt.Decl.Local(constructResultId(rhs.pos), allocType)), g.pos)
              rec(b.label, i + 1, temp, undecl)
            }
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
      def insertUndecl(tempOpt: Option[Z]): ISZ[AST.IR.Stmt.Ground] = {
        var r = ISZ[AST.IR.Stmt.Ground]()
        for (i <- grounds.size - 1 to 0 by -1) {
          val g = grounds(i)
          tempOpt match {
            case Some(temp) =>
              g match {
                case g: AST.IR.Stmt.Assign.Temp if g.lhs == temp => return grounds
                case _ =>
              }
            case _ =>
          }
          val tc = TempCollector(F, HashSMap.empty)
          tc.transform_langastIRStmtGround(g)
          for (temp <- tc.r.keys if tempOpt.isEmpty || tempOpt.get == temp) {
            undeclMap.get(temp) match {
              case Some(undecl) =>
                r = r :+ undecl
                undeclMap = undeclMap -- ISZ(temp)
              case _ =>
            }
          }
          r = r :+ g
        }
        return for (i <- r.size - 1 to 0 by -1) yield r(i)
      }
      for (g <- b.grounds) {
        g match {
          case g: AST.IR.Stmt.Assign.Temp =>
            undeclMap.get(g.lhs) match {
              case Some(_) => grounds = insertUndecl(Some(g.lhs))
              case _ =>
            }
          case _ =>
        }
        g match {
          case g: AST.IR.Stmt.Expr if g.exp.methodType.ret != AST.Typed.unit && (config.tempLocal __>: !isScalar(g.exp.methodType.ret)) =>
            val decl = AST.IR.Stmt.Decl(F, T, T, p.context, ISZ(
              AST.IR.Stmt.Decl.Local(callResultId(g.exp.id, g.exp.pos), g.exp.tipe)), g.pos)
            grounds = grounds :+ decl
            grounds = grounds :+ g
            grounds = grounds :+ decl.undeclare
          case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] && (config.tempLocal __>: !isScalar(g.rhs.tipe)) =>
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
      blocks = blocks :+ b(grounds = insertUndecl(None()))
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
          case g@AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.GlobalVarRef, pos) if !ignoreGlobalInits.contains(rhs.name) && !isIntrinsicGlobalVar(rhs.name) =>
            val owner = ops.ISZOps(rhs.name).dropRight(1)
            if (p.owner :+ p.id != owner) {
              val label1 = fresh.label()
              val label2 = fresh.label()
              blocks = blocks :+ AST.IR.BasicBlock(block.label, grounds, AST.IR.Jump.If(AST.IR.Exp.GlobalVarRef(
                owner, AST.Typed.b, pos), label2, label1, pos))
              blocks = blocks :+ AST.IR.BasicBlock(label1, ISZ(AST.IR.Stmt.Expr(AST.IR.Exp.Apply(T, owner, objInitId,
                ISZ(), AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.unit), pos))),
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

  def transformStackTraceDesc(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    if (!config.stackTrace || p.owner == intrinsicName) {
      return p
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val descOffset = procedureParamInfo(PBox(p))._2.get(sfDescId).get.loc
    val desc = procedureDesc(PBox(p))
    var grounds = ISZ[AST.IR.Stmt.Ground]()
    val sfDescType = sha3(desc)
    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
      AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, p.pos)), descOffset, isSigned(typeShaType),
      typeByteSize(typeShaType), AST.IR.Exp.Int(typeShaType, sfDescType.toZ, p.pos),
      st"$sfDescId = 0x$sfDescType ($desc)", typeShaType, p.pos))
    val label = fresh.label()
    val first = body.blocks(0)
    return p(body = body(blocks = AST.IR.BasicBlock(first.label, grounds, AST.IR.Jump.Goto(label, p.pos)) +: body.blocks(0 ~> first(label = label))))
  }

  def transformErase(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    if (!config.erase || config.memoryAccess == Anvil.Config.MemoryAccess.Default) {
      return p
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    val sp = AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, p.pos))
    for (b <- body.blocks) {
      var block = b
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case AST.IR.Stmt.Intrinsic(in: Intrinsic.Decl) if in.undecl =>
            var offset: Z = 0
            var size: Z = 0
            var ids = ISZ[String]()
            for (i <- in.slots.size - 1 to 0 if in.slots(i).size > 0) {
              val slot = in.slots(i)
              ids = ids :+ slot.id
              if (offset == 0) {
                offset = slot.loc
              }
              assert(offset + size == slot.loc, b.prettyST(printer).render)
              size = size + slot.size
            }
            if (offset != 0) {
              if (grounds.nonEmpty) {
                val label = fresh.label()
                blocks = blocks :+ block(grounds = grounds, jump = AST.IR.Jump.Goto(label, in.pos))
                block = AST.IR.BasicBlock(label, ISZ(), b.jump)
              }
              grounds = ISZ(
                AST.IR.Stmt.Intrinsic(Intrinsic.Erase(sp, offset, size, st"Erase ${(ids, ", ")}", AST.Typed.u8, g.pos)),
                g
              )
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

  def transformSCreate(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure, maxTemps: TempVector): AST.IR.Procedure = {
    @strictpure def isSCreate(e: AST.IR.Exp): B = e match {
      case e: AST.IR.Exp.Apply if e.id == "create" =>
        e.owner match {
          case AST.Typed.isName => T
          case AST.Typed.msName => T
          case AST.Typed.iszName => T
          case AST.Typed.mszName => T
          case _ => F
        }
      case _ => F
    }
    @strictpure def isSCreateGround(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = {
      g match {
        case g: AST.IR.Stmt.Assign.Temp => isSCreate(g.rhs)
        case _ => F
      }
    }
    var createLabels = HashSMap.empty[AST.Typed.Name, Z]
    val cpt: AST.Typed = if (config.splitTempSizes) cpType else AST.Typed.u64
    fresh.setTemp(maxTemps.typeCount(this, cpt))
    val retParam = fresh.temp()
    val spt: AST.Typed = if (config.splitTempSizes) spType else AST.Typed.u64
    if (isSigned(cpt) != isSigned(spt) || typeByteSize(cpt) != typeByteSize(spt)) {
      fresh.setTemp(maxTemps.typeCount(this, spt))
    }
    val lhsOffsetParam = fresh.temp()
    val sizeParam = fresh.temp()
    val index = fresh.temp()
    val defaultT: AST.Typed = AST.Typed.u64
    if (isSigned(spt) != isSigned(defaultT) || typeByteSize(spt) != typeByteSize(defaultT)) {
      fresh.setTemp(maxTemps.typeCount(this, defaultT))
    }
    val defaultParam = fresh.temp()
    val bt: AST.Typed = if (config.splitTempSizes) AST.Typed.b else AST.Typed.u64
    if (isSigned(defaultT) != isSigned(bt) || typeByteSize(defaultT) != typeByteSize(bt)) {
      fresh.setTemp(maxTemps.typeCount(this, bt))
    }
    val cond1 = fresh.temp()
    val cond2 = fresh.temp()
    val body = transformSplitTest(F, fresh, p, isSCreateGround _).body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    var insertCreate = F
    for (b <- body.blocks) {
      b.grounds match {
        case ISZ(stmt: AST.IR.Stmt.Assign.Temp) if isSCreate(stmt.rhs) =>
          insertCreate = T
          val rhs = stmt.rhs.asInstanceOf[AST.IR.Exp.Apply]
          val pos = rhs.pos
          var addGoto = F
          val retLabel: Z = b.jump match {
            case j: AST.IR.Jump.Goto => j.label
            case _ =>
              addGoto = T
              fresh.label()
          }
          val t = rhs.tipe.asInstanceOf[AST.Typed.Name]
          val createLabel: Z = createLabels.get(t).getOrElse(fresh.label())
          createLabels = createLabels + t ~> createLabel
          var grounds = ISZ[AST.IR.Stmt.Ground]()
          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(retParam, AST.IR.Exp.Int(cpType, retLabel, pos), pos)
          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(lhsOffsetParam, AST.IR.Exp.Temp(stmt.lhs, spType, pos), pos)
          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(sizeParam, AST.IR.Exp.Type(F, rhs.args(0), spType, pos), pos)
          var drhs: AST.IR.Exp = rhs.args(1)
          if (drhs.tipe != AST.Typed.u64) {
            drhs = AST.IR.Exp.Type(F, drhs, AST.Typed.u64, pos)
          }
          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(defaultParam, drhs, pos)
          blocks = blocks :+ AST.IR.BasicBlock(b.label, grounds, AST.IR.Jump.Goto(createLabel, pos))
          if (addGoto) {
            blocks = blocks :+ AST.IR.BasicBlock(retLabel, ISZ(), b.jump)
          }
        case _ => blocks = blocks :+ b
      }
    }
    for (entry <- createLabels.entries) {
      val (t, createLabel) = entry
      val maxSize = getMaxArraySize(t)
      val pos = p.pos
      val checkMax = fresh.label()
      val loop = fresh.label()
      val ifLoop = fresh.label()
      val loopBody = fresh.label()
      val inc = fresh.label()
      val end = fresh.label()
      val elementType = t.args(1)
      val elementSize = typeByteSize(elementType)
      var dataOffset = typeShaSize + typeByteSize(AST.Typed.z)
      if (config.alignAxi4 && !isScalar(elementType)) {
        dataOffset = pad64(dataOffset)
      }
      blocks = blocks :+ AST.IR.BasicBlock(createLabel, ISZ(
        AST.IR.Stmt.Assign.Temp(lhsOffsetParam, AST.IR.Exp.Binary(spType, AST.IR.Exp.Temp(lhsOffsetParam, spType, pos),
          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, dataOffset, pos), pos), pos),
        AST.IR.Stmt.Assign.Temp(index, AST.IR.Exp.Int(spType, 0, pos), pos),
        AST.IR.Stmt.Assign.Temp(cond1, AST.IR.Exp.Binary(AST.Typed.b, AST.IR.Exp.Temp(sizeParam, spType, pos),
          AST.IR.Exp.Binary.Op.Le, AST.IR.Exp.Int(spType, maxSize, pos), pos), pos)
      ), AST.IR.Jump.Goto(checkMax, pos))
      blocks = blocks :+ AST.IR.BasicBlock(checkMax, ISZ(), AST.IR.Jump.If(
        AST.IR.Exp.Temp(cond1, AST.Typed.b, pos), loop, errorLabel, pos))
      blocks = blocks :+ AST.IR.BasicBlock(loop, ISZ(
        AST.IR.Stmt.Assign.Temp(cond2, AST.IR.Exp.Binary(AST.Typed.b, AST.IR.Exp.Temp(index, spType, pos),
          AST.IR.Exp.Binary.Op.Lt, AST.IR.Exp.Temp(sizeParam, spType, pos), pos), pos)
      ), AST.IR.Jump.Goto(ifLoop, pos))
      blocks = blocks :+ AST.IR.BasicBlock(ifLoop, ISZ(), AST.IR.Jump.If(AST.IR.Exp.Temp(cond2, AST.Typed.b, pos),
        loopBody, end, pos))
      val assign: AST.IR.Stmt.Ground = if (isScalar(elementType)) {
        var arhs: AST.IR.Exp = AST.IR.Exp.Temp(defaultParam, AST.Typed.u64, pos)
        if (elementType != AST.Typed.u64) {
          arhs = AST.IR.Exp.Type(F, arhs, elementType.asInstanceOf[AST.Typed.Name], pos)
        }
        AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Temp(lhsOffsetParam, spType, pos), 0, isSigned(elementType), typeByteSize(elementType), arhs, st"",
          elementType, pos))
      } else {
        val bytes = typeByteSize(elementType)
        AST.IR.Stmt.Intrinsic(Intrinsic.Copy(
          AST.IR.Exp.Temp(lhsOffsetParam, spType, pos), 0,
          bytes,
          AST.IR.Exp.Int(spType, bytes, pos),
          AST.IR.Exp.Type(F, AST.IR.Exp.Temp(defaultParam, AST.Typed.u64, pos), spType, pos),
          st"", elementType, elementType, pos))
      }
      blocks = blocks :+ AST.IR.BasicBlock(loopBody, ISZ(assign), AST.IR.Jump.Goto(inc, pos))
      blocks = blocks :+ AST.IR.BasicBlock(inc, ISZ(
        AST.IR.Stmt.Assign.Temp(lhsOffsetParam, AST.IR.Exp.Binary(spType, AST.IR.Exp.Temp(lhsOffsetParam, spType, pos),
          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, elementSize, pos), pos), pos),
        AST.IR.Stmt.Assign.Temp(index, AST.IR.Exp.Binary(spType, AST.IR.Exp.Temp(index, spType, pos),
          AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, 1, pos), pos), pos)
      ), AST.IR.Jump.Goto(loop, pos))
      blocks = blocks :+ AST.IR.BasicBlock(end, ISZ(),
        AST.IR.Jump.Intrinsic(Intrinsic.GotoLocal(T, retParam, None(), s"screate:$t", pos)))
    }
    return p(body = body(blocks = blocks))
  }

  def transformCopyDefaultIp(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure, maxTemps: TempVector): AST.IR.Procedure = {
    val spt: AST.Typed = if (config.splitTempSizes) spType else AST.Typed.u64
    fresh.setTemp(maxTemps.typeCount(this, spt))
    val lhsOffsetParam = fresh.temp()
    val rhsOffsetParam = fresh.temp()
    val rhsElementSizeParam = fresh.temp()

    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      b.grounds match {
        case ISZ(AST.IR.Stmt.Intrinsic(in: Intrinsic.Copy)) if !in.rhsBytes.isInstanceOf[AST.IR.Exp.Int] =>
          val copyLabel = fresh.label()
          val t = in.rhsTipe
          val pos = in.pos
          var grounds = ISZ[AST.IR.Stmt.Ground]()
          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(lhsOffsetParam, in.lhsOffset, pos)
          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(rhsOffsetParam, in.rhs, pos)
          val sizeInfoOpt = classSizeFieldOffsets(t.asInstanceOf[AST.Typed.Name])._2.get("size")
          if (config.erase || sizeInfoOpt.isEmpty) {
            grounds = grounds :+ AST.IR.Stmt.Assign.Temp(rhsElementSizeParam, in.rhsBytes, pos)
          } else {
            val (sizeType, sizeOffset) = sizeInfoOpt.get
            val elementByteSize: Z = if (t == AST.Typed.string) 1 else typeByteSize(t.asInstanceOf[AST.Typed.Name].args(1))
            var elementSize: AST.IR.Exp = AST.IR.Exp.Type(F,
              AST.IR.Exp.Intrinsic(Intrinsic.Load(
                in.rhs, sizeOffset, isSigned(sizeType), typeByteSize(sizeType), st"", sizeType, pos)),
              spType, pos)
            if (elementByteSize != 1) {
              elementSize = AST.IR.Exp.Binary(spType, elementSize, AST.IR.Exp.Binary.Op.Mul,
                AST.IR.Exp.Int(spType, elementByteSize, pos), pos)
            }
            grounds = grounds :+ AST.IR.Stmt.Assign.Temp(rhsElementSizeParam, elementSize, pos)
          }
          blocks = blocks :+ AST.IR.BasicBlock(b.label, grounds, AST.IR.Jump.Goto(copyLabel, pos))
          blocks = blocks :+ AST.IR.BasicBlock(copyLabel, ISZ(
            AST.IR.Stmt.Intrinsic(in(
              lbase = AST.IR.Exp.Temp(lhsOffsetParam, spType, pos),
              loffset = 0,
              rhs = AST.IR.Exp.Temp(rhsOffsetParam, spType, pos),
              rhsBytes =
                if (config.erase) AST.IR.Exp.Temp(rhsElementSizeParam, spType, pos)
                else AST.IR.Exp.Binary(spType,
                  AST.IR.Exp.Temp(rhsElementSizeParam, spType, pos), AST.IR.Exp.Binary.Op.Add,
                  AST.IR.Exp.Int(spType, typeShaSize + typeByteSize(AST.Typed.z), pos), pos)))
          ), b.jump)
        case _ => blocks = blocks :+ b
      }
    }
    return p(body = body(blocks = blocks))
  }

  def transformUndecl(p: AST.IR.Procedure): AST.IR.Procedure = {
    val params = HashSet ++ p.paramNames
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val localExitSet = MBox(HashSMap.empty[Z, ISZ[HashSSet[(String, AST.Typed)]]])
    val cfg = ControlFlowGraph.buildBasic(body)
    LocalDeclLV(cfg).compute(body, MBox(HashSMap.empty), localExitSet)
    var blockMap = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    var undeclMap = HashSMap.empty[(String, AST.Typed), AST.IR.Stmt.Decl]
    var blockUndecls = HashMap.empty[Z, ISZ[AST.IR.Stmt.Ground]]
    for (b <- blockMap.values) {
      var undecls = HashMap.empty[Z, ISZ[AST.IR.Stmt.Ground]]
      def findTempUseIndex(i: Z, temp: Z, t: AST.Typed): Option[Z] = {
        for (j <- i until b.grounds.size) {
          val tc = TempCollector(F, HashSMap.empty)
          tc.transform_langastIRStmtGround(b.grounds(j))
          for (tipe <- tc.r.get(temp).getOrElse(HashSSet.empty).elements if tipe == t) {
            return Some(j)
          }
        }
        return None()
      }
      for (i <- b.grounds.indices) {
        val g = b.grounds(i)
        g match {
          case g: AST.IR.Stmt.Decl if !g.isAlloc =>
            if (!g.undecl) {
              undeclMap = undeclMap ++ (for (l <- g.locals) yield (l.id, l.tipe) ~> g.undeclare)
            }
          case _ =>
            val lc = LocalCollector(HashSSet.empty)
            lc.transform_langastIRStmtGround(g)
            g match {
              case g: AST.IR.Stmt.Assign.Local => lc.r = lc.r + (g.lhs, g.tipe)
              case _ =>
            }
            for (idt <- lc.r.elements if !localExitSet.value.get(b.label).get(i).contains(idt)) {
              undeclMap.get(idt) match {
                case Some(undecl) =>
                  val scalarUndecl = undecl(locals = for (l <- undecl.locals if isScalar(l.tipe)) yield l)
                  val nonScalarUndecl = undecl(locals = for (l <- undecl.locals if !isScalar(l.tipe)) yield l)
                  if (scalarUndecl.locals.nonEmpty) {
                    undecls = undecls + i ~> (undecls.get(i).getOrElse(ISZ()) :+ scalarUndecl)
                  }
                  if (nonScalarUndecl.locals.nonEmpty) {
                    val stmt = g.asInstanceOf[AST.IR.Stmt.Assign.Temp]
                    val temp = stmt.lhs
                    findTempUseIndex(i + 1, temp, stmt.rhs.tipe) match {
                      case Some(j) =>
                        undecls = undecls + j ~> (undecls.get(j).getOrElse(ISZ()) :+ nonScalarUndecl)
                      case _ =>
                        val tc = TempCollector(F, HashSMap.empty)
                        tc.transform_langastIRJump(b.jump)
                        assert(tc.r.contains(temp))
                        for (target <- b.jump.targets) {
                          blockUndecls = blockUndecls + target ~> (blockUndecls.get(target).getOrElse(ISZ()) :+ nonScalarUndecl)
                        }
                    }
                  }
                case _ =>
                  if (!params.contains(idt._1) && !ignoredTempLocal.contains(idt._1)) {
                    halt(s"${p.id} @ ${b.label}: $idt, $undeclMap")
                  }
              }
            }
        }
      }
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (i <- b.grounds.indices) {
        val g = b.grounds(i)
        g match {
          case g: AST.IR.Stmt.Decl if g.undecl =>
          case _ =>
            grounds = grounds :+ g
            undecls.get(i) match {
              case Some(ds) => grounds = grounds ++ ds
              case _ =>
            }
        }
      }
      blockMap = blockMap + b.label ~> b(grounds = grounds)
    }
    for (p <- blockUndecls.entries) {
      val b = blockMap.get(p._1).get
      blockMap = blockMap + b.label ~> b(grounds = p._2 ++ b.grounds)
    }
    return p(body = body(blocks = blockMap.values))
  }

  def transformTempNum(proc: AST.IR.Procedure): AST.IR.Procedure = {
    val paramInfo = procedureParamInfo(PBox(proc))._2
    val maxLocalTemps: TempVector = {
      val maxParamTemps = TempVector.empty.incParams(this, paramInfo)
      val sltc = ScalarLocalTempCounter(this, maxParamTemps)
      sltc.transform_langastIRProcedure(proc)
      sltc.r
    }
    return TempIncrementer(this, maxLocalTemps).transform_langastIRProcedure(proc).getOrElse(proc)
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
    if (!config.stackTrace || p.owner == intrinsicName) {
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
        if (!g.isInstanceOf[AST.IR.Stmt.Decl]) {
          assignLoc(g.pos)
        }
        grounds = grounds :+ g
      }
      assignLoc(b.jump.pos)
      blocks = blocks :+ b(grounds = grounds)
    }
    return p(body = body(blocks = blocks))
  }

  def transformBasicBlock(stage: Z, fresh: lang.IRTranslator.Fresh, program: AST.IR.Program, output: Output): AST.IR.Program = {
    var procedureMap = HashSMap.empty[AST.IR.MethodContext, AST.IR.Procedure]
    if (!config.isFirstGen) {
      for (p <- program.procedures) {
        procedureMap = procedureMap + p.context ~> p
      }
    }

    @pure def transform(p: AST.IR.Procedure): AST.IR.Procedure = {
      var r = p
      var pass: Z = 0

      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "basic"), r.prettyST(printer))
      pass = pass + 1

      r = transformGlobalVarRef(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "global"), r.prettyST(printer))
      pass = pass + 1

      r = IntTransformer(this).transform_langastIRProcedure(r).getOrElse(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "int"), r.prettyST(printer))
      pass = pass + 1

      r = FloatEqualityTransformer(this).transform_langastIRProcedure(r).getOrElse(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "float-eq"), r.prettyST(printer))
      pass = pass + 1

      r = transformStackTraceLoc(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "stack-trace-loc"), r.prettyST(printer))
      pass = pass + 1

      r = transformHalt(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "halt"), r.prettyST(printer))
      pass = pass + 1

      r = transformPrint(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "print"), r.prettyST(printer))
      pass = pass + 1

      if (!config.isFirstGen) {
        r = transformSecondGenCall(r, procedureMap)
        output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "second-gen-call"), r.prettyST(printer))
        pass = pass + 1
      }

      r = transformApplyConstructResult(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "apply-construct-result"), r.prettyST(printer))
      pass = pass + 1

      r = transformEmptyBlock(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "empty-block"), r.prettyST(printer))
      pass = pass + 1

      r = transformReduceTemp(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "reduce-temp"), r.prettyST(printer))
      pass = pass + 1

      r = if (config.splitTempSizes) transformTempTypeCompress(r) else transformTempCompress(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "temp-compress"), r.prettyST(printer))
      pass = pass + 1

      @pure def hasAssignTempUsage(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = {
        g match {
          case g: AST.IR.Stmt.Assign.Temp =>
            val tc = TempCollector(F, HashSMap.empty)
            tc.transform_langastIRExp(g.rhs)
            return tc.r.nonEmpty
          case g: AST.IR.Stmt.Assign.Index =>
            val rc = RegisterDetector(F, F)
            rc.transform_langastIRExp(g.index)
            return !rc.hasDP
          case _: AST.IR.Stmt.Assign => return T
          case _ => return F
        }
      }

      r = transformUndecl(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "undecl"), r.prettyST(printer))
      pass = pass + 1

      @strictpure def isDivMod(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = g match {
        case AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.Binary, _) =>
          rhs.op == AST.IR.Exp.Binary.Op.Div || rhs.op == AST.IR.Exp.Binary.Op.Rem
        case _ => F
      }

      r = transformSplitTest(F, fresh, r, isDivMod _)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-div-mod"), r.prettyST(printer))
      pass = pass + 1

      r = transformSplitTest(F, fresh, r, hasAssignTempUsage _)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-temp"), r.prettyST(printer))
      pass = pass + 1

      r = transformSplitTempJump(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-temp-jump"), r.prettyST(printer))
      pass = pass + 1

      r = transformString(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "string"), r.prettyST(printer))
      pass = pass + 1

      r = transformConstruct(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "construct"), r.prettyST(printer))
      pass = pass + 1

      //      r = transformSplitReadWrite(fresh, r)
//      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-read-write"), r.prettyST(printer))
//      pass = pass + 1

      r = transformInstanceOf(fresh, r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "instanceof"), r.prettyST(printer))
      pass = pass + 1

      r = transformMergeDecl(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "merge-decl"), r.prettyST(printer))
      pass = pass + 1

      @strictpure def isInvoke(grounds: ISZ[AST.IR.Stmt.Ground], g: AST.IR.Stmt.Ground): B = g match {
        case AST.IR.Stmt.Assign.Temp(_, _: AST.IR.Exp.Apply, _) => T
        case _: AST.IR.Stmt.Expr => T
        case _ => F
      }

      r = transformSplitTest(T, fresh, r, isInvoke _)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "split-invoke"), r.prettyST(printer))
      pass = pass + 1

      r = transformEmptyBlock(r)
      output.add(F, irProcedurePath(p.id, p.tipe, stage, pass, "empty-block"), r.prettyST(printer))
      pass = pass + 1

      return r
    }
    return program(procedures = ops.ISZOps(program.procedures).map(transform _))
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
          AST.IR.Exp.Intrinsic(Intrinsic.Register(T, _, _)), 0, _, _, n: AST.IR.Exp.Int, _, _, _)) if n.tipe == cpType =>
            r = r + n.value ~> (r.get(n.value).get + 1)
          case AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Intrinsic(Intrinsic.Register(T, _, _)), 0, _, _, AST.IR.Exp.Type(_, n: AST.IR.Exp.Int, _, _), _, _, _)) if n.tipe == cpType =>
            r = r + n.value ~> (r.get(n.value).get + 1)
          case AST.IR.Stmt.Assign.Temp(_, AST.IR.Exp.Type(_, n: AST.IR.Exp.Int, _, _), _) if n.tipe == cpType =>
            r = r + n.value ~> (r.get(n.value).get + 1)
          case AST.IR.Stmt.Assign.Temp(_, n: AST.IR.Exp.Int, _) if n.tipe == cpType =>
            r = r + n.value ~> (r.get(n.value).get + 1)
          case AST.IR.Stmt.Assign.Global(_, _, AST.IR.Exp.Type(_, n: AST.IR.Exp.Int, _, _), _) if n.tipe == cpType =>
            r = r + n.value ~> (r.get(n.value).get + 1)
          case AST.IR.Stmt.Assign.Global(_, _, n: AST.IR.Exp.Int, _) if n.tipe == cpType =>
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
                      callResultOffsetMap: HashMap[String, Z]): ISZ[AST.IR.BasicBlock] = {
    var seen = HashSet.empty[AST.IR.MethodContext]
    var work = ISZ[AST.IR.Procedure](main)
    var mergedBlocks = ISZ[AST.IR.BasicBlock]()
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.Procedure]()
      for (p <- work) {
        seen = seen + p.context
        var addBeginningMap = HashSMap.empty[Z, (ISZ[AST.IR.Stmt.Ground], ISZ[AST.IR.Stmt.Ground], ISZ[AST.IR.Stmt.Ground])]
        var blocks = ISZ[AST.IR.BasicBlock]()
        val body = p.body.asInstanceOf[AST.IR.Body.Basic]
        val exitSet = MBox(HashSMap.empty[Z, ISZ[HashSSet[(Z, AST.Typed)]]])
        TempScalarOrSpLV(this, ControlFlowGraph.buildBasic(body)).compute(body, MBox(HashSMap.empty), exitSet)
        for (b <- body.blocks) {
          def processInvoke(stmtIndex: Z, g: AST.IR.Stmt.Ground, lhsOpt: Option[Z], e: AST.IR.Exp.Apply, label: Z): Unit = {
            val mc = AST.IR.MethodContext(e.isInObject, e.owner, e.id, e.methodType)
            val called = procedureMap.get(mc).get
            val paramInfo = procedureParamInfo(PBox(called))._2
            var liveTemps = exitSet.value.get(b.label).get(stmtIndex).elements
            if (config.tempLocal) {
              val returnInfo = paramInfo.get(returnLocalId).get
              liveTemps = liveTemps :+ (returnInfo.loc, returnInfo.tipe)
            }
            val pMaxTemps = procMaxTemps(this, PBox(p))
            val calledMaxTemps = procMaxTemps(this, PBox(called))
            var maxTemps = pMaxTemps.max(calledMaxTemps)

            val registerSpace: Z = {
              var regs: Z = 0
              for (liveTemp <- liveTemps) {
                val tipe = liveTemp._2
                val t: AST.Typed = if (isScalar(tipe)) tipe else spType
                regs = regs + typeByteSize(t)
              }
              lhsOpt match {
                case Some(_) =>
                  val tipe = called.tipe.ret
                  val t: AST.Typed = if (isScalar(tipe)) tipe else spType
                  regs = regs - typeByteSize(t)
                case _ =>
              }
              regs
            }
            if (!seen.contains(mc)) {
              next = next :+ called
            }
            val spAdd = procedureSizeMap.get(p.context).get
            val spt: AST.Typed = if (config.splitTempSizes) spType else AST.Typed.u64
            var spGrounds = ISZ[AST.IR.Stmt.Ground]()
            var grounds = ISZ[AST.IR.Stmt.Ground]()
            spGrounds = spGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(T, T,
              AST.IR.Exp.Int(spType, pad64(spAdd + registerSpace), e.pos), e.pos))

            val returnInfo = paramInfo.get(returnLocalId).get
            var locals = ISZ[Intrinsic.Decl.Local](
              Intrinsic.Decl.Local(returnInfo.loc, returnInfo.totalSize, returnLocalId, returnInfo.tipe)
            )
            maxTemps = maxTemps.incType(this, if (config.splitTempSizes) returnInfo.tipe else AST.Typed.u64)
            if (called.tipe.ret != AST.Typed.unit) {
              val resultInfo = paramInfo.get(resultLocalId).get
              locals = locals :+ Intrinsic.Decl.Local(resultInfo.loc, resultInfo.totalSize, resultLocalId,
                resultInfo.tipe)
              if (isScalar(resultInfo.tipe)) {
                maxTemps = maxTemps.incType(this, if (config.splitTempSizes) resultInfo.tipe else AST.Typed.u64)
              }
            }
            if (config.stackTrace) {
              val sfCallerInfo = paramInfo.get(sfCallerId).get
              val sfLocInfo = paramInfo.get(sfLocId).get
              val sfDescInfo = paramInfo.get(sfDescId).get
              val sfCurrentInfo = paramInfo.get(sfCurrentId).get
              locals = locals :+ Intrinsic.Decl.Local(sfCallerInfo.loc, sfCallerInfo.totalSize, sfCallerId, sfCallerInfo.tipe)
              locals = locals :+ Intrinsic.Decl.Local(sfLocInfo.loc, sfLocInfo.totalSize, sfLocId, sfLocInfo.tipe)
              locals = locals :+ Intrinsic.Decl.Local(sfDescInfo.loc, sfDescInfo.totalSize, sfDescId, sfDescInfo.tipe)
              locals = locals :+ Intrinsic.Decl.Local(sfCurrentInfo.loc, sfCurrentInfo.totalSize, sfCurrentId, sfCurrentInfo.tipe)
            }
            val isMain = procedureMod(called.context) == PMod.Main
            var tempGrounds = ISZ[AST.IR.Stmt.Ground]()
            if (config.tempLocal) {
              for (param <- ops.ISZOps(called.paramNames).zip(called.tipe.args)) {
                {
                  val info = paramInfo.get(param._1).get
                  locals = locals :+ Intrinsic.Decl.Local(info.loc, info.totalSize, param._1, param._2)
                }
                if (isMain && !isScalar(param._2)) {
                  val info = paramInfo.get(s"${param._1}$dataId").get
                  locals = locals :+ Intrinsic.Decl.Local(info.loc, info.totalSize, param._1, param._2)
                }
              }
              tempGrounds = tempGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(F, F, locals, e.pos))
            } else {
              for (param <- ops.ISZOps(called.paramNames).zip(called.tipe.args)) {
                val info = paramInfo.get(param._1).get
                val t: AST.Typed = if (isMain || isScalar(param._2)) param._2 else spType
                locals = locals :+ Intrinsic.Decl.Local(info.loc, info.totalSize, param._1, t)
              }
              spGrounds = spGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(F, F, locals, e.pos))
            }
            if (config.stackTrace) {
              val n = procedureParamInfo(PBox(p))._2.get(sfCallerId).get.loc -
                pad64(spAdd + registerSpace)
              val sfCallerInfo = paramInfo.get(sfCallerId).get
              val sfCurrentInfo = paramInfo.get(sfCurrentId).get
              val callerRhsOffset = AST.IR.Exp.Binary(spType,
                AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, -n, e.pos), e.pos)
              val rhsTemp = maxTemps.typeCount(this, spt)
              maxTemps = maxTemps.incType(this, spt)
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)), sfCallerInfo.loc, isSigned(spType),
                typeByteSize(spType), callerRhsOffset, st"$sfCallerId@${sfCallerInfo.loc} = $n", spType, e.pos))
              spGrounds = spGrounds :+ AST.IR.Stmt.Assign.Temp(rhsTemp, AST.IR.Exp.Binary(spType,
                AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, sfCallerInfo.loc, e.pos), e.pos), e.pos)
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)), sfCurrentInfo.loc,
                isSigned(spType), typeByteSize(spType), AST.IR.Exp.Temp(rhsTemp, spType, e.pos),
                st"$sfCurrentId@${sfCurrentInfo.loc} = ${sfCallerInfo.loc}", spType, e.pos))
            }

            if (config.tempLocal) {
              {
                tempGrounds = tempGrounds :+ AST.IR.Stmt.Assign.Temp(paramInfo.get(returnLocalId).get.loc,
                  AST.IR.Exp.Int(cpType, label, e.pos), e.pos)
              }

              var paramTypeArgs = ISZ[((String, AST.Typed), AST.IR.Exp)]()
              if (called.tipe.ret != AST.Typed.unit && !isScalar(called.tipe.ret)) {
                val n = callResultOffsetMap.get(callResultId(e.id, e.pos)).get - pad64(spAdd + registerSpace)
                val rhs = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, -n, e.pos), e.pos)
                paramTypeArgs = paramTypeArgs :+ ((resultLocalId, spType), rhs)
              }
              paramTypeArgs = paramTypeArgs ++ ops.ISZOps(ops.ISZOps(called.paramNames).zip(called.tipe.args)).zip(e.args)
              for (param <- paramTypeArgs) {
                val ((pid, pt), parg) = param
                val tempType: AST.Typed =
                  if (config.splitTempSizes) if (isScalar(pt)) pt else spType
                  else AST.Typed.u64
                val temp = maxTemps.typeCount(this, tempType)
                maxTemps = maxTemps.incType(this, tempType)
                grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, parg, parg.pos)
                tempGrounds = tempGrounds :+ AST.IR.Stmt.Assign.Temp(paramInfo.get(pid).get.loc,
                  AST.IR.Exp.Temp(temp, pt, parg.pos), parg.pos)
              }
            } else {
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)), 0,
                isSigned(returnInfo.tipe), returnInfo.totalSize,
                AST.IR.Exp.Int(returnInfo.tipe, label, e.pos), st"$returnLocalId@0 = $label", returnInfo.tipe, e.pos
              ))

              if (called.tipe.ret != AST.Typed.unit) {
                val resultInfo = paramInfo.get(resultLocalId).get
                val n = callResultOffsetMap.get(callResultId(e.id, e.pos)).get - pad64(spAdd + registerSpace)
                val rhsTemp = maxTemps.typeCount(this, spt)
                maxTemps = maxTemps.incType(this, spt)
                spGrounds = spGrounds :+ AST.IR.Stmt.Assign.Temp(rhsTemp, AST.IR.Exp.Binary(spType,
                  AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)),
                  AST.IR.Exp.Binary.Op.Sub, AST.IR.Exp.Int(spType, -n, e.pos), e.pos), e.pos)
                grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                  AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)), resultInfo.loc,
                  isSigned(spType), typeByteSize(spType), AST.IR.Exp.Temp(rhsTemp, spType, e.pos),
                  st"$resultLocalId@${resultInfo.loc} = $n", spType, e.pos))
              }
              for (param <- ops.ISZOps(ops.ISZOps(called.paramNames).zip(mc.t.args)).zip(e.args)) {
                val ((pid, pt), parg) = param
                val t: AST.Typed = if (isScalar(pt)) pt else spType
                grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                  AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)), paramInfo.get(pid).get.loc,
                  isSigned(t), typeByteSize(t), parg, st"$pid = ${parg.prettyST(printer)}", t, parg.pos))
              }
            }
            var rgrounds = ISZ[AST.IR.Stmt.Ground]()
            var i: Z = 0
            val lhsPairOpt: Option[(Z, AST.Typed)] = lhsOpt match {
              case Some(lhs) =>
                val t: AST.Typed = if (isScalar(called.tipe.ret)) called.tipe.ret else spType
                Some((lhs, t))
              case _ => None()
            }
            for (pair <- liveTemps if lhsPairOpt != Some(pair)) {
              val (j, tipe) = pair
              val t: AST.Typed = if (isScalar(tipe)) tipe else spType
              val signed = isSigned(t)
              val size = typeByteSize(t)
              i = i + size
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)), -i, signed, size,
                AST.IR.Exp.Temp(j, t, e.pos), st"save $$$j ($tipe)", t, e.pos))
              rgrounds = rgrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(
                j, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, e.pos)), -i, signed, size,
                st"restore $$$j ($tipe)", t, e.pos))
            }

            var spBgrounds = ISZ[AST.IR.Stmt.Ground]()
            var bgrounds = ISZ[AST.IR.Stmt.Ground]()
            bgrounds = bgrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(T, F,
              for (i <- locals.size - 1 to 0 by -1) yield locals(i), e.pos))

            lhsOpt match {
              case Some(lhs) =>
                if (config.tempLocal) {
                  val rhsOffset: AST.IR.Exp = AST.IR.Exp.Temp(paramInfo.get(resultLocalId).get.loc, called.tipe.ret, g.pos)
                  bgrounds = AST.IR.Stmt.Assign.Temp(lhs, rhsOffset, g.pos) +: bgrounds
                } else {
                  val t: AST.Typed = if (isScalar(called.tipe.ret)) called.tipe.ret else spType
                  val rhsTemp = maxTemps.typeCount(this, spt)
                  maxTemps = maxTemps.incType(this, spt)
                  var base: AST.IR.Exp = AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos))
                  var offset = paramInfo.get(resultLocalId).get.loc
                  if (isScalar(called.tipe.ret)) {
                    spBgrounds = spBgrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(rhsTemp,
                      base, offset, isSigned(spType), typeByteSize(spType), st"", spType, g.pos))
                    base = AST.IR.Exp.Temp(rhsTemp, spType, g.pos)
                    offset = 0
                  }
                  bgrounds = AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(lhs, base, offset,
                    isSigned(t), typeByteSize(t), st"$$$lhs = $resultLocalId", t, g.pos)) +: bgrounds
                }
              case _ =>
            }
            rgrounds = rgrounds :+ AST.IR.Stmt.Intrinsic(
              Intrinsic.RegisterAssign(T, T, AST.IR.Exp.Int(spType, -pad64(spAdd + registerSpace), e.pos), e.pos))
            addBeginningMap = addBeginningMap + label ~> (rgrounds, spBgrounds, bgrounds)
            val calledLabel = called.body.asInstanceOf[AST.IR.Body.Basic].blocks(0).label
            val tempLabel = fresh.label()
            if (tempGrounds.nonEmpty) {
              val tempLabel2 = fresh.label()
              blocks = blocks :+ b(grounds = spGrounds, jump = AST.IR.Jump.Goto(tempLabel, e.pos))
              blocks = blocks :+ AST.IR.BasicBlock(tempLabel, grounds, AST.IR.Jump.Goto(tempLabel2, e.pos))
              blocks = blocks :+ AST.IR.BasicBlock(tempLabel2, tempGrounds, AST.IR.Jump.Goto(calledLabel, e.pos))
            } else {
              blocks = blocks :+ b(grounds = spGrounds, jump = AST.IR.Jump.Goto(tempLabel, e.pos))
              blocks = blocks :+ AST.IR.BasicBlock(tempLabel, grounds, AST.IR.Jump.Goto(calledLabel, e.pos))
            }
          }
          def processInvokeH(stmtIndex: Z, g: AST.IR.Stmt.Ground, lhsOpt: Option[Z], e: AST.IR.Exp.Apply, lbl: Z): Unit = {
            th.nameMap.get(e.owner :+ e.id) match {
              case Some(_: Info.ExtMethod) =>
                blocks = blocks :+ b
                return
              case _ =>
            }
            val label = fresh.label()
            processInvoke(stmtIndex, g, lhsOpt, e, label)
            blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(), AST.IR.Jump.Goto(lbl, e.pos))
          }

          b.jump match {
            case j: AST.IR.Jump.Goto if b.grounds.size == 1 =>
              b.grounds(0) match {
                case g: AST.IR.Stmt.Expr =>
                  processInvokeH(0, g, None(), g.exp, j.label)
                case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
                  processInvokeH(0, g, Some(g.lhs), g.rhs.asInstanceOf[AST.IR.Exp.Apply], j.label)
                case _ => blocks = blocks :+ b
              }
            case j: AST.IR.Jump.Return =>
              var addGrounds = ISZ[AST.IR.Stmt.Ground]()
              j.expOpt match {
                case Some(exp) =>
                  if (config.tempLocal) {
                    val paramInfo = procedureParamInfo(PBox(p))._2
                    if (isScalar(exp.tipe)) {
                      addGrounds = addGrounds :+ AST.IR.Stmt.Assign.Temp(paramInfo.get(resultLocalId).get.loc, exp, exp.pos)
                    } else {
                      val lhsOffset: AST.IR.Exp = AST.IR.Exp.Temp(paramInfo.get(resultLocalId).get.loc, spType, exp.pos)
                      addGrounds = addGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(lhsOffset, 0,
                        typeByteSize(p.context.t.ret), copySize(exp), exp,
                        st"$resultLocalId = ${exp.prettyST(printer)}", p.context.t.ret, exp.tipe, exp.pos))
                    }
                  } else {
                    val lhsOffset: AST.IR.Exp = AST.IR.Exp.Intrinsic(Intrinsic.Load(
                      AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, exp.pos)), typeByteSize(cpType),
                      isSigned(spType), typeByteSize(spType), st"", spType, exp.pos))
                    if (isScalar(exp.tipe)) {
                      addGrounds = addGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(lhsOffset, 0,
                        isSigned(exp.tipe), typeByteSize(exp.tipe), exp, st"$resultLocalId = ${exp.prettyST(printer)}", exp.tipe, exp.pos))
                    } else {
                      addGrounds = addGrounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(lhsOffset, 0,
                        typeByteSize(p.context.t.ret), copySize(exp), exp,
                        st"$resultLocalId = ${exp.prettyST(printer)}", p.context.t.ret, exp.tipe, exp.pos))
                    }
                  }
                case _ =>
              }
              blocks = blocks :+ b(grounds = b.grounds ++ addGrounds,
                jump = AST.IR.Jump.Intrinsic(Intrinsic.GotoLocal(config.tempLocal,
                  procedureParamInfo(PBox(p))._2.get(returnLocalId).get.loc, Some(p.context), returnLocalId, j.pos)))
            case _ => blocks = blocks :+ b
          }
        }
        for (b <- blocks) {
          addBeginningMap.get(b.label) match {
            case Some((rgrounds, spGrounds, grounds)) =>
              var label = fresh.label()
              var block = b
              val jpos = b.jump.pos
              if (spGrounds.nonEmpty) {
                mergedBlocks = mergedBlocks :+ block(grounds = spGrounds, jump = AST.IR.Jump.Goto(label, jpos))
                block = AST.IR.BasicBlock(label, ISZ(), b.jump)
                label = fresh.label()
              }
              if (config.tempLocal && rgrounds.nonEmpty) {
                mergedBlocks = mergedBlocks :+
                  block(grounds = grounds ++ b.grounds, jump = AST.IR.Jump.Goto(label, jpos)) :+
                  AST.IR.BasicBlock(label, rgrounds, b.jump)
              } else {
                mergedBlocks = mergedBlocks :+ block(grounds = grounds ++ b.grounds,
                  jump = AST.IR.Jump.Goto(label, jpos)) :+
                  AST.IR.BasicBlock(label, rgrounds, b.jump)
              }
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
                rest()
                substMap = substMap + g.lhs ~> AST.IR.Exp.Temp(g.lhs, g.rhs.tipe, g.pos)
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
                case rhs: AST.IR.Exp.LocalVarRef if config.tempLocal && isScalar(rhs.tipe) =>
                  substMap = substMap + g.lhs ~> rhs
                  grounds = grounds :+ g
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
      val lv = TempScalarOrSpLV(this, ControlFlowGraph.buildBasic(body))
      val entrySet = MBox(HashSMap.empty[Z, ISZ[HashSSet[(Z, AST.Typed)]]])
      val exitSet = MBox(entrySet.value)
      def exitSetContains(label: Z, i: Z, temp: Z): B = {
        for (pair <- exitSet.value.get(label).get(i).elements if pair._1 == temp) {
          return T
        }
        return F
      }
      lv.compute(body, entrySet, exitSet)
      var blocks = ISZ[AST.IR.BasicBlock]()
      for (b <- body.blocks) {
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        for (i <- b.grounds.indices) {
          val g = b.grounds(i)
          g match {
            case g: AST.IR.Stmt.Assign.Temp if !exitSetContains(b.label, i, g.lhs) => changed = T
            case _ => grounds = grounds :+ g
          }
        }
        blocks = blocks :+ b(grounds = grounds)
      }
      body = body(blocks = blocks)
    }
    return proc(body = body)
  }

  def transformTempTypeCompress(proc: AST.IR.Procedure): AST.IR.Procedure = {
    val tc = TempCollector(T, HashSMap.empty)
    tc.transform_langastIRProcedure(proc)
    val temps = tc.r.entries
    var tempMap = HashMap.empty[(Z, AST.Typed), Z]
    var tv = TempVector.empty
    for (i <- temps.indices) {
      for (t <- temps(i)._2.elements) {
        val count = tv.typeCount(this, t)
        tv = tv.incType(this, t)
        tempMap = tempMap + (temps(i)._1, t) ~> count
      }
    }
    return TempTypeRenumberer(this, tempMap).transform_langastIRProcedure(proc).getOrElse(proc)
  }

  def transformTempCompress(proc: AST.IR.Procedure): AST.IR.Procedure = {
    val tc = TempCollector(T, HashSMap.empty)
    tc.transform_langastIRProcedure(proc)
    val temps = tc.r.keys
    var tempMap = HashMap.empty[Z, Z]
    for (i <- temps) {
      tempMap = tempMap + i ~> tempMap.size
    }
    return TempRenumberer(this, tempMap).transform_langastIRProcedure(proc).getOrElse(proc)
  }

  @memoize def procedureDesc(pbox: PBox): String = {
    val proc = pbox.p
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

    var tv = TempVector.empty

    var maxOffset: Z = 0
    if (config.tempLocal) {
      val tvType: AST.Typed = if (config.splitTempSizes) cpType else AST.Typed.u64
      m = m + returnLocalId ~> VarInfo(isScalar(cpType), tv.typeCount(this, tvType), 0, 0, cpType, p.pos)
      tv = tv.incType(this, tvType)
    } else {
      m = m + returnLocalId ~> VarInfo(isScalar(cpType), maxOffset, typeByteSize(cpType), 0, cpType, p.pos)
      maxOffset = maxOffset + typeByteSize(cpType)
    }

    val isMain = procedureMod(p.context) == PMod.Main
    if (p.tipe.ret != AST.Typed.unit) {
      if (config.tempLocal) {
        val t: AST.Typed = if (isScalar(p.tipe.ret)) p.tipe.ret else spType
        val tvType: AST.Typed = if (config.splitTempSizes) t else AST.Typed.u64
        m = m + resultLocalId ~> VarInfo(isScalar(t), tv.typeCount(this, tvType), 0, 0, t, p.pos)
        tv = tv.incType(this, tvType)
        if (isMain && !isScalar(p.tipe.ret)) {
          val size = typeByteSize(p.tipe.ret)
          m = m + s"$resultLocalId$dataId" ~> VarInfo(isScalar(p.tipe.ret), maxOffset, size, 0, p.tipe.ret, p.pos)
          maxOffset = maxOffset + size
        }
      } else {
        val dataSize: Z = if (isMain) typeByteSize(p.tipe.ret) else 0
        val size = typeByteSize(spType)
        m = m + resultLocalId ~> VarInfo(isScalar(spType), maxOffset, size, dataSize, spType, p.pos)
        maxOffset = maxOffset + size + dataSize
      }
    }

    if (config.stackTrace) {
      m = m + sfCallerId ~> VarInfo(isScalar(spType), maxOffset, typeByteSize(spType), 0, spType, p.pos)
      maxOffset = maxOffset + typeByteSize(spType)

      m = m + sfLocId ~> VarInfo(isScalar(sfLocType), maxOffset, typeByteSize(sfLocType), 0, sfLocType, p.pos)
      maxOffset = maxOffset + typeByteSize(sfLocType)

      val mdescType = typeShaType
      m = m + sfDescId ~> VarInfo(isScalar(mdescType), maxOffset, typeByteSize(mdescType), 0, mdescType, p.pos)
      maxOffset = maxOffset + typeByteSize(mdescType)

      m = m + sfCurrentId ~> VarInfo(isScalar(spType), maxOffset, typeByteSize(spType), 0, spType, p.pos)
      maxOffset = maxOffset + typeByteSize(spType)
    }

    if (config.tempLocal) {
      for (param <- ops.ISZOps(p.paramNames).zip(p.tipe.args)) {
        val (id, tipe) = param
        val tempType: AST.Typed = if (config.splitTempSizes) if (isScalar(tipe)) tipe else spType else AST.Typed.u64
        val localTemp = tv.typeCount(this, tempType)
        tv = tv.incType(this, tempType)
        m = m + id ~> VarInfo(T, localTemp, 0, 0, if (isScalar(tipe)) tipe else spType, p.pos)
        if (isMain && !isScalar(tipe)) {
          val size = typeByteSize(tipe)
          m = m + s"$id$dataId" ~> VarInfo(F, maxOffset, size, 0, tipe, p.pos)
          maxOffset = maxOffset + size
        }
      }
    } else {
      for (param <- ops.ISZOps(p.paramNames).zip(p.tipe.args)) {
        val (id, t) = param
        val dataSize: Z = if (isMain && !isScalar(t)) typeByteSize(t) else 0
        val size: Z = if (isScalar(t)) typeByteSize(t) else typeByteSize(spType)
        m = m + id ~> VarInfo(isScalar(t), maxOffset, size, dataSize, t, p.pos)
        maxOffset = maxOffset + size + dataSize
      }
    }

    maxOffset = pad64(maxOffset)

    return (maxOffset, m)
  }

  def transformLocal(p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val paramInfo = procedureParamInfo(PBox(p))._2
    var tv = TempVector.empty
    var localTempMap: HashSMap[Z, HashSMap[String, Z]] = {
      var m = HashSMap.empty[String, Z]
      for (entry <- paramInfo.entries if !ignoredTempLocal.contains(entry._1) && isScalar(entry._2.tipe)) {
        val t: AST.Typed = if (config.splitTempSizes) entry._2.tipe else AST.Typed.u64
        m = m + entry._1 ~> tv.typeCount(this, t)
        tv = tv.incType(this, t)
      }
      HashSMap.empty[Z, HashSMap[String, Z]] + body.blocks(0).label ~> m
    }
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    var work = ISZ(body.blocks(0).label)
    var seen = HashSet.empty[Z] ++ work
    while (work.nonEmpty) {
      var next = ISZ[Z]()
      for (label <- work) {
        val b = blockMap.get(label).get
        var map = localTempMap.get(label).get
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        for (g <- b.grounds) {
          g match {
            case g: AST.IR.Stmt.Decl if !g.isAlloc =>
              var localTemps = ISZ[Intrinsic.Decl.Local]()
              var otherLocals = ISZ[AST.IR.Stmt.Decl.Local]()
              for (l <- g.locals) {
                if (isScalar(l.tipe) && !ignoredTempLocal.contains(l.id)) {
                  val loc: Z = if (g.undecl) {
                    val r = map.get(l.id).get
                    map = map -- ISZ(l.id)
                    r
                  } else {
                    val t: AST.Typed = if (config.splitTempSizes) l.tipe else AST.Typed.u64
                    val r = tv.typeCount(this, t)
                    tv = tv.incType(this, t)
                    map = map + l.id ~> r
                    r
                  }
                  localTemps = localTemps :+ Intrinsic.Decl.Local(loc, 0, l.id, l.tipe)
                } else {
                  otherLocals = otherLocals :+ l
                }
              }
              if (otherLocals.nonEmpty) {
                grounds = grounds :+ g(locals = otherLocals)
              }
              if (localTemps.nonEmpty) {
                grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(g.undecl, g.isAlloc, localTemps, g.pos))
              }
            case _ =>
              grounds = grounds :+ LocalTempSubstutitor(map).transform_langastIRStmtGround(g).getOrElse(g)
          }
        }
        blockMap = blockMap + b.label ~> b(grounds = grounds,
          jump = LocalTempSubstutitor(map).transform_langastIRJump(b.jump).getOrElse(b.jump))
        for (target <- b.jump.targets if !seen.contains(target)) {
          seen = seen + target
          localTempMap = localTempMap + target ~> map
          next = next :+ target
        }
      }
      work = next
    }
    return p(body = body(blocks = blockMap.values))
  }

  def transformIfLoadStoreCopyIntrinsic(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure, maxTemps: TempVector): AST.IR.Procedure = {
    @strictpure def shouldSplit(e: AST.IR.Exp): B = e match {
      case AST.IR.Exp.Intrinsic(in) => in.isInstanceOf[Intrinsic.Load] || in.isInstanceOf[Intrinsic.Indexing]
      case _ => e.isInstanceOf[AST.IR.Exp.Binary]
    }
    val spt: AST.Typed = if (config.splitTempSizes) spType else AST.Typed.u64
    val temp = maxTemps.typeCount(this, spt)
    val tempB: Z = if (config.splitTempSizes) maxTemps.typeCount(this, AST.Typed.b) else temp
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      b.grounds match {
        case ISZ(AST.IR.Stmt.Intrinsic(in@Intrinsic.TempLoad(_, base, _, _, _, _, _, _))) if shouldSplit(base) =>
          val label = fresh.label()
          val pos = base.pos
          blocks = blocks :+ b(grounds = ISZ(
            AST.IR.Stmt.Assign.Temp(temp, base, pos)
          ), jump = AST.IR.Jump.Goto(label, pos))
          blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(
            AST.IR.Stmt.Intrinsic(in(base = AST.IR.Exp.Temp(temp, spType, pos)))
          ), b.jump)
        case ISZ(AST.IR.Stmt.Intrinsic(in: Intrinsic.Copy)) if shouldSplit(in.lbase) =>
          val label = fresh.label()
          val pos = in.lbase.pos
          blocks = blocks :+ b(grounds = ISZ(
            AST.IR.Stmt.Assign.Temp(temp, in.lbase, pos)
          ), jump = AST.IR.Jump.Goto(label, pos))
          blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(
            AST.IR.Stmt.Intrinsic(in(lbase = AST.IR.Exp.Temp(temp, spType, pos)))
          ), b.jump)
        case ISZ(AST.IR.Stmt.Intrinsic(in: Intrinsic.Store)) if shouldSplit(in.base) =>
          val label = fresh.label()
          val pos = in.base.pos
          blocks = blocks :+ b(grounds = ISZ(
            AST.IR.Stmt.Assign.Temp(temp, in.base, pos)
          ), jump = AST.IR.Jump.Goto(label, pos))
          blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(
            AST.IR.Stmt.Intrinsic(in(base = AST.IR.Exp.Temp(temp, spType, pos)))
          ), b.jump)
        case _ =>
          b.jump match {
            case j: AST.IR.Jump.If if shouldSplit(j.cond) =>
              val label = fresh.label()
              val pos = j.cond.pos
              blocks = blocks :+ b(grounds = ISZ(
                AST.IR.Stmt.Assign.Temp(tempB, j.cond, pos)
              ), jump = AST.IR.Jump.Goto(label, pos))
              blocks = blocks :+ AST.IR.BasicBlock(label, b.grounds, j(cond = AST.IR.Exp.Temp(tempB, AST.Typed.b, pos)))
            case _ =>
              blocks = blocks :+ b
          }
      }
    }
    return p(body = body(blocks = blocks))
  }

  def transformOffset(globalMap: HashSMap[ISZ[String], VarInfo],
                      proc: AST.IR.Procedure): (Z, AST.IR.Procedure, HashMap[String, Z]) = {
    val body = proc.body.asInstanceOf[AST.IR.Body.Basic]
    var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- body.blocks) yield (b.label, b))
    var blockLocalOffsetMap = HashMap.empty[Z, (Z, Z, LocalOffsetInfo)]
    var callResultIdOffsetMap = HashMap.empty[String, Z]
    val offsetParamInfo = procedureParamInfo(PBox(proc))
    var maxOffset = offsetParamInfo._1
    val incomingMap = countNumOfIncomingJumps(body.blocks)
    val paramSet = HashSet ++ proc.paramNames
    blockLocalOffsetMap = blockLocalOffsetMap + body.blocks(0).label ~> (maxOffset, 0, LocalOffsetInfo(
      HashMap.empty[String, Z] ++ (for (entry <- offsetParamInfo._2.entries) yield (entry._1, entry._2.loc)), ISZ()))
    var work = ISZ(body.blocks(0))
    while (work.nonEmpty) {
      var next = ISZ[AST.IR.BasicBlock]()
      for (b <- work) {
        var (offset, _, m) = blockLocalOffsetMap.get(b.label).get
        var grounds = ISZ[AST.IR.Stmt.Ground]()
        for (g <- b.grounds) {
          g match {
            case g: AST.IR.Stmt.Decl =>
              var locals = ISZ[Intrinsic.Decl.Local]()
              for (l <- g.locals) {
                val size = typeByteSize(l.tipe)
                if (g.undecl) {
                  locals = locals :+ Intrinsic.Decl.Local(m.get(l.id).get, size, l.id, l.tipe)
                  val loffset = m.get(l.id).get
                  m = m -- ISZ(l.id)
                  if (loffset + size == offset) {
                    offset = offset - size
                  } else {
                    m = m.addFreeCell(LocalOffsetInfo.FreeCell(loffset, size))
                  }
                } else {
                  var loffset = offset
                  var found = F
                  for (i <- m.freeCells.indices if !found) {
                    val fc = m.freeCells(i)
                    if (fc.size >= size) {
                      found = T
                      loffset = fc.offset
                      val fcsOps = ops.ISZOps(m.freeCells)
                      m = m(freeCells = fcsOps.slice(0, i) ++ fcsOps.slice(i + 1, fcsOps.s.size))
                    }
                  }
                  m = m + l.id ~> loffset
                  if (!found) {
                    offset = offset + size
                  }
                  locals = locals :+ Intrinsic.Decl.Local(loffset, size, l.id, l.tipe)
                }
              }
              if (maxOffset < offset) {
                maxOffset = offset
              }
              grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Decl(g.undecl, g.isAlloc, locals, g.pos))
            case _ =>
              g match {
                case g@AST.IR.Stmt.Assign.Global(name, tipe, rhs, pos) =>
                  val globalInfo = globalMap.get(name).get
                  val newRhs = OffsetSubsitutor(this, paramSet, m, globalMap).transform_langastIRExp(rhs).getOrElse(rhs)
                  if (isTempGlobal(this, globalInfo.tipe, name)) {
                    grounds = grounds :+ g(rhs = newRhs)
                  } else {
                    val globalOffset = AST.IR.Exp.Int(spType, globalInfo.loc, pos)
                    if (isScalar(tipe) || name(name.size - 1) == resultLocalId) {
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(globalOffset, 0, isSigned(tipe),
                        typeByteSize(tipe), newRhs, g.prettyST(printer), tipe, g.pos))
                    } else {
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(globalOffset, 0, typeByteSize(tipe),
                        copySize(newRhs), newRhs, g.prettyST(printer), tipe, newRhs.tipe, g.pos))
                    }
                  }
                case AST.IR.Stmt.Assign.Local(_, lhs, t, rhs, pos) =>
                  val newRhs = OffsetSubsitutor(this, paramSet, m, globalMap).transform_langastIRExp(rhs).getOrElse(rhs)
                  val localOffset = m.get(lhs).get
                  if (isScalar(t)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                      AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, newRhs.pos)), localOffset, T, typeByteSize(t),
                      newRhs, st"$lhs = ${newRhs.prettyST(printer)}", t, pos))
                  } else {
                    if (paramSet.contains(lhs)) {
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(AST.IR.Exp.Intrinsic(
                        Intrinsic.Load(AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, newRhs.pos)), localOffset,
                          isSigned(spType), typeByteSize(spType), st"", spType, pos)), 0,
                        typeByteSize(t), copySize(newRhs), newRhs,
                        st"$lhs = ${newRhs.prettyST(printer)}", t, newRhs.tipe, pos))
                    } else {
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(
                        AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, newRhs.pos)), localOffset,
                        typeByteSize(t), copySize(newRhs), newRhs, st"$lhs = ${newRhs.prettyST(printer)}", t, newRhs.tipe, pos))
                    }
                  }
                case AST.IR.Stmt.Assign.Field(receiver, id, _, rhs, pos) =>
                  val (ft, foffset) = classSizeFieldOffsets(receiver.tipe.asInstanceOf[AST.Typed.Name])._2.get(id).get
                  if (isScalar(ft)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(receiver, foffset, isSigned(ft),
                      typeByteSize(ft), rhs, g.prettyST(printer), ft, pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(receiver, foffset, typeByteSize(ft),
                      copySize(rhs), rhs, g.prettyST(printer), ft, rhs.tipe, pos))
                  }
                case AST.IR.Stmt.Assign.Index(rcv, idx, rhs, pos) =>
                  val os = OffsetSubsitutor(this, paramSet, m, globalMap)
                  val newRhs = os.transform_langastIRExp(rhs).getOrElse(rhs)
                  val receiverOffset = indexing(os, rcv, idx, pos)
                  val elementType = rcv.tipe.asInstanceOf[AST.Typed.Name].args(1)
                  if (isScalar(elementType)) {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(receiverOffset, 0,
                      isSigned(elementType), typeByteSize(elementType), newRhs, g.prettyST(printer), elementType, g.pos))
                  } else {
                    grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Copy(receiverOffset, 0, typeByteSize(elementType),
                      copySize(newRhs), newRhs, g.prettyST(printer), elementType, newRhs.tipe, g.pos))
                  }
                case g@AST.IR.Stmt.Assign.Temp(n, rhs, pos) =>
                  rhs match {
                    case rhs: AST.IR.Exp.LocalVarRef =>
                      val localOffset = m.get(rhs.id).get
                      val temp = n
                      if (isScalar(rhs.tipe) || paramSet.contains(rhs.id)) {
                        val t: AST.Typed = if (isScalar(rhs.tipe)) rhs.tipe else spType
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp,
                          AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, rhs.pos)), localOffset, isSigned(t),
                          typeByteSize(t), g.prettyST(printer), t, pos))
                      } else {
                        val lhsOffset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(
                          Intrinsic.Register(T, spType, rhs.pos)), AST.IR.Exp.Binary.Op.Add,
                          AST.IR.Exp.Int(spType, localOffset, rhs.pos), rhs.pos)
                        grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, lhsOffset, pos)
                      }
                    case rhs: AST.IR.Exp.GlobalVarRef =>
                      val globalInfo = globalMap.get(rhs.name).get
                      if (isTempGlobal(this, globalInfo.tipe, rhs.name)) {
                        grounds = grounds :+ g
                      } else {
                        val temp = n
                        val globalOffset = AST.IR.Exp.Int(spType, globalInfo.loc, rhs.pos)
                        val t: AST.Typed = if (isScalar(rhs.tipe)) rhs.tipe else spType
                        if (isScalar(rhs.tipe)) {
                          grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp, globalOffset, 0,
                            isSigned(t), typeByteSize(t), g.prettyST(printer), t, pos))
                        } else {
                          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, globalOffset, rhs.pos)
                        }
                      }
                    case rhs: AST.IR.Exp.FieldVarRef =>
                      val receiver = OffsetSubsitutor(this, paramSet, m, globalMap).transform_langastIRExp(rhs.receiver).
                        getOrElse(rhs.receiver)
                      if (isSeq(rhs.receiver.tipe)) {
                        assert(rhs.id == "size")
                        val temp = n
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(
                          temp, receiver, typeShaSize, T, typeByteSize(rhs.tipe), g.prettyST(printer), rhs.tipe, pos))
                      } else {
                        val temp = n
                        val (ft, foffset) = classSizeFieldOffsets(rhs.receiver.tipe.asInstanceOf[AST.Typed.Name]).
                          _2.get(rhs.id).get
                        if (isScalar(ft)) {
                          grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(temp, receiver, foffset,
                            isSigned(ft), typeByteSize(ft), g.prettyST(printer), ft, pos))
                        } else {
                          val rhsOffset: AST.IR.Exp = if (foffset != 0) AST.IR.Exp.Binary(spType, receiver,
                            AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, foffset, rhs.pos), rhs.pos) else receiver
                          grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, rhsOffset, pos)
                        }
                      }
                    case rhs: AST.IR.Exp.Indexing =>
                      val rhsOffset = indexing(OffsetSubsitutor(this, paramSet, m, globalMap), rhs.exp, rhs.index, rhs.pos)
                      val elementType = rhs.tipe
                      if (isScalar(elementType)) {
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.TempLoad(n, rhsOffset, 0,
                          isSigned(elementType), typeByteSize(elementType), g.prettyST(printer), elementType, pos))
                      } else {
                        grounds = grounds :+ AST.IR.Stmt.Assign.Temp(n, rhsOffset, pos)
                      }
                    case rhs if isConstruct(rhs) =>
                      val loffset = m.get(constructResultId(rhs.pos)).get
                      val lhsOffset = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                        AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, loffset, g.pos),
                        g.pos)
                      grounds = grounds :+ g(rhs = lhsOffset)
                      val sha = sha3Type(rhs.tipe)
                      grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                        AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)), loffset, F, typeShaSize,
                        AST.IR.Exp.Int(AST.Typed.u32, sha.toZ, g.pos),
                        st"sha3 type signature of ${rhs.tipe}: 0x$sha", AST.Typed.u32, g.pos))
                      if (isSeq(rhs.tipe) || rhs.tipe == AST.Typed.string) {
                        val size: AST.IR.Exp = rhs match {
                          case rhs: AST.IR.Exp.String => AST.IR.Exp.Int(AST.Typed.z, conversions.String.toU8is(rhs.value).size, g.pos)
                          case rhs: AST.IR.Exp.Construct => AST.IR.Exp.Int(AST.Typed.z, rhs.args.size, g.pos)
                          case rhs: AST.IR.Exp.Apply => rhs.args(0)
                          case _ => halt(s"Infeasible")
                        }
                        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
                          AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)), loffset + typeShaSize,
                          isSigned(AST.Typed.z), typeByteSize(AST.Typed.z), size,
                          st"size of ${rhs.prettyST(printer)}", AST.Typed.z, g.pos))
                        if (rhs.isInstanceOf[AST.IR.Exp.Apply]) {
                          grounds = grounds :+ g(rhs = AST.IR.Exp.Binary(spType, AST.IR.Exp.Intrinsic(Intrinsic.Register(T, spType, g.pos)),
                            AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(spType, loffset, g.pos),
                            g.pos))
                          grounds = grounds :+ g
                        }
                      }
                    case _: AST.IR.Exp.If => halt(s"Infeasible: $rhs")
                    case _: AST.IR.Exp.Intrinsic => halt(s"Infeasible: $rhs")
                    case _ =>
                      grounds = grounds :+ OffsetSubsitutor(this, paramSet, m, globalMap).transform_langastIRStmtGround(g).getOrElse(g)
                  }
                case _ =>
                  grounds = grounds :+ OffsetSubsitutor(this, paramSet, m, globalMap).transform_langastIRStmtGround(g).getOrElse(g)
              }
              g match {
                case g: AST.IR.Stmt.Expr if g.exp.methodType.ret != AST.Typed.unit && (config.tempLocal __>: !isScalar(g.exp.methodType.ret)) =>
                  val id = callResultId(g.exp.id, g.exp.pos)
                  callResultIdOffsetMap = callResultIdOffsetMap + id ~> m.get(id).get
                case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] && (config.tempLocal __>: !isScalar(g.rhs.tipe)) =>
                  val e = g.rhs.asInstanceOf[AST.IR.Exp.Apply]
                  val id = callResultId(e.id, e.pos)
                  callResultIdOffsetMap = callResultIdOffsetMap + id ~> m.get(id).get
                case _ =>
              }
          }
        }
        blockMap = blockMap + b.label ~> b(grounds = grounds,
          jump = OffsetSubsitutor(this, paramSet, m, globalMap).transform_langastIRJump(b.jump).getOrElse(b.jump))
        for (target <- b.jump.targets) {
          blockLocalOffsetMap.get(target) match {
            case Some((po, jumps, pm)) =>
              var om = HashMap.empty[String, Z]
              for (k <- pm.offsetMap.keySet.intersect(m.offsetMap.keySet).elements) {
                val pv = pm.get(k).get
                val v = m.get(k).get
                assert(v == pv, s"m($k) = $v, pm($k) = $pv, m = $m, pm = $pm")
                om = om + k ~> v
              }
              val fcs = (HashSSet ++ m.freeCells).intersect(HashSSet ++ pm.freeCells).elements
              val targetOffset: Z = if (offset < po) po else offset
              blockLocalOffsetMap = blockLocalOffsetMap + target ~> (targetOffset, jumps + 1, LocalOffsetInfo(om, fcs))
            case _ =>
              blockLocalOffsetMap = blockLocalOffsetMap + target ~> (offset, 1, m)
          }
          if (blockLocalOffsetMap.get(target).get._2 <= incomingMap.get(target).get) {
            next = next :+ blockMap.get(target).get
          }
        }
      }
      work = next
    }
    return (maxOffset, proc(body = body(blocks = blockMap.values)), callResultIdOffsetMap)
  }

  def transformHalt(p: AST.IR.Procedure): AST.IR.Procedure = {
    if (!config.stackTrace) {
      return p
    }
    val id = "printStackTrace"
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      b.jump match {
        case _: AST.IR.Jump.Halt =>
          val pos = b.jump.pos
          val callerOffset = AST.IR.Exp.LocalVarRef(T, p.context, sfCurrentId, spType, pos)
          blocks = blocks :+ b(grounds = b.grounds ++ ISZ[AST.IR.Stmt.Ground](
            AST.IR.Stmt.Assign.Temp(0, AST.IR.Exp.Type(F, callerOffset, displayIndexType, pos), pos),
            AST.IR.Stmt.Expr(AST.IR.Exp.Apply(T, runtimeName, id, ISZ(
              AST.IR.Exp.Int(spType, 0, pos),
              AST.IR.Exp.Int(displayIndexType, typeByteSize(spType), pos),
              AST.IR.Exp.Int(displayIndexType, typeShaSize, pos),
              AST.IR.Exp.Int(displayIndexType, typeByteSize(sfLocType), pos),
              AST.IR.Exp.Int(displayIndexType, typeByteSize(AST.Typed.z), pos),
              AST.IR.Exp.Temp(0, displayIndexType, pos)
            ), runtimePrintMethodTypeMap.get(id).get, pos))
          ))
        case _ => blocks = blocks :+ b
      }
    }
    return p(body = body(blocks = blocks))
  }

  def dp(pos: message.Position): AST.IR.Exp = {
    return if (config.isFirstGen) AST.IR.Exp.Intrinsic(Intrinsic.Register(F, dpType, pos))
    else AST.IR.Exp.GlobalVarRef(dpName, dpType, pos)
  }

  @pure def printStringLit(fresh: lang.IRTranslator.Fresh, s: String, pos: message.Position): ISZ[AST.IR.Stmt.Ground] = {
    var r = ISZ[AST.IR.Stmt.Ground]()
    if (config.shouldPrint) {
      val cis = conversions.String.toCis(s)
      val register = dp(pos)
      if (config.isFirstGen) {
        var i = 0
        for (c <- cis) {
          for (byte <- conversions.String.toU8is(s"$c")) {
            val lhsOffset = AST.IR.Exp.Binary(dpType, register, AST.IR.Exp.Binary.Op.And, AST.IR.Exp.Int(dpType, dpMask, pos), pos)
            r = r :+ AST.IR.Stmt.Assign.Index(AST.IR.Exp.GlobalVarRef(displayName, displayType, pos), lhsOffset, AST.IR.Exp.Int(AST.Typed.u8, byte.toZ, pos), pos)
            r = r :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, T, AST.IR.Exp.Int(dpType, 1, pos), pos))
            i = i + 1
          }
        }
      } else {
        var i = 0
        val dpTemp = fresh.temp()
        val offsetTemp = fresh.temp()
        val dpExp = AST.IR.Exp.Temp(dpTemp, dpType, pos)
        val offsetExp = AST.IR.Exp.Temp(offsetTemp, dpType, pos)
        r = r :+ AST.IR.Stmt.Assign.Temp(dpTemp, register, pos)
        for (c <- cis) {
          for (byte <- conversions.String.toU8is(s"$c")) {
            val lhsOffset = AST.IR.Exp.Binary(dpType, dpExp, AST.IR.Exp.Binary.Op.And, AST.IR.Exp.Int(dpType, dpMask, pos), pos)
            r = r :+ AST.IR.Stmt.Assign.Temp(offsetTemp, lhsOffset, pos)
            r = r :+ AST.IR.Stmt.Assign.Index(AST.IR.Exp.GlobalVarRef(displayName, displayType, pos), offsetExp, AST.IR.Exp.Int(AST.Typed.u8, byte.toZ, pos), pos)
            r = r :+ AST.IR.Stmt.Assign.Temp(dpTemp, AST.IR.Exp.Binary(dpType, dpExp, AST.IR.Exp.Binary.Op.Add, AST.IR.Exp.Int(dpType, 1, pos), pos), pos)
            i = i + 1
          }
        }
        r = r :+ AST.IR.Stmt.Assign.Global(dpName, dpType, dpExp, pos)
      }
    }
    return r
  }

  def transformPrint(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      val nextTemp = nextBlockTemp(b)
      fresh.setTemp(nextTemp)
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      for (g <- b.grounds) {
        g match {
          case AST.IR.Stmt.Expr(e) if e.isInObject && e.owner == AST.Typed.sireumName &&
            (e.id == "print" || e.id == "eprint" || e.id == "cprint") =>
            e.args(if (e.id == "cprint") 1 else 0) match {
              case arg: AST.IR.Exp.Bool =>
                grounds = grounds ++ printStringLit(fresh, if (arg.value) "T" else "F", arg.pos)
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
                  grounds = grounds ++ printStringLit(fresh, conversions.String.fromU8ms(u8ms), arg.pos)
                } else if (arg.tipe == AST.Typed.c) {
                  val buffer = MS.create[anvil.PrinterIndex.U, U8](4, u8"0")
                  val n = anvil.Runtime.printC(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask),
                    conversions.U32.toC(conversions.Z.toU32(arg.value))).toZ
                  val u8ms = MSZ.create(n, u8"0")
                  for (i <- 0 until n) {
                    u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                  }
                  grounds = grounds ++ printStringLit(fresh, conversions.String.fromU8ms(u8ms), arg.pos)
                } else {
                  val buffer = MS.create[anvil.PrinterIndex.U, U8](20, u8"0")
                  val n: Z =
                    if (isSigned(arg.tipe)) anvil.Runtime.printS64(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), conversions.Z.toS64(arg.value)).toZ
                    else anvil.Runtime.printU64(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), conversions.Z.toU64(arg.value)).toZ
                  val u8ms = MSZ.create(n, u8"0")
                  for (i <- 0 until n) {
                    u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                  }
                  grounds = grounds ++ printStringLit(fresh, conversions.String.fromU8ms(u8ms), arg.pos)
                }
              case arg: AST.IR.Exp.F32 =>
                val buffer = MS.create[anvil.PrinterIndex.U, U8](50, u8"0")
                val n = anvil.Runtime.printF32_2(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), arg.value).toZ
                val u8ms = MSZ.create(n, u8"0")
                for (i <- 0 until n) {
                  u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                }
                grounds = grounds ++ printStringLit(fresh, conversions.String.fromU8ms(u8ms), arg.pos)
              case arg: AST.IR.Exp.F64 =>
                val buffer = MS.create[anvil.PrinterIndex.U, U8](320, u8"0")
                val n = anvil.Runtime.printF64_2(buffer, u"0", anvil.Runtime.Ext.z2u(dpMask), arg.value).toZ
                val u8ms = MSZ.create(n, u8"0")
                for (i <- 0 until n) {
                  u8ms(i) = buffer(anvil.Runtime.Ext.z2u(i))
                }
                grounds = grounds ++ printStringLit(fresh, conversions.String.fromU8ms(u8ms), arg.pos)
              case arg: AST.IR.Exp.R => halt(s"TODO: $arg")
              case arg: AST.IR.Exp.String => grounds = grounds ++ printStringLit(fresh, arg.value, arg.pos)
              case arg =>
                val pos = g.pos
                val buffer = AST.IR.Exp.GlobalVarRef(displayName, displayType, pos)
                val index: AST.IR.Exp = if (config.isFirstGen) {
                  dp(pos)
                } else {
                  val dpTemp = fresh.temp()
                  grounds = grounds :+ AST.IR.Stmt.Assign.Temp(dpTemp, AST.IR.Exp.GlobalVarRef(dpName, dpType, pos), pos)
                  AST.IR.Exp.Temp(dpTemp, dpType, pos)
                }
                val mask = AST.IR.Exp.Int(displayIndexType, dpMask, pos)
                val printApply: AST.IR.Exp.Apply = arg.tipe match {
                  case AST.Typed.b =>
                    val id = "printB"
                    val mt = runtimePrintMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, pos)
                  case AST.Typed.c =>
                    val id = "printC"
                    val mt = runtimePrintMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, pos)
                  case AST.Typed.z =>
                    val id = "printS64"
                    val mt = runtimePrintMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, AST.IR.Exp.Type(F, arg, AST.Typed.s64, pos)), mt, pos)
                  case AST.Typed.f32 =>
                    val id = "printF32_2"
                    val mt = runtimePrintMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, pos)
                  case AST.Typed.f64 =>
                    val id = "printF64_2"
                    val mt = runtimePrintMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, pos)
                  case AST.Typed.string =>
                    val id = "printString"
                    val mt = runtimePrintMethodTypeMap.get(id).get
                    AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, arg), mt, pos)
                  case t if subZOpt(t).nonEmpty =>
                    if (isBitVector(t) && !isSigned(t)) {
                      val digits = AST.IR.Exp.Int(AST.Typed.z, typeByteSize(t) * 2, pos)
                      val id = "printU64Hex"
                      val mt = runtimePrintMethodTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.u64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.u64, pos)
                      }
                      AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, a, digits), mt, pos)
                    } else if (isSigned(t)) {
                      val id = "printS64"
                      val mt = runtimePrintMethodTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.s64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.s64, pos)
                      }
                      AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, a), mt, pos)
                    } else {
                      val id = "printU64"
                      val mt = runtimePrintMethodTypeMap.get(id).get
                      var a = arg
                      if (a.tipe != AST.Typed.u64) {
                        a = AST.IR.Exp.Type(F, a, AST.Typed.u64, pos)
                      }
                      AST.IR.Exp.Apply(T, runtimeName, id, ISZ(buffer, index, mask, a), mt, pos)
                    }
                  case AST.Typed.r => halt(s"TODO: $arg")
                  case t => halt(s"TODO: $t, $arg")
                }
                val temp = fresh.temp()
                grounds = grounds :+ AST.IR.Stmt.Assign.Temp(temp, printApply, pos)
                val inc = AST.IR.Exp.Type(F, AST.IR.Exp.Temp(temp, AST.Typed.u64, pos), dpType, pos)
                if (config.isFirstGen) {
                  grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, T, inc, pos))
                } else {
                  val dpTemp = fresh.temp()
                  val dpTempExp = AST.IR.Exp.Temp(dpTemp, dpType, pos)
                  grounds = grounds :+ AST.IR.Stmt.Assign.Temp(dpTemp, AST.IR.Exp.GlobalVarRef(dpName, dpType, pos), pos)
                  grounds = grounds :+ AST.IR.Stmt.Assign.Temp(dpTemp,
                    AST.IR.Exp.Binary(dpType, dpTempExp, AST.IR.Exp.Binary.Op.Add, inc, pos), pos)
                  grounds = grounds :+ AST.IR.Stmt.Assign.Global(dpName, dpType, dpTempExp, pos)
                }
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
            val label = fresh.label()
            val tLabel = fresh.label()
            val fLabel = fresh.label()
            val eLabel = fresh.label()
            blocks = blocks :+ AST.IR.BasicBlock(b.label, grounds :+ AST.IR.Stmt.Assign.Temp(lhs,
              AST.IR.Exp.FieldVarRef(rhs.exp, typeFieldId, typeShaType, pos), pos), AST.IR.Jump.Goto(label, pos))
            blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(), AST.IR.Jump.Switch(
              AST.IR.Exp.Temp(lhs, typeShaType, pos),
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
                  printStringLit(fresh, s"Cannot cast to ${rhs.t}\n", pos),
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

  def transformIpSubroutines(fresh: lang.IRTranslator.Fresh,
                             p: AST.IR.Procedure,
                             gm: HashSMap[QName, VarInfo]): (AST.IR.Procedure, HashSMap[QName, VarInfo]) = {
    val pos = p.pos
    var ipBlocks = ISZ[AST.IR.BasicBlock]()
    var binopLocMap = HashMap.empty[(AST.IR.Exp.Binary.Op.Type, B), Z]
    var globalMap = gm
    @pure def initLoc: Z = {
      var r: Z = 0
      for (p <- globalMap.entries) {
        val (name, info) = p
        if (isTempGlobal(this, info.tipe, name) && r < info.loc) {
          r = info.loc
        }
      }
      return r
    }
    var loc = initLoc + 1

    def addBinop(op: AST.IR.Exp.Binary.Op.Type, isSigned: B, returnType: AST.Typed): Unit = {
      if (binopLocMap.get((op, isSigned)).nonEmpty) {
        return
      }
      val t: AST.Typed = if (isSigned) AST.Typed.s64 else AST.Typed.u64
      val opGlobalName = binopSignGlobalName(op, isSigned)
      val ret = opGlobalName :+ returnLocalId
      val l = opGlobalName :+ binopLeftId
      val r = opGlobalName :+ binopRightId
      val v = opGlobalName :+ resultLocalId
      val retInfo = VarInfo(T, loc, typeByteSize(cpType), 0, cpType, pos)
      globalMap = globalMap + ret ~> retInfo
      loc = loc + 1
      val lInfo = VarInfo(T, loc, typeByteSize(t), 0, t, pos)
      globalMap = globalMap + l ~> lInfo
      loc = loc + 1
      val rInfo = VarInfo(T, loc, typeByteSize(t), 0, t, pos)
      globalMap = globalMap + r ~> rInfo
      loc = loc + 1
      val vInfo = VarInfo(T, loc, typeByteSize(returnType), 0, returnType, pos)
      globalMap = globalMap + v ~> vInfo
      loc = loc + 1

      val label = fresh.label()
      val end = fresh.label()
      ipBlocks = ipBlocks :+ AST.IR.BasicBlock(label, ISZ(
        AST.IR.Stmt.Assign.Global(v, vInfo.tipe,
          AST.IR.Exp.Binary(lInfo.tipe, AST.IR.Exp.GlobalVarRef(l, lInfo.tipe, pos), op,
            AST.IR.Exp.GlobalVarRef(r, rInfo.tipe, pos), pos), pos)),
        AST.IR.Jump.Goto(end, pos))
      ipBlocks = ipBlocks :+ AST.IR.BasicBlock(end, ISZ(), AST.IR.Jump.Intrinsic(Intrinsic.GotoGlobal(ret, pos)))
      binopLocMap = binopLocMap + (op, isSigned) ~> label
    }
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    var blocks = ISZ[AST.IR.BasicBlock]()
    for (b <- body.blocks) {
      var grounds = ISZ[AST.IR.Stmt.Ground]()
      var labelOpt = Option.none[Z]()
      for (g <- b.grounds) {
        g match {
          case g@AST.IR.Stmt.Assign.Temp(_, e@AST.IR.Exp.Binary(t: AST.Typed.Name, l, op, r, epos), _) =>
            assert(labelOpt.isEmpty, s"There are multiple IPs in the same block: ${b.prettyST(printer)}")
            val label = fresh.label()
            val sign = isSigned(l.tipe)
            addBinop(op, sign, t)
            val ipLoc = binopLocMap.get((op, sign)).get
            val gname = binopSignGlobalName(op, sign)
            blocks = blocks :+ b(grounds = ISZ[AST.IR.Stmt.Ground](
              AST.IR.Stmt.Assign.Global(gname :+ returnLocalId, cpType, AST.IR.Exp.Int(cpType, label, epos), epos),
              AST.IR.Stmt.Assign.Global(gname :+ binopLeftId, l.tipe, l, epos),
              AST.IR.Stmt.Assign.Global(gname :+ binopRightId, r.tipe, r, epos)
            ), jump = AST.IR.Jump.Goto(ipLoc, epos))
            val res = gname :+ resultLocalId
            val resType = globalMap.get(res).get.tipe
            var rhs: AST.IR.Exp = AST.IR.Exp.GlobalVarRef(gname :+ resultLocalId, e.tipe, epos)
            if (resType != res) {
              rhs = AST.IR.Exp.Type(F, rhs, t, epos)
            }
            grounds = grounds :+ g(rhs = rhs)
            labelOpt = Some(label)
          case _ => grounds = grounds :+ g
        }
      }
      labelOpt match {
        case Some(label) => blocks = blocks :+ AST.IR.BasicBlock(label, grounds, b.jump)
        case _ => blocks = blocks :+ b
      }
    }
    return (p(body = body(blocks = blocks ++ ipBlocks)), globalMap)
  }

  def transformMain(fresh: lang.IRTranslator.Fresh, p: AST.IR.Procedure, globalSize: Z, globalMap: HashSMap[QName, VarInfo]): AST.IR.Procedure = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    assert(config.alignAxi4 ->: (globalSize % 8 == 0))
    var grounds = ISZ[AST.IR.Stmt.Ground](
      AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(T, F, AST.IR.Exp.Int(spType, globalSize, p.pos), p.pos))
    )
    var stores = ISZ[AST.IR.Stmt.Ground]()
    if (config.stackTrace) {
      val memInfo = globalMap.get(memName).get
      val memTypeInfo = globalMap.get(memTypeName).get
      val memSizeInfo = globalMap.get(memSizeName).get
      val sha3t = sha3Type(displayType)
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, memInfo.loc, p.pos), 0, isSigned(spType), typeByteSize(spType),
        AST.IR.Exp.Int(spType, memTypeInfo.loc, p.pos), st"${memName(0)}", spType, p.pos))
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, memTypeInfo.loc, p.pos), 0, isSigned(typeShaType), typeShaSize,
        AST.IR.Exp.Int(typeShaType, sha3t.toZ, p.pos), st"memory $typeFieldId ($displayType: 0x$sha3t)", typeShaType, p.pos))
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, memSizeInfo.loc, p.pos), 0, isSigned(AST.Typed.z), typeByteSize(AST.Typed.z),
        AST.IR.Exp.Int(AST.Typed.z, config.memory, p.pos), st"memory $sizeFieldId", AST.Typed.z, p.pos))
      val sfCallerInfo = procedureParamInfo(PBox(p))._2.get(sfCallerId).get
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, globalSize + sfCallerInfo.loc, p.pos), 0, isSigned(spType), typeByteSize(spType),
        AST.IR.Exp.Int(spType, 0, p.pos), st"$sfCallerId = 0", spType, p.pos))
    }
    if (config.shouldPrint) {
      if (config.isFirstGen) {
        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(F, F, AST.IR.Exp.Int(dpType, 0, p.pos), p.pos))
      } else {
        val displayInfo = globalMap.get(dpName).get
        grounds = grounds :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(AST.IR.Exp.Int(spType, displayInfo.loc, p.pos), 0,
          isSigned(dpType), typeByteSize(dpType), AST.IR.Exp.Int(dpType, 0, p.pos), st"", dpType, p.pos))
      }
      val displayInfo = globalMap.get(displayName).get
      val sha3t = sha3Type(displayType)
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(typeShaType, displayInfo.loc + typeByteSize(spType), p.pos), 0, isSigned(typeShaType), typeShaSize,
        AST.IR.Exp.Int(typeShaType, sha3t.toZ, p.pos), st"$displayId.$typeFieldId ($displayType: 0x$sha3t)", typeShaType, p.pos))
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, displayInfo.loc + typeByteSize(spType) + typeByteSize(typeShaType), p.pos), 0,
        isSigned(AST.Typed.z), typeByteSize(AST.Typed.z),
        AST.IR.Exp.Int(AST.Typed.z, dpMask + 1, p.pos), st"$displayId.size", AST.Typed.z, p.pos))
    }
    val paramInfo = procedureParamInfo(PBox(p))._2
    if (config.tempLocal) {
      grounds = grounds :+ AST.IR.Stmt.Assign.Temp(paramInfo.get(returnLocalId).get.loc,
        AST.IR.Exp.Int(cpType, 0, p.pos), p.pos)
    } else {
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(cpType, globalSize + paramInfo.get(returnLocalId).get.loc, p.pos), 0, isSigned(cpType),
        typeByteSize(cpType), AST.IR.Exp.Int(cpType, 0, p.pos), st"$returnLocalId", cpType, p.pos))
    }
    if (p.tipe.ret != AST.Typed.unit) {
      val offset = paramInfo.get(resultLocalId).get.loc
      stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
        AST.IR.Exp.Int(spType, offset, p.pos), 0, isSigned(spType), typeByteSize(spType),
        AST.IR.Exp.Int(spType, offset + typeByteSize(spType), p.pos), st"data address of $resultLocalId (size = ${typeByteSize(p.tipe.ret)})", spType, p.pos))
    }
    for (pid <- p.paramNames) {
      val info = paramInfo.get(pid).get
      if (!isScalar(info.tipe)) {
        stores = stores :+ AST.IR.Stmt.Intrinsic(Intrinsic.Store(
          AST.IR.Exp.Int(spType, info.loc, p.pos), 0, isSigned(spType), typeByteSize(spType),
          AST.IR.Exp.Int(spType, info.loc + typeByteSize(spType), p.pos), st"data address of $pid (size = ${typeByteSize(info.tipe)})", spType, p.pos))
      }
    }
    var blocks = ISZ(AST.IR.BasicBlock(fresh.label(), grounds, AST.IR.Jump.Goto(startingLabel, p.pos)))
    for (g <- stores) {
      val label = fresh.label()
      val last = blocks.size - 1
      val lastBlock = blocks(last)
      blocks = blocks(last ~> lastBlock(jump = AST.IR.Jump.Goto(label, p.pos)))
      blocks = blocks :+ AST.IR.BasicBlock(label, ISZ(g), AST.IR.Jump.Goto(startingLabel, p.pos))
    }
    return p(body = body(blocks ++ body.blocks))
  }

  @memoize def subZOpt(t: AST.Typed): Option[TypeInfo.SubZ] = {
    t match {
      case t: AST.Typed.Name =>
        th.typeMap.get(t.ids) match {
          case Some(ti: TypeInfo.SubZ) => return Some(ti)
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
      if (t == AST.Typed.string) {
        offset = offset + config.maxStringSize
      } else if (t.args(1) == AST.Typed.b) {
        offset = offset + getMaxArraySize(t)
      } else {
        offset = offset + getMaxArraySize(t) * typeByteSize(t.args(1))
      }
      offset = pad64(offset + typeByteSize(AST.Typed.z))
      //println(s"$t (max: $offset) = $r")
      return (offset, r)
    }
    val info = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
    val sm = TypeChecker.buildTypeSubstMap(t.ids, None(), info.ast.typeParams, t.args, message.Reporter.create).get
    val vars = info.vars.values
    var fieldTypes = HashMap.empty[String, AST.Typed]
    for (v <- vars) {
      fieldTypes = fieldTypes + v.ast.id.value ~> v.typedOpt.get.subst(sm)
    }
    @strictpure def fLt(f1: String, f2: String): B = {
      val f1Size = typeByteSize(fieldTypes.get(f1).get)
      val f2Size = typeByteSize(fieldTypes.get(f2).get)
      if (f1Size < f2Size) F
      else if (f1Size > f2Size) T
      else f1 <= f2
    }
    if (config.alignAxi4 && ops.ISZOps(fieldTypes.values).exists((t: AST.Typed) => !isScalar(t))) {
      offset = pad64(offset)
    }
    for (f <- ops.ISZOps(fieldTypes.keys).sortWith(fLt _)) {
      val ft = fieldTypes.get(f).get
      r = r + f ~> (ft, offset)
      offset = offset + typeByteSize(ft)
    }
    offset = pad64(offset)
    //println(s"$t (max: $offset) = $r")
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
          if (subz.ast.isBitVector) {
            return if (size < config.maxArraySize) size else config.maxStringSize
          } else {
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

  @strictpure def is1Bit(t: AST.Typed): B = if (t == AST.Typed.b) {
    T
  } else {
    subZOpt(t) match {
      case Some(info) => info.ast.isBitVector && info.ast.bitWidth == 1
      case _ => F
    }
  }

  @memoize def typeBitSize(t: AST.Typed): Z = {
    if (is1Bit(t)) {
      return 1
    }
    return typeByteSize(t) * 8
  }

  @strictpure def pad64(r: Z): Z = if (config.padObject64) 8 * (r / 8 + (if (r % 8 != 0) 1 else 0)) else r

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

    def typeByteSizeH: Z = {
      t match {
        case AST.Typed.b => return 1
        case AST.Typed.c => return 4
        case AST.Typed.z => return numOfBytes(config.defaultBitWidth)
        case AST.Typed.f32 => return 4
        case AST.Typed.f64 => return 8
        case AST.Typed.r => return 8
        case AST.Typed.string => return classSizeFieldOffsets(AST.Typed.string)._1
        case AST.Typed.unit => return 0
        case AST.Typed.nothing => return 0
        case `dpType` => return dpTypeByteSize
        case Util.spType => return spTypeByteSize
        case `cpType` =>
          assert(numOfLocs != 0, "Number of locations for CP has not been initialized")
          return cpTypeByteSize
        case t: AST.Typed.Name =>
          if (t.ids.size == 1 && t.args.isEmpty && Z(t.ids(0)).nonEmpty) {
            return 8
          }
          if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
            return classSizeFieldOffsets(t)._1
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
          var r: Z = typeShaSize // type sha
          for (arg <- t.args) {
            r = r + typeByteSize(arg)
          }
          return r
        case t => halt(s"Infeasible: $t")
      }
    }

    var r = typeByteSizeH
    if (!isScalar(t)) {
      r = pad64(r)
    }
    return r
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
      case Util.spType =>
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
    assert(!isScalar(t), s"$exp: $t")
    val pos = exp.pos
    if (config.memoryAccess == Config.MemoryAccess.Default && (t == AST.Typed.string || (isSeq(t) && !config.erase))) {
      val (sizeType, sizeOffset) = classSizeFieldOffsets(t.asInstanceOf[AST.Typed.Name])._2.get("size").get
      val elementByteSize: Z = if (t == AST.Typed.string) 1 else typeByteSize(t.asInstanceOf[AST.Typed.Name].args(1))
      var elementSize: AST.IR.Exp = AST.IR.Exp.Type(F,
        AST.IR.Exp.Intrinsic(Intrinsic.Load(
          exp, sizeOffset, isSigned(sizeType), typeByteSize(sizeType), st"", sizeType, pos)),
        spType, pos)
      if (elementByteSize != 1) {
        elementSize = AST.IR.Exp.Binary(spType, elementSize, AST.IR.Exp.Binary.Op.Mul,
          AST.IR.Exp.Int(spType, elementByteSize, pos), pos)
      }
      return AST.IR.Exp.Binary(spType, elementSize, AST.IR.Exp.Binary.Op.Add,
        AST.IR.Exp.Int(spType, typeShaSize + typeByteSize(AST.Typed.z), pos), pos)
    } else {
      return AST.IR.Exp.Int(spType, typeByteSize(t), pos)
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

  @strictpure def isFP(t: AST.Typed): B = t match {
    case AST.Typed.f32 => T
    case AST.Typed.f64 => T
    case _ => F
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
      case Util.spType => return F
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
      case Util.spType => 0
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

  @pure def nextBlockTemp(b: AST.IR.BasicBlock): Z = {
    val tc = TempCollector(F, HashSMap.empty)
    tc.transform_langastIRBasicBlock(b)
    for (g <- b.grounds) {
      g match {
        case g: AST.IR.Stmt.Assign.Temp => tc.r = tc.r + g.lhs ~> (tc.r.get(g.lhs).getOrElse(HashSSet.empty[AST.Typed] + g.rhs.tipe))
        case _ =>
      }
    }
    var max: Z = 0
    for (t <- tc.r.keys) {
      if (max <= t) {
        max = max + 1
      }
    }
    return max
  }

  @strictpure def allocTypeNamed(isImmutable: B, numOfBytes: Z): AST.Typed.Name = AST.Typed.Name(
    if (isImmutable) AST.Typed.isName else AST.Typed.msName,
    ISZ(AST.Typed.Name(ISZ(s"$numOfBytes"), ISZ()), AST.Typed.u8))

  @memoize def procMaxTemps(anvil: Anvil, pbox: PBox): TempVector = {
    val tmc = TempMaxCounter(anvil, HashSet.empty, TempVector.empty)
    tmc.transform_langastIRProcedure(pbox.p)
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
}