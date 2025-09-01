// #Sireum
/*
 Copyright (c) 2017-2025, Kejun Chen, Kansas State University
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
import org.sireum.anvil.Anvil.VarInfo
import org.sireum.anvil.Util.{AnvilIRPrinter, constructLocalId, indexing, isTempGlobal, spType}
import org.sireum.lang.ast.{IR, Typed}
import org.sireum.lang.ast.IR.{Exp, Jump}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Resolver.{QName, addBuiltIns, typeParamMap}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Position

import HwSynthesizer2._
@record class HwSynthesizer2(val anvil: Anvil) {
  val sharedMemName: String = "arrayRegFiles"
  val generalRegName: String = "generalRegFiles"

  var ipAlloc: Util.IpAlloc = Util.IpAlloc(HashSMap.empty, HashSMap.empty, 0)
  val hwLog: HwSynthesizer2.HwLog = HwSynthesizer2.HwLog(0, MNone(), F, F, 0, 0, 0)

  val xilinxIPValid: B = if(anvil.config.useIP) anvil.config.noXilinxIp else T
  var ipModules: ISZ[ChiselModule] = ISZ[ChiselModule](
    Adder(F, "AdderUnsigned64", "adderUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Add, F), xilinxIPValid),
    Adder(T, "AdderSigned64", "adderSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Add, T), xilinxIPValid),
    Subtractor(F, "SubtractorUnsigned64", "subtractorUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Sub, F), xilinxIPValid),
    Subtractor(T, "SubtractorSigned64", "subtractorSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Sub, T), xilinxIPValid),
    Indexer(F, "Indexer", "indexer", anvil.typeBitSize(spType), IntrinsicIP(defaultIndexing), xilinxIPValid),
    And(F, "AndUnsigned64", "andUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.And, F)),
    And(T, "AndSigned64", "andSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.And, T)),
    Or(F, "OrUnsigned64", "orUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Or, F)),
    Or(T, "OrSigned64", "orSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Or, T)),
    Xor(F, "XorUnsigned64", "xorUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Xor, F)),
    Xor(T, "XorSigned64", "xorSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Xor, T)),
    Eq(F, "EqUnsigned64", "eqUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Eq, F)),
    Eq(T, "EqSigned64", "eqSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Eq, T)),
    Ne(F, "NeUnsigned64", "neUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Ne, F)),
    Ne(T, "NeSigned64", "neSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Ne, T)),
    Gt(F, "GtUnsigned64", "gtUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Gt, F)),
    Gt(T, "GtSigned64", "gtSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Gt, T)),
    Ge(F, "GeUnsigned64", "geUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Ge, F)),
    Ge(T, "GeSigned64", "geSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Ge, T)),
    Lt(F, "LtUnsigned64", "ltUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Lt, F)),
    Lt(T, "LtSigned64", "ltSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Lt, T)),
    Le(F, "LeUnsigned64", "leUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Le, F)),
    Le(T, "LeSigned64", "leSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Le, T)),
    Shr(F, "ShrUnsigned64", "shrUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Shr, F)),
    Shr(T, "ShrSigned64", "shrSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Shr, T)),
    Shl(F, "ShlUnsigned64", "shlUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Shl, F)),
    Shl(T, "ShlSigned64", "shlSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Shl, T)),
    Ushr(F, "UshrUnsigned64", "ushrUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Ushr, F)),
    Ushr(T, "UshrSigned64", "ushrSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Ushr, T)),
    Multiplier(F, "MultiplierUnsigned64", "multiplierUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Mul, F), xilinxIPValid),
    Multiplier(T, "MultiplierSigned64", "multiplierSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Mul, T), xilinxIPValid),
    Division(F, "DivisionUnsigned64", "divisionUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Div, F), xilinxIPValid),
    Division(T, "DivisionSigned64", "divisionSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Div, T), xilinxIPValid),
    Remainder(F, "RemainerUnsigned64", "remainerUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Rem, F), xilinxIPValid),
    Remainder(T, "RemainerSigned64", "remainerSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Rem, T), xilinxIPValid),
    BlockMemory(T, "BlockMemory", s"${sharedMemName}", 8, anvil.config.memory, BlockMemoryIP(), anvil.config.memoryAccess, anvil.config.genVerilog, anvil.config.erase, anvil.config.alignAxi4),
    LabelToFsm(F, "LabelToFsmIP", "labelToFsmIp", 0, LabelToFsmIP())
  )

  @strictpure def getCpIndex(label: Z): (Z, Z) = (label / anvil.config.cpMax, label % anvil.config.cpMax)

  @pure def findChiselModule(ip: IpType): Option[ChiselModule] = {
    for(i <- 0 until ipModules.size) {
      if(ipModules(i).expression == ip) {
        return Some(ipModules(i))
      }
    }
    return None()
  }

  @pure def getIpArbiterTemplate(ip: IpType): ST = {
    val mod = findChiselModule(ip).get

    @pure def requestBundleST: ST = {
      var portST: ISZ[ST] = ISZ[ST]()

      ip match {
        case BinaryIP(_, _) =>
          for(i <- mod.portListWithoutControl.entries) {
            portST = portST :+ st"val ${i._1} = ${i._2}(dataWidth.W)"
          }
        case IntrinsicIP(_) => halt("IP arbiter template, IntrinsicIP not impl")
        case BlockMemoryIP() => halt("IP arbiter template, BlockMemoryIP not impl")
        case LabelToFsmIP() => halt("IP arbiter template, LabelToFsmIP not impl")
      }

      return st"""
                 |class ${mod.moduleName}RequestBundle(dataWidth: Int) extends Bundle {
                 |  ${(portST, "")}
                 |}
               """
    }

    @pure def responseBundleST: ST = {
      var portST: ISZ[ST] = ISZ[ST]()

      ip match {
        case BinaryIP(_, _) =>
          val signedStr: String = if (mod.signed) "SInt" else "UInt"
          portST = portST :+ st"val out = ${signedStr}(dataWidth.W)"
        case IntrinsicIP(_) => halt("IP arbiter template, IntrinsicIP not impl")
        case BlockMemoryIP() => halt("IP arbiter template, BlockMemoryIP not impl")
        case LabelToFsmIP() => halt("IP arbiter template, LabelToFsmIP not impl")
      }

      return st"""
                 |class ${mod.moduleName}ResponseBundle(dataWidth: Int) extends Bundle {
                 |  ${(portST, "")}
                 |}
               """
    }

    @pure def IpIOST: ST = {
      return st"""
                 class ${mod.moduleName}IO(dataWidth: Int) extends Bundle {
                   val req = Valid(new ${mod.moduleName}RequestBundle(dataWidth))
                   val resp = Flipped(Valid(new ${mod.moduleName}ResponseBundle(dataWidth)))
                 }
               """
    }

    @pure def IpArbiterIOST: ST = {
      return st"""
                 |class ${mod.moduleName}ArbiterIO(numIPs: Int, dataWidth: Int) extends Bundle {
                 |  val ipReqs  = Flipped(Vec(numIPs, Valid(new ${mod.moduleName}RequestBundle(dataWidth))))
                 |  val ipResps = Vec(numIPs, Valid(new ${mod.moduleName}ResponseBundle(dataWidth)))
                 |  val ip      = new ${mod.moduleName}IO(dataWidth)
                 |}
               """
    }

    @pure def arbiterModuleST: ST = {
      return st"""
                 |class ${mod.moduleName}ArbiterModule(numIPs: Int, dataWidth: Int) extends Module {
                 |  val io = IO(new ${mod.moduleName}ArbiterIO(numIPs, dataWidth))
                 |
                 |  // ------------------ Stage 0: Input Cache ------------------
                 |  val r_ipReq_valid = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
                 |  val r_ipReq_valid_next = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
                 |  val r_ipReq_enable = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
                 |  val r_ipReq_bits = Reg(Vec(numIPs, new MultiplyRequestBundle(dataWidth)))
                 |
                 |  for (i <- 0 until numIPs) {
                 |    r_ipReq_valid(i) := io.ipReqs(i).valid
                 |    r_ipReq_valid_next(i) := r_ipReq_valid(i)
                 |    when(r_ipReq_valid(i) & ~r_ipReq_valid_next(i)) {
                 |      r_ipReq_enable(i) := true.B
                 |      r_ipReq_bits(i) := io.ipReqs(i).bits
                 |    } .otherwise {
                 |      r_ipReq_enable(i) := false.B
                 |    }
                 |  }
                 |
                 |  // ------------------ Stage 1: Arbitration Decision Pipeline ------------------
                 |  val r_foundReq = RegInit(false.B)
                 |  val r_reqBits  = Reg(new ${mod.moduleName}RequestBundle(dataWidth))
                 |  val r_chosen   = Reg(UInt(log2Ceil(numIPs).W))
                 |
                 |  r_foundReq := r_ipReq_enable.reduce(_ || _)
                 |  for (i <- 0 until numIPs) {
                 |    when(r_ipReq_enable(i)) {
                 |      r_reqBits := r_ipReq_bits(i)
                 |      r_chosen  := i.U
                 |    }
                 |  }
                 |
                 |  io.ip.req.valid := r_foundReq
                 |  io.ip.req.bits  := r_reqBits
                 |
                 |  // ------------------ Stage 2: memory.resp handling ------------------
                 |  val r_mem_resp_valid = RegNext(io.ip.resp.valid)
                 |  val r_mem_resp_bits  = RegNext(io.ip.resp.bits)
                 |  val r_mem_resp_id    = RegNext(r_chosen)
                 |
                 |  val r_ipResp_valid = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
                 |  val r_ipResp_bits  = Reg(Vec(numIPs, new ${mod.moduleName}ResponseBundle(dataWidth)))
                 |
                 |  for (i <- 0 until numIPs) {
                 |    r_ipResp_valid(i)    := false.B
                 |    r_ipResp_bits(i).out := 0.U
                 |  }
                 |
                 |  when(r_mem_resp_valid) {
                 |    r_ipResp_valid(r_mem_resp_id) := true.B
                 |    r_ipResp_bits(r_mem_resp_id)  := r_mem_resp_bits
                 |  } .otherwise {
                 |    r_ipResp_valid(r_mem_resp_id) := false.B
                 |  }
                 |
                 |  for (i <- 0 until numIPs) {
                 |    io.ipResps(i).valid := r_ipResp_valid(i)
                 |    io.ipResps(i).bits  := r_ipResp_bits(i)
                 |  }
                 |}
               """
    }

    return st"""
               |${requestBundleST}
               |${responseBundleST}
               |${IpIOST}
               |${IpArbiterIOST}
               |${arbiterModuleST}
             """
  }

  @pure def insDeclST(ip: IpType, numInstances: Z): ST = {
    val targetModule: ChiselModule = findChiselModule(ip).get
    val moduleInstances: ST = {
      val modDeclIns: ISZ[ST] = if(targetModule.expression == BlockMemoryIP()) {
        for (i <- 0 until numInstances) yield
          if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative)
            st"""val ${targetModule.instanceName} = Module(new ${targetModule.moduleName}(${targetModule.asInstanceOf[BlockMemory].depth}, ${targetModule.width}))"""
          else if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4 || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr)
            st"""val ${targetModule.instanceName} = Module(new ${targetModule.moduleName}(C_M_AXI_DATA_WIDTH = C_M_AXI_DATA_WIDTH, C_M_AXI_ADDR_WIDTH = C_M_AXI_ADDR_WIDTH, C_M_TARGET_SLAVE_BASE_ADDR = C_M_TARGET_SLAVE_BASE_ADDR, MEMORY_DEPTH = MEMORY_DEPTH))"""
          else
            st""
      } else if(targetModule.expression == LabelToFsmIP()) {
        if(anvil.config.cpMax > 0) {
          for (i <- 0 until numInstances) yield
            st"""val ${targetModule.instanceName} = Module(new ${targetModule.moduleName}(${hwLog.maxNumLabel}, ${anvil.config.cpMax}))"""
        } else {
          ISZ[ST]()
        }
      } else {
        for (i <- 0 until numInstances) yield
          st"""val ${targetModule.instanceName}_${i} = Module(new ${targetModule.moduleName}(${targetModule.width}))"""
      }

      st"""
          |${(modDeclIns, "\n")}
        """
    }
    return moduleInstances
  }

  @pure def insPortCallST(ip: IpType, numInstances: Z): ST = {
    val targetModule: ChiselModule = findChiselModule(ip).get
    var portCallST: ISZ[ST] = ISZ()
    for(i <- 0 until numInstances) {
      portCallST = portCallST :+ st"init${targetModule.instanceName}_${i}()"
    }
    return st"""
        |${(portCallST, "\n")}
      """
  }

  @pure def insPortFuncST(ip: IpType, numInstances: Z): ST = {
    val targetModule: ChiselModule = findChiselModule(ip).get
    @pure def inputPortListSTWithoutMux(modIdx: Z): ST = {
      @strictpure def defaultValue(portValueType: String): String = {
        portValueType match {
          case "UInt" => "0.U"
          case "SInt" => "0.S"
          case "Bool" => "false.B"
          case _ => halt(s"${portValueType} is not support in input type")
        }
      }
      var muxLogicST: ISZ[ST] = ISZ[ST]()

      for(entry <- targetModule.portList.entries) {
        if(ip == BlockMemoryIP()) {
          muxLogicST = muxLogicST :+ st"o.${targetModule.instanceName}.io.${entry._1} := ${defaultValue(entry._2)}"
        } else if(ip == LabelToFsmIP()) {
          muxLogicST = muxLogicST :+ st"o.${targetModule.instanceName}.io.${entry._1} := ${defaultValue(entry._2)}"
        } else {
          muxLogicST = muxLogicST :+ st"o.${targetModule.instanceName}_${modIdx}.io.${entry._1} := ${defaultValue(entry._2)}"
        }
      }

      return st"""
                 |def init${targetModule.instanceName}_${modIdx}(): Unit = {
                 |  ${(muxLogicST, "\n")}
                 |}
        """
    }

    val instancePort: ST = {
      val modPortInsWithoutMux: ISZ[ST] = {
        for(i <- 0 until numInstances) yield
          st"""${(inputPortListSTWithoutMux(i), "\n")}"""
      }

      st"""
            |${(modPortInsWithoutMux, "\n")}
        """
    }

    return st"""
               |${(instancePort, "\n")}
               """
  }

  @pure def insertIPInput(ip: IpType, newHashSMap: HashSMap[Z, HashSMap[String, ChiselModule.Input]], inputMap: InputMap): Unit = {
    var h: HashSMap[Z, HashSMap[String, ChiselModule.Input]] = inputMap.ipMap.get(ip).get
    for(entry <- newHashSMap.entries) {
      h = h + entry._1 ~> entry._2
    }

    inputMap.ipMap = inputMap.ipMap - (ip, inputMap.ipMap.get(ip).get)
    inputMap.ipMap = inputMap.ipMap + (ip, h)
  }

  @pure def getIpInstanceName(ip: IpType): Option[String] = {
    for(i <- 0 until ipModules.size) {
      if(ipModules(i).expression == ip) {
        return Some(ipModules(i).instanceName)
      }
    }
    return None()
  }

  @pure def populateInputs(label: Z, hashSMap: HashSMap[String, (ST, String)], instanceIndex: Z) : HashSMap[Z, HashSMap[String, ChiselModule.Input]] = {
    var inputList: HashSMap[String, ChiselModule.Input] = HashSMap.empty
    var finalList: HashSMap[Z, HashSMap[String, ChiselModule.Input]] = HashSMap.empty
    for(entry <- hashSMap.entries) {
      val stateValue: ChiselModule.StateValue = ChiselModule.StateValue(label, entry._2._1.render)
      inputList = inputList + entry._1 ~> ChiselModule.Input(stateValue, entry._2._2)
    }
    finalList = finalList + instanceIndex ~> inputList
    return finalList
  }


  /*
    Notes/links:
    * Slang IR: https://github.com/sireum/slang/blob/master/ast/shared/src/main/scala/org/sireum/lang/ast/IR.scala
    * Anvil IR Intrinsic: https://github.com/sireum/anvil/blob/master/shared/src/main/scala/org/sireum/anvil/Intrinsic.scala
   */
  def printProcedure(name: String, program: AST.IR.Program, output: Anvil.Output, maxRegisters: Util.TempVector, globalInfoMap: HashSMap[QName, VarInfo]): Unit = {
    val o = program.procedures(0)
    if(anvil.config.useIP) {
      ipAlloc = Util.ipAlloc(anvil, o, anvil.config.ipMax)
    }
    var r = HashSMap.empty[ISZ[String], ST]
    val processedProcedureST = processProcedure(name, o, maxRegisters, globalInfoMap)
    r = r + ISZ(name) ~> o.prettyST(anvil.printer)

    @strictpure def cyclesXilinxAdder(width: Z): Z = {
      width match {
        case w if w <= 12 => 1
        case w if w <= 24 => 2
        case w if w <= 36 => 3
        case w if w <= 48 => 4
        case w if w <= 60 => 5
        case w if w <= 64 => 6
        case _ => halt("not support this width")
      }
    }

    @strictpure def cyclesXilinxMultiplier(width: Z): Z = {
      width match {
        case w if w <= 2 => 1
        case w if w <= 4 => 2
        case w if w <= 8 => 3
        case w if w <= 16 => 4
        case w if w <= 32 => 5
        case w if w <= 64 => 6
        case _ => halt("not support this width")
      }
    }

    @pure def arbiterModuleST: HashSMap[String, ISZ[ST]] = {
      var arbiterModuleMap: HashSMap[String, ISZ[ST]] = HashSMap.empty
      val importPaddingST: ST =
        st"""
            |import chisel3._
            |import chisel3.util._
            |import chisel3.experimental._
            |
          """

      val xilinxAdderUnsigned64WrapperST: ST =
        st"""
            |class XilinxAdderUnsigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ce = Input(Bool())
            |    val A = Input(UInt(64.W))
            |    val B = Input(UInt(64.W))
            |    val valid = Output(Bool())
            |    val S = Output(UInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxAdderUnsigned64Wrapper.v")
            |}
          """

      val xilinxAdderSigned64WrapperST: ST =
        st"""
            |class XilinxAdderSigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ce = Input(Bool())
            |    val A = Input(SInt(64.W))
            |    val B = Input(SInt(64.W))
            |    val valid = Output(Bool())
            |    val S = Output(SInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxAdderSigned64Wrapper.v")
            |}
          """

      val xilinxSubtractorUnsigned64WrapperST: ST =
        st"""
            |class XilinxSubtractorUnsigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ce = Input(Bool())
            |    val A = Input(UInt(64.W))
            |    val B = Input(UInt(64.W))
            |    val valid = Output(Bool())
            |    val S = Output(UInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxSubtractorUnsigned64Wrapper.v")
            |}
          """

      val xilinxSubtractorSigned64WrapperST: ST =
        st"""
            |class XilinxSubtractorSigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ce = Input(Bool())
            |    val A = Input(SInt(64.W))
            |    val B = Input(SInt(64.W))
            |    val valid = Output(Bool())
            |    val S = Output(SInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxSubtractorSigned64Wrapper.v")
            |}
          """

      val xilinxMultiplierUnsigned64WrapperST: ST =
        st"""
            |class XilinxMultiplierUnsigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ce = Input(Bool())
            |    val a = Input(UInt(64.W))
            |    val b = Input(UInt(64.W))
            |    val valid = Output(Bool())
            |    val p = Output(UInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxMultiplierUnsigned64Wrapper.v")
            |}
          """

      val xilinxMultiplierSigned64WrapperST: ST =
        st"""
            |class XilinxMultiplierSigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ce = Input(Bool())
            |    val a = Input(SInt(64.W))
            |    val b = Input(SInt(64.W))
            |    val valid = Output(Bool())
            |    val p = Output(SInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxMultiplierSigned64Wrapper.v")
            |}
          """

      val xilinxDividerUnsigned64WrapperST: ST =
        st"""
            |class XilinxDividerUnsigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clock = Input(Bool())
            |    val resetn = Input(Bool())
            |    val a = Input(UInt(64.W))
            |    val b = Input(UInt(64.W))
            |    val start = Input(Bool())
            |    val valid = Output(Bool())
            |    val quotient = Output(UInt(64.W))
            |    val remainder = Output(UInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxDividerUnsigned64Wrapper.v")
            |}
          """

      val xilinxDividerSigned64WrapperST: ST =
        st"""
            |class XilinxDividerSigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clock = Input(Bool())
            |    val resetn = Input(Bool())
            |    val a = Input(SInt(64.W))
            |    val b = Input(SInt(64.W))
            |    val start = Input(Bool())
            |    val valid = Output(Bool())
            |    val quotient = Output(SInt(64.W))
            |    val remainder = Output(SInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxDividerSigned64Wrapper.v")
            |}
          """

      val xilinxBramWrapperST =
        st"""
            |class XilinxBRAMWrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ena = Input(Bool())
            |    val wea = Input(Bool())
            |    val addra = Input(UInt(10.W))
            |    val dina = Input(UInt(64.W))
            |    val douta = Output(UInt(64.W))
            |    val enb = Input(Bool())
            |    val web = Input(Bool())
            |    val addrb = Input(UInt(10.W))
            |    val dinb = Input(UInt(64.W))
            |    val doutb = Output(UInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxBRAMWrapper.v")
            |}
          """

      val xilinxIndexAdderWrapperST =
        st"""
            |class XilinxIndexAdderWrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk   = Input(Bool())
            |    val ce    = Input(Bool())
            |    val A     = Input(UInt(16.W))
            |    val B     = Input(UInt(16.W))
            |    val valid = Output(Bool())
            |    val S     = Output(UInt(16.W))
            |  })
            |
            |  addResource("/verilog/XilinxIndexAdderWrapper.v")
            |}
          """

      val xilinxIndexMultiplierWrapperST =
        st"""
            |class XilinxIndexMultiplierWrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk   = Input(Bool())
            |    val ce    = Input(Bool())
            |    val A     = Input(UInt(16.W))
            |    val B     = Input(UInt(16.W))
            |    val valid = Output(Bool())
            |    val P     = Output(UInt(16.W))
            |  })
            |
            |  addResource("/verilog/XilinxIndexMultiplierWrapper.v")
            |}
          """

      val xilinxBufgWrapperST =
        st"""
            |class XilinxBUFGWrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val I    = Input(Clock())
            |    val O    = Output(Clock())
            |  })
            |
            |  addResource("/verilog/XilinxBUFGWrapper.v")
            |}
          """

      for(i <- 0 until ipModules.size) {
        ipModules(i) match {
          case Adder(signed, _, _, _, _, xilinxIpValid) =>
            if(xilinxIpValid) {
              val t: ST = if(signed) xilinxAdderSigned64WrapperST else xilinxAdderUnsigned64WrapperST
              arbiterModuleMap = arbiterModuleMap + ipModules(i).moduleName ~> (ISZ[ST]() :+ importPaddingST :+ t :+ ipModules(i).moduleST)
            }
          case Subtractor(signed, _, _, _, _, xilinxIpValid) => {
            if(xilinxIpValid) {
              val t: ST = if(signed) xilinxSubtractorSigned64WrapperST else xilinxSubtractorUnsigned64WrapperST
              arbiterModuleMap = arbiterModuleMap + ipModules(i).moduleName ~> (ISZ[ST]() :+ importPaddingST :+ t :+ ipModules(i).moduleST)
            }
          }
          case Multiplier(signed, _, _, _, _, xilinxIpValid) =>
            if(xilinxIpValid) {
              val t: ST = if(signed) xilinxMultiplierSigned64WrapperST else xilinxMultiplierUnsigned64WrapperST
              arbiterModuleMap = arbiterModuleMap + ipModules(i).moduleName ~> (ISZ[ST]() :+ importPaddingST :+ t :+ ipModules(i).moduleST)
            }
          case Division(signed, _, _, _, _, xilinxIpValid) =>
            if(xilinxIpValid) {
              val t: ST = if(signed) xilinxDividerSigned64WrapperST else xilinxDividerUnsigned64WrapperST
              arbiterModuleMap = arbiterModuleMap + ipModules(i).moduleName ~> (ISZ[ST]() :+ importPaddingST :+ t :+ ipModules(i).moduleST)
            }
          case Indexer(signed, _, _, _, _, xilinxIpValid) =>
            if(xilinxIpValid) {
              arbiterModuleMap = arbiterModuleMap + ipModules(i).moduleName ~>
                (ISZ[ST]() :+ importPaddingST :+ xilinxIndexAdderWrapperST :+ xilinxIndexMultiplierWrapperST :+ ipModules(i).moduleST)
            }
          case BlockMemory(_, _, _, _, _, _, _, _, _, _) =>
            val bramST: ST = if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) xilinxBramWrapperST else st""
            arbiterModuleMap = arbiterModuleMap + ipModules(i).moduleName ~> (ISZ[ST]() :+ importPaddingST :+ bramST :+ ipModules(i).moduleST)
          case _ =>
            arbiterModuleMap = arbiterModuleMap + ipModules(i).moduleName ~> (ISZ[ST]() :+ importPaddingST :+ ipModules(i).moduleST)
        }
      }

      return arbiterModuleMap
    }

    @strictpure def routerST: ST = {
      st"""
          |import chisel3._
          |import chisel3.util._
          |import chisel3.experimental._
          |
          |class Packet(val idWidth: Int, val cpWidth: Int) extends Bundle {
          |  val srcID = UInt(idWidth.W)
          |  val dstID = UInt(idWidth.W)
          |  val srcCP = UInt(cpWidth.W)
          |  val dstCP = UInt(cpWidth.W)
          |}
          |
          |class RouterIO(val nPorts: Int, val idWidth: Int, val cpWidth: Int) extends Bundle {
          |  val in  = Flipped(Vec(nPorts, Valid(new Packet(idWidth, cpWidth))))
          |  val out = Vec(nPorts, Valid(new Packet(idWidth, cpWidth)))
          |}
          |
          |class Router(val nPorts: Int, val idWidth: Int, val cpWidth: Int) extends Module {
          |  val io = IO(new RouterIO(nPorts, idWidth, cpWidth))
          |
          |  // input buffer
          |  val r_inputBuffer       = VecInit(Seq.fill(nPorts)(Reg(new Packet(idWidth, cpWidth))))
          |  val r_inputBuffer_valid = VecInit(Seq.fill(nPorts)(Reg(Bool())))
          |  for (i <- 0 until nPorts) {
          |    r_inputBuffer(i)       := io.in(i).bits
          |    r_inputBuffer_valid(i) := io.in(i).valid
          |  }
          |
          |  // output buffer
          |  val r_outputBuffer       = VecInit(Seq.fill(nPorts)(Reg(new Packet(idWidth, cpWidth))))
          |  val r_outputBuffer_valid = VecInit(Seq.fill(nPorts)(Reg(Bool())))
          |  for (i <- 0 until nPorts) {
          |    io.out(i).bits  := r_outputBuffer(i)
          |    io.out(i).valid := r_outputBuffer_valid(i)
          |  }
          |
          |  // default: no write
          |  for (i <- 0 until nPorts) {
          |    r_outputBuffer(i).srcID := 0.U
          |    r_outputBuffer(i).dstID := 0.U
          |    r_outputBuffer(i).srcCP := 0.U
          |    r_outputBuffer(i).dstCP := 0.U
          |
          |    r_outputBuffer_valid(i) := false.B
          |  }
          |
          |  // arbiter
          |  for (i <- 0 until nPorts) {
          |    when(r_inputBuffer_valid(i)) {
          |      r_outputBuffer_valid(r_inputBuffer(i).dstID) := true.B
          |      r_outputBuffer(r_inputBuffer(i).dstID)       := r_inputBuffer(i)
          |    }
          |  }
          |}
        """
    }

    @strictpure def stackST: ST = {
      st"""
          |import chisel3._
          |import chisel3.util._
          |import chisel3.experimental._
          |
          |class Stack[T <: Data](val gen: T, val width: Int, val depth: Int) extends Module {
          |  val io = IO(new Bundle {
          |    val push         = Input(Bool())
          |    val pop          = Input(Bool())
          |    val en           = Input(Bool())
          |    val dataIn       = Input(gen.cloneType)
          |    val dataOut      = Output(gen.cloneType)
          |    val valid        = Output(Bool())
          |  })
          |
          |  val stack_mem = Mem(depth, gen)
          |  val sp        = RegInit(0.U(log2Ceil(depth+1).W))
          |  val out       = RegInit(0.U.asTypeOf(gen))
          |  val popValid  = Reg(Bool())
          |  val pushValid = Reg(Bool())
          |
          |  popValid  := false.B
          |  pushValid := false.B
          |
          |  when (io.en) {
          |    when(io.push && (sp < depth.U)) {
          |      stack_mem(sp) := io.dataIn
          |      sp            := sp + 1.U
          |      pushValid     := true.B
          |    }
          |    when (io.pop && sp > 0.U) {
          |      out      := stack_mem(sp - 1.U)
          |      sp       := sp - 1.U
          |      popValid := true.B
          |    }
          |  }
          |
          |  io.dataOut := out
          |  io.valid   := pushValid | popValid
          |}
        """
    }

    val configST: ST =
      st"""
          |runtimeCheck = ${if(anvil.config.runtimeCheck) "true" else "false"},
          |printSize = ${anvil.config.printSize},
          |memory = ${anvil.config.memory},
          |erase = ${if(anvil.config.erase) "true" else "false"},
          |noXilinxIp = ${if(anvil.config.noXilinxIp) "true" else "false"},
          |splitTempSizes = ${if(anvil.config.splitTempSizes) "true" else  "false"},
          |tempLocal = ${if(anvil.config.tempLocal) "true" else "false"},
          |memoryAccess = ${anvil.config.memoryAccess.string},
          |useIp = ${if(anvil.config.useIP) "true" else "false"},
          |ipMax = ${anvil.config.ipMax},
          |cpMax = ${anvil.config.cpMax},
          |CPsize = ${anvil.typeBitSize(spType)},
          |SPsize = ${anvil.typeBitSize(anvil.cpType)},
          |tempGlobal = ${anvil.config.tempGlobal},
          |alignAxi4 = ${anvil.config.alignAxi4}
        """

    val backslash = "\\"

    val bramNativeGenerationST: ST =
      st"""
          |# need to be customzied for different benchmarks
          |create_ip -name blk_mem_gen -vendor xilinx.com -library ip -version 8.4 -module_name XilinxBRAM
          |set_property -dict [list $backslash
          |  CONFIG.Memory_Type {True_Dual_Port_RAM} $backslash
          |  CONFIG.Operating_Mode_A {NO_CHANGE} $backslash
          |  CONFIG.Operating_Mode_B {NO_CHANGE} $backslash
          |  CONFIG.Register_PortA_Output_of_Memory_Primitives {false} $backslash
          |  CONFIG.Register_PortB_Output_of_Memory_Primitives {false} $backslash
          |  CONFIG.Write_Depth_A {${anvil.config.memory}} $backslash
          |  CONFIG.Write_Width_A {8} $backslash
          |] [get_ips XilinxBRAM]
          """
    val ipGenerationTclST: ST =
      st"""
          |set PROJECT_PATH [lindex $$argv 0]
          |set PROJECT_NAME [lindex $$argv 1]
          |set FREQ_HZ [lindex $$argv 2]
          |set FILE_PATH $${PROJECT_PATH}/chisel/generated_verilog
          |
          |# /home/kejun/development/HLS_slang/zcu102/InsertSortIP
          |create_project $$PROJECT_NAME $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME -part xczu9eg-ffvb1156-2-e
          |
          |set_property board_part xilinx.com:zcu102:part0:3.4 [current_project]
          |
          |set_property target_language Verilog [current_project]
          |
          |# /home/kejun/Desktop/ip.v
          |add_files -norecurse [glob $$FILE_PATH/*.v]
          |update_compile_order -fileset sources_1
          |
          |# add xilinx IPs
          |create_ip -name div_gen -vendor xilinx.com -library ip -version 5.1 -module_name XilinxDividerSigned64
          |set_property -dict [list $backslash
          |  CONFIG.ARESETN {true} $backslash
          |  CONFIG.FlowControl {Blocking} $backslash
          |  CONFIG.dividend_and_quotient_width {64} $backslash
          |  CONFIG.divisor_width {64} $backslash
          |  CONFIG.fractional_width {64} $backslash
          |  CONFIG.latency {69} $backslash
          |] [get_ips XilinxDividerSigned64]
          |
          |create_ip -name div_gen -vendor xilinx.com -library ip -version 5.1 -module_name XilinxDividerUnsigned64
          |set_property -dict [list $backslash
          |  CONFIG.ARESETN {true} $backslash
          |  CONFIG.FlowControl {Blocking} $backslash
          |  CONFIG.dividend_and_quotient_width {64} $backslash
          |  CONFIG.divisor_width {64} $backslash
          |  CONFIG.fractional_width {64} $backslash
          |  CONFIG.latency {67} $backslash
          |  CONFIG.operand_sign {Unsigned} $backslash
          |] [get_ips XilinxDividerUnsigned64]
          |
          |create_ip -name mult_gen -vendor xilinx.com -library ip -version 12.0 -module_name XilinxMultiplierUnsigned64
          |set_property -dict [list $backslash
          |  CONFIG.ClockEnable {true} $backslash
          |  CONFIG.Multiplier_Construction {Use_Mults} $backslash
          |  CONFIG.OutputWidthHigh {63} $backslash
          |  CONFIG.PipeStages {18} $backslash
          |  CONFIG.PortAType {Unsigned} $backslash
          |  CONFIG.PortAWidth {64} $backslash
          |  CONFIG.PortBType {Unsigned} $backslash
          |  CONFIG.PortBWidth {64} $backslash
          |  CONFIG.Use_Custom_Output_Width {true} $backslash
          |] [get_ips XilinxMultiplierUnsigned64]
          |
          |create_ip -name mult_gen -vendor xilinx.com -library ip -version 12.0 -module_name XilinxMultiplierSigned64
          |set_property -dict [list $backslash
          |  CONFIG.ClockEnable {true} $backslash
          |  CONFIG.Multiplier_Construction {Use_Mults} $backslash
          |  CONFIG.OutputWidthHigh {63} $backslash
          |  CONFIG.PipeStages {18} $backslash
          |  CONFIG.PortAWidth {64} $backslash
          |  CONFIG.PortBWidth {64} $backslash
          |  CONFIG.Use_Custom_Output_Width {true} $backslash
          |] [get_ips XilinxMultiplierSigned64]
          |
          |create_ip -name c_addsub -vendor xilinx.com -library ip -version 12.0 -module_name XilinxAdderSigned64
          |set_property -dict [list $backslash
          |  CONFIG.A_Width {64} $backslash
          |  CONFIG.B_Value {0000000000000000000000000000000000000000000000000000000000000000} $backslash
          |  CONFIG.B_Width {64} $backslash
          |  CONFIG.Latency {6} $backslash
          |  CONFIG.Latency_Configuration {Automatic} $backslash
          |  CONFIG.Out_Width {64} $backslash
          |] [get_ips XilinxAdderSigned64]
          |
          |create_ip -name c_addsub -vendor xilinx.com -library ip -version 12.0 -module_name XilinxAdderUnsigned64
          |set_property -dict [list $backslash
          |  CONFIG.A_Type {Unsigned} $backslash
          |  CONFIG.A_Width {64} $backslash
          |  CONFIG.B_Type {Unsigned} $backslash
          |  CONFIG.B_Value {0000000000000000000000000000000000000000000000000000000000000000} $backslash
          |  CONFIG.B_Width {64} $backslash
          |  CONFIG.Latency {6} $backslash
          |  CONFIG.Latency_Configuration {Automatic} $backslash
          |  CONFIG.Out_Width {64} $backslash
          |] [get_ips XilinxAdderUnsigned64]
          |
          |create_ip -name c_addsub -vendor xilinx.com -library ip -version 12.0 -module_name XilinxSubtractorSigned64
          |set_property -dict [list $backslash
          |  CONFIG.A_Width {64} $backslash
          |  CONFIG.Add_Mode {Subtract} $backslash
          |  CONFIG.B_Value {0000000000000000000000000000000000000000000000000000000000000000} $backslash
          |  CONFIG.B_Width {64} $backslash
          |  CONFIG.Latency {6} $backslash
          |  CONFIG.Latency_Configuration {Automatic} $backslash
          |  CONFIG.Out_Width {64} $backslash
          |] [get_ips XilinxSubtractorSigned64]
          |
          |create_ip -name c_addsub -vendor xilinx.com -library ip -version 12.0 -module_name XilinxSubtractorUnsigned64
          |set_property -dict [list $backslash
          |  CONFIG.A_Type {Unsigned} $backslash
          |  CONFIG.A_Width {64} $backslash
          |  CONFIG.Add_Mode {Subtract} $backslash
          |  CONFIG.B_Type {Unsigned} $backslash
          |  CONFIG.B_Value {0000000000000000000000000000000000000000000000000000000000000000} $backslash
          |  CONFIG.B_Width {64} $backslash
          |  CONFIG.Latency {6} $backslash
          |  CONFIG.Latency_Configuration {Automatic} $backslash
          |  CONFIG.Out_Width {64} $backslash
          |] [get_ips XilinxSubtractorUnsigned64]
          |
          |${if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) bramNativeGenerationST else st""}
          |
          |# need to be customzied for different benchmarks
          |create_ip -name mult_gen -vendor xilinx.com -library ip -version 12.0 -module_name XilinxIndexMultiplier
          |set_property -dict [list $backslash
          |  CONFIG.ClockEnable {true} $backslash
          |  CONFIG.OutputWidthHigh {${anvil.typeBitSize(spType) - 1}} $backslash
          |  CONFIG.PipeStages {${cyclesXilinxMultiplier(anvil.typeBitSize(spType))}} $backslash
          |  CONFIG.PortAType {Unsigned} $backslash
          |  CONFIG.PortAWidth {${anvil.typeBitSize(spType)}} $backslash
          |  CONFIG.PortBType {Unsigned} $backslash
          |  CONFIG.PortBWidth {${anvil.typeBitSize(spType)}} $backslash
          |  CONFIG.Use_Custom_Output_Width {true} $backslash
          |] [get_ips XilinxIndexMultiplier]
          |
          |# need to be customzied for different benchmarks
          |create_ip -name c_addsub -vendor xilinx.com -library ip -version 12.0 -module_name XilinxIndexAdder
          |set_property -dict [list $backslash
          |  CONFIG.A_Type {Unsigned} $backslash
          |  CONFIG.A_Width {${anvil.typeBitSize(spType)}} $backslash
          |  CONFIG.B_Type {Unsigned} $backslash
          |  CONFIG.B_Value {00000000} $backslash
          |  CONFIG.B_Width {${anvil.typeBitSize(spType)}} $backslash
          |  CONFIG.Latency {${cyclesXilinxAdder(anvil.typeBitSize(spType))}} $backslash
          |  CONFIG.Latency_Configuration {Automatic} $backslash
          |  CONFIG.Out_Width {${anvil.typeBitSize(spType)}} $backslash
          |] [get_ips XilinxIndexAdder]
          |
          |# /home/kejun/development/HLS_slang/zcu102/InsertSortIP/IP_dir
          |ipx::package_project -root_dir $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME//IP_dir -vendor user.org -library user -taxonomy /UserIP -import_files -set_current false
          |ipx::unload_core $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME//IP_dir/component.xml
          |ipx::edit_ip_in_project -upgrade true -name tmp_edit_project -directory $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/IP_dir $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/IP_dir/component.xml
          |
          |update_compile_order -fileset sources_1
          |set_property core_revision 2 [ipx::current_core]
          |ipx::update_source_project_archive -component [ipx::current_core]
          |ipx::create_xgui_files [ipx::current_core]
          |ipx::update_checksums [ipx::current_core]
          |ipx::save_core [ipx::current_core]
          |ipx::move_temp_component_back -component [ipx::current_core]
          |close_project -delete
          |set_property  ip_repo_paths  $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/IP_dir [current_project]
          |update_ip_catalog
          """

    val gpOrHpST: ST = {
      if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative)
        st"""
            |set_property CONFIG.PSU__USE__M_AXI_GP1 {0} [get_bd_cells zynq_ultra_ps_e_0]
            |set_property CONFIG.PSU__MAXIGP0__DATA_WIDTH {32} [get_bd_cells zynq_ultra_ps_e_0]
              """
      else if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4)
        st"""
            |set_property -dict [list $backslash
            |  CONFIG.PSU__MAXIGP0__DATA_WIDTH {64} $backslash
            |  CONFIG.PSU__USE__M_AXI_GP1 {0} $backslash
            |] [get_bd_cells zynq_ultra_ps_e_0]
            """
      else if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr)
        st"""
            |set_property -dict [list $backslash
            |  CONFIG.PSU__USE__M_AXI_GP1 {0} $backslash
            |  CONFIG.PSU__USE__S_AXI_GP2 {1} $backslash
            |] [get_bd_cells zynq_ultra_ps_e_0]
            |set_property CONFIG.PSU__SAXIGP2__DATA_WIDTH {64} [get_bd_cells zynq_ultra_ps_e_0]
            |set_property CONFIG.PSU__MAXIGP0__DATA_WIDTH {64} [get_bd_cells zynq_ultra_ps_e_0]
            """
      else
        st""
    }

    val blockDesignST: ST = {
      if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative)
        st"""
            |# reverse reset
            |create_bd_cell -type ip -vlnv xilinx.com:ip:util_vector_logic:2.0 util_vector_logic_0
            |set_property CONFIG.C_OPERATION {not} [get_bd_cells util_vector_logic_0]
            |set_property CONFIG.C_SIZE {1} [get_bd_cells util_vector_logic_0]
            |connect_bd_net [get_bd_pins util_vector_logic_0/Res] [get_bd_pins GeneratedIP/reset]
            |
            |apply_bd_automation -rule xilinx.com:bd_rule:axi4 -config { Clk_master {Auto} Clk_slave {Auto} Clk_xbar {Auto} Master {/zynq_ultra_ps_e_0/M_AXI_HPM0_FPD} Slave {/GeneratedIP/io_S_AXI} ddr_seg {Auto} intc_ip {New AXI SmartConnect} master_apm {0}}  [get_bd_intf_pins GeneratedIP/io_S_AXI]
            |connect_bd_net [get_bd_pins rst_ps8_0_99M/peripheral_aresetn] [get_bd_pins util_vector_logic_0/Op1]
            |set_property -dict [list CONFIG.PSU__CRL_APB__PL0_REF_CTRL__FREQMHZ $$FREQ_HZ $backslash
            | CONFIG.PSU__CRL_APB__PL0_REF_CTRL__SRCSEL {RPLL} $backslash
            |] [get_bd_cells zynq_ultra_ps_e_0]
            """
      else if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4)
        st"""
            |# inverse reset_n
            |create_bd_cell -type ip -vlnv xilinx.com:ip:util_vector_logic:2.0 util_vector_logic_0
            |set_property -dict [list $backslash
            |  CONFIG.C_OPERATION {not} $backslash
            |  CONFIG.C_SIZE {1} $backslash
            |] [get_bd_cells util_vector_logic_0]
            |connect_bd_net [get_bd_pins util_vector_logic_0/Res] [get_bd_pins GeneratedIP/reset]
            |
            |# connect PS to slave of generated IP
            |apply_bd_automation -rule xilinx.com:bd_rule:axi4 -config { Clk_master {Auto} Clk_slave {Auto} Clk_xbar {Auto} Master {/zynq_ultra_ps_e_0/M_AXI_HPM0_FPD} Slave {/GeneratedIP/io_S_AXI} ddr_seg {Auto} intc_ip {New AXI SmartConnect} master_apm {0}}  [get_bd_intf_pins GeneratedIP/io_S_AXI]
            |
            |# create AXI4 based BRAM
            |create_bd_cell -type ip -vlnv xilinx.com:ip:blk_mem_gen:8.4 blk_mem_gen_0
            |set_property -dict [list $backslash
            |  CONFIG.Memory_Type {True_Dual_Port_RAM} $backslash
            |  CONFIG.Register_PortA_Output_of_Memory_Primitives {false} $backslash
            |  CONFIG.Register_PortB_Output_of_Memory_Primitives {false} $backslash
            |  CONFIG.Write_Depth_A ${anvil.config.memory / 8 + 1} $backslash
            |  CONFIG.Write_Width_A {64} $backslash
            |  CONFIG.use_bram_block {BRAM_Controller} $backslash
            |] [get_bd_cells blk_mem_gen_0]
            |
            |# create axi bram controller
            |create_bd_cell -type ip -vlnv xilinx.com:ip:axi_bram_ctrl:4.1 axi_bram_ctrl_0
            |set_property -dict [list $backslash
            |  CONFIG.DATA_WIDTH {64} $backslash
            |  CONFIG.SINGLE_PORT_BRAM {1} $backslash
            |] [get_bd_cells axi_bram_ctrl_0]
            |connect_bd_intf_net [get_bd_intf_pins axi_bram_ctrl_0/BRAM_PORTA] [get_bd_intf_pins blk_mem_gen_0/BRAM_PORTA]
            |create_bd_cell -type ip -vlnv xilinx.com:ip:axi_bram_ctrl:4.1 axi_bram_ctrl_1
            |set_property -dict [list $backslash
            |  CONFIG.DATA_WIDTH {64} $backslash
            |  CONFIG.SINGLE_PORT_BRAM {1} $backslash
            |] [get_bd_cells axi_bram_ctrl_1]
            |connect_bd_intf_net [get_bd_intf_pins axi_bram_ctrl_1/BRAM_PORTA] [get_bd_intf_pins blk_mem_gen_0/BRAM_PORTB]
            |
            |# connect to two axi bram controller
            |set_property CONFIG.NUM_MI {2} [get_bd_cells axi_smc]
            |connect_bd_intf_net [get_bd_intf_pins axi_smc/M01_AXI] [get_bd_intf_pins axi_bram_ctrl_1/S_AXI]
            |connect_bd_intf_net [get_bd_intf_pins GeneratedIP/io_M_AXI] [get_bd_intf_pins axi_bram_ctrl_0/S_AXI]
            |
            |# connect to axi clock
            |apply_bd_automation -rule xilinx.com:bd_rule:clkrst -config { Clk {/zynq_ultra_ps_e_0/pl_clk0} Ref_Clk0 {} Ref_Clk1 {} Ref_Clk2 {}}  [get_bd_pins axi_bram_ctrl_0/s_axi_aclk]
            |apply_bd_automation -rule xilinx.com:bd_rule:clkrst -config { Clk {/zynq_ultra_ps_e_0/pl_clk0} Ref_Clk0 {} Ref_Clk1 {} Ref_Clk2 {}}  [get_bd_pins axi_bram_ctrl_1/s_axi_aclk]
            |
            |# connect to utility vector
            |connect_bd_net [get_bd_pins rst_ps8_0_99M/peripheral_aresetn] [get_bd_pins util_vector_logic_0/Op1]
            |
            |# set the clock freq
            |set_property -dict [list CONFIG.PSU__CRL_APB__PL0_REF_CTRL__FREQMHZ $$FREQ_HZ $backslash
            | CONFIG.PSU__CRL_APB__PL0_REF_CTRL__SRCSEL {RPLL} $backslash
            |] [get_bd_cells zynq_ultra_ps_e_0]
            |
            |# assign memory address for PS access
            |assign_bd_address -target_address_space /zynq_ultra_ps_e_0/Data [get_bd_addr_segs axi_bram_ctrl_1/S_AXI/Mem0] -force
            """
      else if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr)
        st"""
            |# connect to HP port
            |connect_bd_intf_net [get_bd_intf_pins zynq_ultra_ps_e_0/S_AXI_HP0_FPD] [get_bd_intf_pins GeneratedIP/io_M_AXI]
            |
            |# inverse reset_n
            |create_bd_cell -type ip -vlnv xilinx.com:ip:util_vector_logic:2.0 util_vector_logic_0
            |set_property -dict [list $backslash
            |  CONFIG.C_OPERATION {not} $backslash
            |  CONFIG.C_SIZE {1} $backslash
            |] [get_bd_cells util_vector_logic_0]
            |connect_bd_net [get_bd_pins util_vector_logic_0/Res] [get_bd_pins GeneratedIP/reset]
            |
            |apply_bd_automation -rule xilinx.com:bd_rule:axi4 -config { Clk_master {Auto} Clk_slave {Auto} Clk_xbar {Auto} Master {/zynq_ultra_ps_e_0/M_AXI_HPM0_FPD} Slave {/GeneratedIP/io_S_AXI} ddr_seg {Auto} intc_ip {New AXI SmartConnect} master_apm {0}}  [get_bd_intf_pins GeneratedIP/io_S_AXI]
            |apply_bd_automation -rule xilinx.com:bd_rule:clkrst -config { Clk {/zynq_ultra_ps_e_0/pl_clk0} Ref_Clk0 {} Ref_Clk1 {} Ref_Clk2 {}}  [get_bd_pins zynq_ultra_ps_e_0/saxihp0_fpd_aclk]
            |connect_bd_net [get_bd_pins rst_ps8_0_99M/peripheral_aresetn] [get_bd_pins util_vector_logic_0/Op1]
            |set_property -dict [list CONFIG.PSU__CRL_APB__PL0_REF_CTRL__FREQMHZ $$FREQ_HZ $backslash
            | CONFIG.PSU__CRL_APB__PL0_REF_CTRL__SRCSEL {RPLL} $backslash
            |] [get_bd_cells zynq_ultra_ps_e_0]
            |
            |# set the address map for HP port
            |assign_bd_address -target_address_space /GeneratedIP/io_M_AXI [get_bd_addr_segs zynq_ultra_ps_e_0/SAXIGP2/HP0_DDR_LOW] -force
            """
      else
        st""
    }

    val synthImplST: ST =
      st"""
          |set PROJECT_PATH [lindex $$argv 0]
          |set PROJECT_NAME [lindex $$argv 1]
          |set IP_DIR [lindex $$argv 2]
          |set IP_NAME [lindex $$argv 3]
          |set FREQ_HZ [lindex $$argv 4]
          |puts $$FREQ_HZ
          |# /home/kejun/development/HLS_slang/zcu102/TestSystem
          |create_project $$PROJECT_NAME $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME -part xczu9eg-ffvb1156-2-e
          |
          |set_property board_part xilinx.com:zcu102:part0:3.4 [current_project]
          |
          |set_property target_language Verilog [current_project]
          |
          |create_bd_design "design_1"
          |update_compile_order -fileset sources_1
          |
          |create_bd_cell -type ip -vlnv xilinx.com:ip:zynq_ultra_ps_e:3.5 zynq_ultra_ps_e_0
          |
          |apply_bd_automation -rule xilinx.com:bd_rule:zynq_ultra_ps_e -config {apply_board_preset "1" }  [get_bd_cells zynq_ultra_ps_e_0]
          |
          |${gpOrHpST}
          |
          |# /home/kejun/development/HLS_slang/zcu102/InsertSortIP/IP_dir
          |set_property  ip_repo_paths  $$IP_DIR [current_project]
          |update_ip_catalog
          |
          |# instantiate the generated IP
          |create_bd_cell -type ip -vlnv user.org:user:$$IP_NAME:1.0 GeneratedIP
          |${blockDesignST}
          |
          |save_bd_design
          |
          |# /home/kejun/development/HLS_slang/zcu102/TestSystem/TestSystem.srcs/sources_1/bd/design_1/design_1.bd
          |make_wrapper -files [get_files $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/$$PROJECT_NAME.srcs/sources_1/bd/design_1/design_1.bd] -top
          |
          |# /home/kejun/development/HLS_slang/zcu102/TestSystem/TestSystem.srcs/sources_1/bd/design_1/hdl/design_1_wrapper.v
          |add_files -norecurse $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/$$PROJECT_NAME.srcs/sources_1/bd/design_1/hdl/design_1_wrapper.v
          |
          |launch_runs impl_1 -to_step write_bitstream -jobs 30
          |wait_on_run impl_1
          |
          |# /home/kejun/development/HLS_slang/zcu102/TestSystem/TestSystem.srcs/sources_1/bd/design_1/design_1.bd
          |set_property pfm_name {} [get_files -all $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/$$PROJECT_NAME.srcs/sources_1/bd/design_1/design_1.bd]
          |
          |# /home/kejun/development/HLS_slang/zcu102/TestSystem/design_1_wrapper.xsa
          |write_hw_platform -fixed -include_bit -force -file $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/design_1_wrapper.xsa
          |
          |open_run impl_1
          |
          |report_utilization -file $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/utilization_report.txt -name utilization_1
          |report_timing_summary -delay_type max -report_unconstrained -check_timing_verbose -max_paths 20 -input_pins -routable_nets -name timing_1 -file $$PROJECT_PATH/$$FREQ_HZ/$$PROJECT_NAME/timing_report.txt
          """

    val autoShScriptST: ST =
      st"""
          |#!/bin/bash
          |
          |TCL_PATH=$$1
          |PROJECT_PATH=$$2
          |IP_NAME=$$3
          |SoC_NAME=$$4
          |FREQ_HZ=$$5
          |
          |vivado -mode batch -source $${TCL_PATH}/ip_generation.tcl -tclargs $${PROJECT_PATH} $${IP_NAME} $${FREQ_HZ}
          |
          |vivado -mode batch -source $${TCL_PATH}/synthesize_zcu102_zynq.tcl -tclargs $${PROJECT_PATH} $${SoC_NAME} $${PROJECT_PATH}/$$FREQ_HZ/$${IP_NAME}/IP_dir $${IP_NAME} $${FREQ_HZ}
          """

    val testManyShScriptST: ST =
      st"""
          |#!/bin/sh
          |
          |log_file="time_log.txt"
          |
          |start_bound=100
          |end_bound=150
          |step=25
          |
          |bound=$$start_bound
          |while [ "$$bound" -le "$$end_bound" ]; do
          |    echo "Running with bound=$$bound" >> "$$log_file"
          |
          |    start=$$(date +%s.%N)
          |    ./auto_script.sh . ./ ${name} TestSystem "$$bound"
          |    end=$$(date +%s.%N)
          |
          |    duration=$$(echo "$$end - $$start" | bc)
          |    echo "Execution time for bound=$$bound: $$duration seconds" >> "$$log_file"
          |    echo "" >> "$$log_file"
          |
          |    bound=$$((bound + step))
          |done
          """

    val zynqCProgramST: ST = {
      if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative)
        st"""
            |#include <stdio.h>
            |#include <stdint.h>
            |#include "platform.h"
            |#include "xil_printf.h"
            |#include "xil_io.h"
            |#include "xparameters.h"
            |
            |#define VALID_ADDR (XPAR_GENERATEDIP_BASEADDR + ${anvil.config.memory})
            |#define READY_ADDR (XPAR_GENERATEDIP_BASEADDR + ${anvil.config.memory})
            |#define ARRAY_ADDR (XPAR_GENERATEDIP_BASEADDR + 0x0)
            |
            |int main()
            |{
            |    init_platform();
            |
            |    printf("benchmark ${name}\n");
            |
            |    Xil_Out32(ARRAY_ADDR, 0xFFFFFFFF);
            |    Xil_Out32(ARRAY_ADDR+4, 0xFFFFFFFF);
            |
            |	   // write to port valid (generated IP)
            |	   Xil_Out32(VALID_ADDR, 0x1);
            |
            |	   // read from port ready (generated IP)
            |	   uint32_t ready = Xil_In32(READY_ADDR);
            |	   while(ready != 0x1) {
            |	   	ready = Xil_In32(READY_ADDR);
            |	   }
            |
            |	   // read the elements form the array
            |	   for(int i = 0; i < 3; i++) {
            |	   	uint32_t c = Xil_In32(ARRAY_ADDR + 20 + i*4);
            |	   	printf("%x\n", c);
            |	   }
            |
            |	   printf("\n");
            |    print("Successfully ran application");
            |
            |    cleanup_platform();
            |    return 0;
            |}
            """
      else if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4 || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr)
        st"""
            |#include <stdio.h>
            |#include <stdint.h>
            |#include "platform.h"
            |#include "xil_printf.h"
            |#include "xil_io.h"
            |#include "xil_cache.h"
            |#include "xparameters.h"
            |
            |#define VALID_ADDR (XPAR_GENERATEDIP_BASEADDR + 0x0)
            |#define READY_ADDR (XPAR_GENERATEDIP_BASEADDR + 0x8)
            |#define DP_ADDR (XPAR_GENERATEDIP_BASEADDR + 0x10)
            |#define ARRAY_ADDR ${if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr) "XPAR_PSU_DDR_0_S_AXI_BASEADDR" else "XPAR_AXI_BRAM_CTRL_1_S_AXI_BASEADDR"}
            |
            |uint8_t load_u8(uint32_t offset) {
            |  uint32_t buffer_addr = ARRAY_ADDR + 20;
            |  uint32_t char_addr = buffer_addr + offset;
            |  uint32_t abs_addr = char_addr & 0xFFFFFFF8;
            |  uint32_t abs_offset = char_addr & 0x00000007;
            |
            |  uint64_t c = Xil_In64(abs_addr);
            |
            |  return (c >> (abs_offset * 8)) & 0xFF;
            |}
            |
            |int main()
            |{
            |  init_platform();
            |
            |  //Xil_DCacheDisable();
            |  printf("benchmark ${name}\n");
            |
            |  // write FFFFFFFFFFFFFFFF to testNum
            |  Xil_Out64(${if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr) "XPAR_PSU_DDR_0_S_AXI_BASEADDR" else "XPAR_AXI_BRAM_CTRL_1_S_AXI_BASEADDR"}, 0xFFFFFFFFFFFFFFFF);
            |  // using memory barrier when disable DCache
            |  //__asm__ volatile("dsb sy");
            |
            |  // using flush when enable DCache
            |  ${if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr) "Xil_DCacheFlushRange(XPAR_PSU_DDR_0_S_AXI_BASEADDR, sizeof(uint64_t));" else ""}
            |
            |  // write to port valid (generated IP)
            |  Xil_Out64(VALID_ADDR, 0x1);
            |
            |  // read from port ready (generated IP)
            |  uint64_t ready = Xil_In64(READY_ADDR);
            |  while(ready != 0x1) {
            |    ready = Xil_In64(READY_ADDR);
            |  }
            |
            |  uint64_t displaySize = ${anvil.config.printSize};
            |  uint64_t DP = Xil_In64(DP_ADDR);
            |  int lo = (DP < displaySize) ? 0 : DP;
            |  int hi = (DP < displaySize) ? DP : displaySize + DP - 1;
            |  char output[displaySize + 1];
            |  // fetch the elements form the array
            |  int j = 0;
            |  for(int i = lo; i < hi; i++) {
            |	   uint32_t offset = i % displaySize;
            |	   output[j++] = load_u8(offset);
            |  }
            |  output[j] = '\0'; // null-terminate
            |  printf("result: %s\n", output);
            |
            |  print("Successfully ran application");
            |
            |  cleanup_platform();
            |  return 0;
            |}
            """
      else
        st""
    }

    @strictpure def xilinxAddSub64ST(isAdder: B, sign: B): ST = {
      val opStr: String = if(isAdder) "Adder" else "Subtractor"
      val signStr: String = if(sign) "Signed" else "Unsigned"
      st"""
          |module Xilinx${opStr}${signStr}64Wrapper(
          |    input wire clk,
          |    input wire ce,
          |    input wire [63:0] A,
          |    input wire [63:0] B,
          |    output wire valid,
          |    output wire [63:0] S);
          |
          |  reg [5:0] valid_shift = 6'b0;
          |
          |  Xilinx${opStr}${signStr}64 u_Xilinx${opStr}${signStr}64 (
          |    .CLK(clk),
          |    .CE(ce),
          |    .A(A),
          |    .B(B),
          |    .S(S)
          |  );
          |
          |  always @(posedge clk) begin
          |    if(ce & ~valid_shift[5])
          |      valid_shift <= {valid_shift[4:0], 1'b1};
          |    else
          |      valid_shift <= 0;
          |  end
          |
          |  assign valid = valid_shift[5];
          |endmodule
          """
    }

    @strictpure def xilinxMul64ST(sign: B): ST = {
      val signStr: String = if(sign) "Signed" else "Unsigned"
      st"""
          |module XilinxMultiplier${signStr}64Wrapper(
          |    input wire clk,
          |    input wire ce,
          |    input wire [63:0] a,
          |    input wire [63:0] b,
          |    output wire valid,
          |    output wire [63:0] p);
          |
          |  localparam LATENCY = 18;
          |
          |  reg [LATENCY-1:0] valid_shift;
          |  XilinxMultiplier${signStr}64 u_XilinxMultiplier${signStr}64 (
          |    .CLK(clk),
          |    .CE(ce),
          |    .A(a),
          |    .B(b),
          |    .P(p)
          |  );
          |
          |  always @(posedge clk) begin
          |    if(ce & ~valid_shift[LATENCY-1])
          |      valid_shift <= {valid_shift[LATENCY-2:0], 1'b1};
          |    else
          |      valid_shift <= 0;
          |  end
          |
          |  assign valid = valid_shift[LATENCY-1];
          |endmodule
          """
    }

    @strictpure def xilinxDiv64ST(sign: B): ST = {
      val signStr: String = if(sign) "Signed" else "Unsigned"
      st"""
          |module XilinxDivider${signStr}64Wrapper(
          |    input wire clock,
          |    input wire resetn,
          |    input wire [63:0] a,
          |    input wire [63:0] b,
          |    input wire start,
          |    output wire valid,
          |    output wire [63:0] quotient,
          |    output wire [63:0] remainder);
          |
          |  localparam IDLE  = 2'b00;
          |  localparam START = 2'b01;
          |  localparam WAIT  = 2'b10;
          |
          |  reg start_reg;
          |  reg [1:0] state;
          |  wire [127:0] dout_tdata;
          |  wire divisor_tready, dividend_tready;
          |  XilinxDivider${signStr}64 u_XilinxDivider${signStr}64 (
          |    .aclk(clock),                                      // input wire aclk
          |    .aresetn(resetn),                                // input wire aresetn
          |    .s_axis_divisor_tvalid(start_reg),    // input wire s_axis_divisor_tvalid
          |    .s_axis_divisor_tready(divisor_tready),
          |    .s_axis_divisor_tdata(b),      // input wire [63 : 0] s_axis_divisor_tdata
          |    .s_axis_dividend_tvalid(start_reg),  // input wire s_axis_dividend_tvalid
          |    .s_axis_dividend_tready(dividend_tready),
          |    .s_axis_dividend_tdata(a),    // input wire [63 : 0] s_axis_dividend_tdata
          |    .m_axis_dout_tvalid(valid),          // output wire m_axis_dout_tvalid
          |    .m_axis_dout_tdata(dout_tdata)            // output wire [127 : 0] m_axis_dout_tdata
          |  );
          |
          |  always @(posedge clock) begin
          |    if (~resetn) begin
          |        start_reg <= 0;
          |        state <= IDLE;
          |    end else begin
          |        case(state)
          |            IDLE: begin
          |                if(start) begin
          |                    start_reg <= 1'b1;
          |                    state <= START;
          |                end
          |            end
          |            START: begin
          |                if(~valid) begin
          |                    start_reg <= 1'b0;
          |                    state <= WAIT;
          |                end
          |            end
          |            WAIT: begin
          |                if(~start) begin
          |                    state <= IDLE;
          |                end
          |            end
          |        endcase
          |    end
          |  end
          |
          |  assign quotient = dout_tdata[127:64];
          |  assign remainder = dout_tdata[63:0];
          |endmodule
          """
    }

    @strictpure def xilinxBRAMWrapperST: ST = {
      st"""
          |module XilinxBRAMWrapper(
          |    input wire clk,
          |    input wire ena,
          |    input wire wea,
          |    input wire [9:0] addra,
          |    input wire [7:0] dina,
          |    output wire [7:0] douta,
          |    input wire enb,
          |    input wire web,
          |    input wire [9:0] addrb,
          |    input wire [7:0] dinb,
          |    output wire [7:0] doutb
          |);
          |
          |  XilinxBRAM u_XilinxBRAM (
          |    .clka(clk),    // input wire clka
          |    .ena(ena),      // input wire ena
          |    .wea(wea),      // input wire [0 : 0] wea
          |    .addra(addra),  // input wire [9 : 0] addra
          |    .dina(dina),    // input wire [7: 0] dina
          |    .douta(douta),  // output wire [7: 0] douta
          |    .clkb(clk),    // input wire clkb
          |    .enb(enb),      // input wire enb
          |    .web(web),      // input wire [0 : 0] web
          |    .addrb(addrb),  // input wire [9 : 0] addrb
          |    .dinb(dinb),    // input wire [7: 0] dinb
          |    .doutb(doutb)  // output wire [7: 0] doutb
          |  );
          |
          |endmodule
          """
    }

    @strictpure def xilinxIndexAdderWrapperST(width: Z): ST = {
      val latencyST: ST =
        if(cyclesXilinxAdder(width) == 1)
          st"""1'b1"""
        else
          st"""{valid_shift[LATENCY-2:0], 1'b1}"""

      st"""
          |module XilinxIndexAdderWrapper (
          |    input wire clk,
          |    input wire ce,
          |    input wire [${width-1}:0] A,
          |    input wire [${width-1}:0] B,
          |    output wire valid,
          |    output wire [${width-1}:0] S);
          |
          |  localparam LATENCY = ${cyclesXilinxAdder(anvil.typeBitSize(spType))};
          |  reg [LATENCY-1:0] valid_shift = 'd0;
          |
          |  XilinxIndexAdder u_XilinxIndexAdder (
          |    .CLK(clk),
          |    .CE(ce),
          |    .A(A),
          |    .B(B),
          |    .S(S)
          |  );
          |
          |  always @(posedge clk) begin
          |    if(ce & ~valid_shift[LATENCY-1])
          |      valid_shift <= ${latencyST.render};
          |    else
          |      valid_shift <= 0;
          |  end
          |
          |  assign valid = valid_shift[LATENCY-1];
          |endmodule
          """
    }

    @strictpure def xilinxIndexMultiplierWrapperST(width: Z): ST = {
      val latencyST: ST =
        if(cyclesXilinxMultiplier(width) == 1)
          st"""1'b1"""
        else
          st"""{valid_shift[LATENCY-2:0], 1'b1}"""

      st"""
          |module XilinxIndexMultiplierWrapper (
          |    input wire clk,
          |    input wire ce,
          |    input wire [${width-1}:0] A,
          |    input wire [${width-1}:0] B,
          |    output wire valid,
          |    output wire [${width-1}:0] P);
          |
          |  localparam LATENCY = ${cyclesXilinxMultiplier(anvil.typeBitSize(spType))};
          |  reg [LATENCY-1:0] valid_shift = 'd0;
          |
          |  XilinxIndexMultiplier u_XilinxIndexMultiplier (
          |    .CLK(clk),
          |    .CE(ce),
          |    .A(A),
          |    .B(B),
          |    .P(P)
          |  );
          |
          |  always @(posedge clk) begin
          |    if(ce & ~valid_shift[LATENCY-1])
          |      valid_shift <= ${latencyST.render};
          |    else
          |      valid_shift <= 0;
          |  end
          |
          |  assign valid = valid_shift[LATENCY-1];
          |endmodule
          """
    }

    output.add(T, ISZ("config.txt"), configST)
    for(entry <- arbiterModuleST.entries) {
      output.add(T, ISZ("chisel/src/main/scala", s"${entry._1}.scala"), st"${(entry._2, "")}")
    }
    output.add(T, ISZ("chisel/src/main/scala", s"Stack.scala"), stackST)
    output.add(T, ISZ("chisel/src/main/scala", s"Router.scala"), routerST)
    output.add(T, ISZ("chisel/src/main/scala", s"chisel-${name}.scala"), processedProcedureST)
    output.add(T, ISZ("chisel", "build.sbt"), buildSbtST())
    output.add(T, ISZ("chisel", "project", "build.properties"), st"sbt.version=${output.sbtVersion}")

    if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) {
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxBRAMWrapper.v"), xilinxBRAMWrapperST)
    }
    output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxIndexAdderWrapper.v"), xilinxIndexAdderWrapperST(anvil.typeBitSize(spType)))
    output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxIndexMultiplierWrapper.v"), xilinxIndexMultiplierWrapperST(anvil.typeBitSize(spType)))
    if(!anvil.config.noXilinxIp) {
      output.addPerm(T, ISZ("chisel/..", "test_many.sh"), testManyShScriptST, "+x")
      output.addPerm(T, ISZ("chisel/..", "auto_script.sh"), autoShScriptST, "+x")
      output.add(T, ISZ("chisel/..", "synthesize_zcu102_zynq.tcl"), synthImplST)
      output.add(T, ISZ("chisel/..", "ip_generation.tcl"), ipGenerationTclST)
      output.add(T, ISZ("chisel/src/main/resources/C", "zynq_program.c"), zynqCProgramST)
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxAdderSigned64Wrapper.v"), xilinxAddSub64ST(T ,T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxAdderUnsigned64Wrapper.v"), xilinxAddSub64ST(T, F))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxSubtractorSigned64Wrapper.v"), xilinxAddSub64ST(F, T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxSubtractorUnsigned64Wrapper.v"), xilinxAddSub64ST(F, F))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxDividerSigned64Wrapper.v"), xilinxDiv64ST(T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxDividerUnsigned64Wrapper.v"), xilinxDiv64ST(F))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxMultiplierSigned64Wrapper.v"), xilinxMul64ST(T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxMultiplierUnsigned64Wrapper.v"), xilinxMul64ST(F))
    }

    if (anvil.config.genVerilog) {
      @strictpure def xilinxBUFGWrapperST: ST = {
        st"""
            |module XilinxBUFGWrapper (
            |  input wire I,
            |  output wire O
            |);
            |  BUFG bufg_inst(
            |    .I(I),
            |    .O(O)
            |  );
            |endmodule
          """
      }
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxBUFGWrapper.v"), xilinxBUFGWrapperST)
      output.add(T, ISZ("chisel/src/test/scala", s"${name}VerilogGeneration.scala"), verilogGenerationST(name))
    }

    anvil.config.simOpt match {
      case Some(simConfig) => {
        output.add(T, ISZ("chisel/src/test/scala", s"${name}Bench.scala"), testBenchST(name, simConfig.cycles))
      }
      case _ =>
    }

    return
  }

  @pure def verilogGenerationST(moduleName: String): ST = {
    val verilogGenST: ST =
      st"""
          |import chisel3.stage.{ChiselStage,ChiselGeneratorAnnotation}
          |
          |object ${moduleName}VerilogGeneration extends App {
          |  (new ChiselStage).execute(
          |    Array("--target-dir", "generated_verilog"),
          |    Seq(ChiselGeneratorAnnotation(() => new ${moduleName}()))
          |  )
          |}
          |
        """

    return verilogGenST
  }

  @pure def testBenchST(moduleName: String, cycles: Z): ST = {
    val benchST: ST =
      st"""
          |import chisel3._
          |import chiseltest._
          |import chiseltest.simulator.WriteVcdAnnotation
          |import org.scalatest.flatspec.AnyFlatSpec
          |
          |class ${moduleName}Bench extends AnyFlatSpec with ChiselScalatestTester {
          |  "${moduleName}Bench" should "work" in {
          |    test(new ${moduleName}()).withAnnotations(Seq(WriteVcdAnnotation, VerilatorBackendAnnotation)) { dut =>
          |      dut.clock.setTimeout(10000)
          |
          |      dut.reset.poke(true.B)
          |      for (i <- 0 until (5)) {
          |        dut.clock.step()
          |      }
          |      dut.reset.poke(false.B)
          |      dut.clock.step()
          |
          |      // write 8 FF to testNum
          |      dut.io.S_AXI_AWVALID.poke(true.B)
          |      dut.io.S_AXI_AWADDR.poke(0.U)
          |      dut.clock.step()
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_AWVALID.poke(false.B)
          |      dut.io.S_AXI_WVALID.poke(true.B)
          |      dut.io.S_AXI_WDATA.poke("hFFFFFFFF".U)
          |      dut.io.S_AXI_WSTRB.poke("hF".U)
          |      dut.clock.step()
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_WVALID.poke(false.B)
          |      dut.io.S_AXI_BREADY.poke(true.B)
          |      dut.clock.step(6)
          |      //while (!dut.io.S_AXI_BVALID.peek().litToBoolean) {
          |      //  dut.clock.step(1)
          |      //}
          |
          |      dut.io.S_AXI_AWVALID.poke(true.B)
          |      dut.io.S_AXI_AWADDR.poke(4.U)
          |      dut.clock.step()
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_AWVALID.poke(false.B)
          |      dut.io.S_AXI_WVALID.poke(true.B)
          |      dut.io.S_AXI_WDATA.poke("hFFFFFFFF".U)
          |      dut.io.S_AXI_WSTRB.poke("hF".U)
          |      dut.clock.step()
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_WVALID.poke(false.B)
          |      dut.io.S_AXI_BREADY.poke(true.B)
          |      dut.clock.step(6)
          |      //while (!dut.io.S_AXI_BVALID.peek().litToBoolean) {
          |      //  dut.clock.step(1)
          |      //}
          |
          |      // write valid signal
          |      dut.io.S_AXI_AWVALID.poke(true.B)
          |      dut.io.S_AXI_AWADDR.poke(${anvil.config.memory}.U)
          |      dut.clock.step()
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_AWVALID.poke(false.B)
          |      dut.io.S_AXI_WVALID.poke(true.B)
          |      dut.io.S_AXI_WDATA.poke("h01".U)
          |      dut.io.S_AXI_WSTRB.poke("h1".U)
          |      dut.clock.step()
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_WVALID.poke(false.B)
          |      dut.io.S_AXI_BREADY.poke(true.B)
          |      dut.clock.step(6)
          |      //while (!dut.io.S_AXI_BVALID.peek().litToBoolean) {
          |      //  dut.clock.step(1)
          |      //}
          |
          |      dut.clock.step(${cycles})
          |
          |      for(i <- 0 until ${anvil.config.printSize / 4 + 1}) {
          |        dut.io.S_AXI_ARVALID.poke(true.B)
          |        dut.io.S_AXI_ARADDR.poke((20 + i * 4).U)
          |        dut.clock.step(1)
          |        dut.clock.step(1)
          |
          |        dut.io.S_AXI_ARVALID.poke(false.B)
          |        dut.io.S_AXI_RREADY.poke(true.B)
          |        dut.clock.step(8)
          |        //while (!dut.io.S_AXI_RVALID.peek().litToBoolean) {
          |        //  dut.clock.step(1)
          |        //}
          |      }
          |
          |      dut.clock.step(50)
          |    }
          |  }
          |}
        """

    return benchST
  }

  @pure def buildSbtST(): ST = {
    val sbtST: ST = {
      /*
      st"""
          |ThisBuild / scalaVersion     := "2.13.16"
          |ThisBuild / version          := "0.1.0"
          |ThisBuild / organization     := "Kansas State University"
          |
          |val chiselVersion = "6.7.0"
          |
          |lazy val root = (project in file("."))
          |  .settings(
          |    name := "Chisel6-Test",
          |    libraryDependencies ++= Seq(
          |      "org.chipsalliance" %% "chisel" % chiselVersion,
          |      "edu.berkeley.cs" %% "chiseltest" % "6.0.0" % Test,
          |      "org.scalatest" %% "scalatest" % "3.2.17" % "test",
          |    ),
          |    scalacOptions ++= Seq(
          |      "-language:reflectiveCalls",
          |      "-deprecation",
          |      "-feature",
          |      "-Xcheckinit",
          |      "-Ymacro-annotations",
          |    ),
          |    addCompilerPlugin("org.chipsalliance" % "chisel-plugin" % chiselVersion cross CrossVersion.full),
          |)
        """
       */
      st"""scalaVersion := "2.13.10"
          |
          |
          |scalacOptions ++= Seq(
          |  "-feature",
          |  "-language:reflectiveCalls",
          |)
          |
          |// Chisel 3.5
          |addCompilerPlugin("edu.berkeley.cs" % "chisel3-plugin" % "3.5.6" cross CrossVersion.full)
          |libraryDependencies += "edu.berkeley.cs" %% "chisel3" % "3.5.6"
          |libraryDependencies += "edu.berkeley.cs" %% "chiseltest" % "0.5.6"
        """
    }

    return sbtST
  }

  @pure def processProcedure(name: String, o: AST.IR.Procedure, maxRegisters: Util.TempVector, globalInfoMap: HashSMap[QName, VarInfo]): ST = {

    @pure def generalPurposeRegisterST: ST = {
      var generalRegMap: HashMap[String, (Z,Z,B)] = HashMap.empty[String, (Z,Z,B)]
      var generalRegST: ISZ[ST] = ISZ[ST]()

      for(i <- 0 until maxRegisters.unsigneds.size){
        if(maxRegisters.unsigneds(i) > 0) {
          generalRegMap = generalRegMap + (s"${generalRegName}U${i+1}" ~> (i+1, maxRegisters.unsigneds(i), F))
        }
      }

      for(entry <- maxRegisters.signeds.entries) {
        if(entry._2 > 0) {
          generalRegMap = generalRegMap + (s"${generalRegName}S${entry._1}" ~> (entry._1, entry._2, T))
        }
      }

      for(entry <- generalRegMap.entries) {
        //generalRegST = generalRegST :+ st"val ${entry._1} = RegInit(VecInit(${entry._2._2}, ${if(entry._2._3) "SInt" else "UInt"}(${entry._2._1}.W)))"
        generalRegST = generalRegST :+ st"val ${entry._1} = RegInit(VecInit(Seq.fill(${entry._2._2})(${if(entry._2._3) "0.S" else "0.U"}(${entry._2._1}.W))))"
      }

      return st"${(generalRegST, "\n")}"
    }

    @strictpure def cpST(moduleName: String): ST = {
      st"""
          |val ${moduleName}CP = RegInit(2.U(CODE_POINTER_WIDTH.W))
        """
    }

    @pure def globalTempST: ST = {
      var globalTempSTs: ISZ[ST] = ISZ[ST]()
      for(entry <- globalInfoMap.entries) {
        if(isTempGlobal(anvil, entry._2.tipe, entry._1)) {
          val signed: B = anvil.isSigned(entry._2.tipe)
          val initValueST: ST = if(signed) st"0.S" else st"0.U"
          val bitWidthST: ST = st"${anvil.typeBitSize(entry._2.tipe)}"
          globalTempSTs = globalTempSTs :+ st"val ${globalName(entry._1)} = RegInit(${initValueST}(${bitWidthST}.W))"
        }
      }
      return st"${(globalTempSTs, "\n")}"
    }

    @pure def topST(stateMachineST: ST, stateMachineIdxRange: HashSMap[Z, Z], stateFunctionObjectST: ST): ST = {
      val instanceDeclST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for (entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insDeclST(b, entry._2)
        }
        instanceST = instanceST :+ insDeclST(IntrinsicIP(HwSynthesizer2.defaultIndexing), ipAlloc.indexingAllocSize)
        if (anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          instanceST = instanceST :+ insDeclST(BlockMemoryIP(), 1)
        }
        st"""${(instanceST, "\n")}"""
      }

      val instancePortFuncST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for (entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insPortFuncST(b, entry._2)
        }
        instanceST = instanceST :+ insPortFuncST(IntrinsicIP(HwSynthesizer2.defaultIndexing), ipAlloc.indexingAllocSize)
        if (anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          instanceST = instanceST :+ insPortFuncST(BlockMemoryIP(), 1)
        }
        st"""${(instanceST, "\n")}"""
      }

      val instancePortCallST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for (entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insPortCallST(b, entry._2)
        }
        instanceST = instanceST :+ insPortCallST(IntrinsicIP(HwSynthesizer2.defaultIndexing), ipAlloc.indexingAllocSize)
        if (anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          instanceST = instanceST :+ insPortCallST(BlockMemoryIP(), 1)
        }
        st"""${(instanceST, "\n")}"""
      }

      val bramDefaultPortValueST: ST =
        st"""
            |// BRAM default
            |${sharedMemName}.io.mode         := 0.U
            |${sharedMemName}.io.readAddr     := 0.U
            |${sharedMemName}.io.readOffset   := 0.U
            |${sharedMemName}.io.readLen      := 0.U
            |${sharedMemName}.io.writeAddr    := 0.U
            |${sharedMemName}.io.writeOffset  := 0.U
            |${sharedMemName}.io.writeLen     := 0.U
            |${sharedMemName}.io.writeData    := 0.U
            |${sharedMemName}.io.dmaSrcAddr   := 0.U
            |${sharedMemName}.io.dmaDstAddr   := 0.U
            |${sharedMemName}.io.dmaDstOffset := 0.U
            |${sharedMemName}.io.dmaSrcLen    := 0.U
            |${sharedMemName}.io.dmaDstLen    := 0.U
          """

      val memWriteST: ST =
        if (anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default)
          st"""
              |when(r_writeAddr === ${anvil.config.memory}.U) {
              |  writeState              := sBActive
              |  r_valid                 := r_writeData(0).asBool
              |} .otherwise {
              |  ${sharedMemName}.io.mode          := 2.U
              |  ${sharedMemName}.io.writeAddr     := r_writeAddr
              |  ${sharedMemName}.io.writeOffset   := 0.U
              |  ${sharedMemName}.io.writeLen      := r_writeLen
              |  ${sharedMemName}.io.writeData     := r_writeData
              |}
              |
              |when((r_writeAddr =/= ${anvil.config.memory}.U) & ${sharedMemName}.io.writeValid) {
              |  ${sharedMemName}.io.mode          := 0.U
              |  writeState              := sBActive
              |}
            """
        else
          st"""
              |writeState := sBActive
              |when(r_writeAddr === ${anvil.config.memory}.U){
              |  r_valid := r_writeData(0)
              |} .otherwise{
              |  for(byteIndex <- 0 until (C_S_AXI_DATA_WIDTH/8)) {
              |    when(io.S_AXI_WSTRB(byteIndex.U) === 1.U) {
              |      ${sharedMemName}(r_writeAddr + byteIndex.U) := r_writeData((byteIndex * 8) + 7, byteIndex * 8)
              |    }
              |  }
              |}
            """

      val memReadST: ST = {
        if (anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default)
          st"""
              |when(r_readAddr === ${anvil.config.memory}.U) {
              |  r_s_axi_rdata         := r_ready
              |  readState             := sReadEnd
              |} .otherwise {
              |  ${sharedMemName}.io.mode        := 1.U
              |  ${sharedMemName}.io.readAddr    := r_readAddr
              |  ${sharedMemName}.io.readOffset  := 0.U
              |  ${sharedMemName}.io.readLen     := (C_S_AXI_DATA_WIDTH/8).U
              |}
              |
              |when((r_readAddr =/= ${anvil.config.memory}.U) & ${sharedMemName}.io.readValid) {
              |  ${sharedMemName}.io.mode        := 0.U
              |
              |  r_s_axi_rdata         := ${sharedMemName}.io.readData
              |  readState             := sReadEnd
              |}
            """
        else
          st"""
              |readState := sReadEnd
              |when(r_readAddr === ${anvil.config.memory}.U) {
              |  r_s_axi_rdata := r_ready
              |} .otherwise {
              |  val readBytes = Seq.tabulate(C_S_AXI_DATA_WIDTH/8) { i =>
              |    ${sharedMemName}(io.S_AXI_ARADDR + i.U)
              |  }
              |  r_s_axi_rdata := Cat(readBytes.reverse)
              |}
            """
      }

      @pure def axi4LiteInterfaceST: ST = {
        val simAxi4LiteST: ST =
          st"""
              |// registers for diff channels
              |val r_s_axi_awready = Reg(Bool())
              |val r_s_axi_wready  = Reg(Bool())
              |val r_s_axi_bvalid  = Reg(Bool())
              |val r_s_axi_arready = Reg(Bool())
              |val r_s_axi_rdata   = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
              |val r_s_axi_rvalid  = Reg(Bool())
              |
              |val r_writeAddr     = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
              |val r_writeData     = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
              |val r_writeLen      = Reg(UInt((C_S_AXI_DATA_WIDTH / 8).W))
              |
              |val r_readAddr      = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
              |val r_readData      = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
              |val r_readLen       = Reg(UInt((C_S_AXI_DATA_WIDTH / 8).W))
              |
              |${if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) bramDefaultPortValueST.render else st""}
              |
              |// write state machine
              |val sWriteIdle :: sAWActive :: sWActive :: sBActive:: Nil = Enum(4)
              |val writeState = RegInit(sWriteIdle)
              |
              |r_s_axi_awready := Mux(io.S_AXI_AWVALID, true.B ,false.B)
              |r_s_axi_wready  := Mux((writeState === sAWActive) & io.S_AXI_WVALID,  true.B, false.B)
              |r_s_axi_bvalid  := Mux((writeState === sWActive)${if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) s"& ${sharedMemName}.io.writeValid" else ""}, true.B, false.B) |
              |                   Mux(io.S_AXI_WVALID & io.S_AXI_WREADY & (r_writeAddr === ${anvil.config.memory}.U), true.B, false.B)
              |switch(writeState) {
              |  is(sWriteIdle) {
              |    writeState  := Mux(io.S_AXI_AWVALID & io.S_AXI_AWREADY, sAWActive, sWriteIdle)
              |    r_writeAddr := Mux(io.S_AXI_AWVALID & io.S_AXI_AWREADY, io.S_AXI_AWADDR, r_writeAddr)
              |  }
              |  is(sAWActive) {
              |    writeState  := Mux(io.S_AXI_WVALID & io.S_AXI_WREADY, sWActive, sAWActive)
              |    r_writeLen  := Mux(io.S_AXI_WVALID & io.S_AXI_WREADY, PopCount(io.S_AXI_WSTRB), r_writeLen)
              |    r_writeData := Mux(io.S_AXI_WVALID & io.S_AXI_WREADY, io.S_AXI_WDATA, r_writeData)
              |  }
              |  is(sWActive) {
              |    ${memWriteST}
              |  }
              |  is(sBActive) {
              |    writeState := Mux(io.S_AXI_BVALID & io.S_AXI_BREADY, sWriteIdle, sBActive)
              |  }
              |}
              |
              |// read state machine
              |val sReadIdle :: sARActive :: sRActive :: sReadEnd :: Nil = Enum(4)
              |val readState = RegInit(sReadIdle)
              |
              |r_s_axi_arready := Mux(io.S_AXI_ARVALID, true.B, false.B)
              |r_s_axi_rvalid  := Mux((readState === sRActive) ${if (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) s" & (${sharedMemName}.io.readValid | r_readAddr === ${anvil.config.memory}.U)" else ""}, true.B, false.B)
              |switch(readState) {
              |  is(sReadIdle) {
              |    readState := Mux(io.S_AXI_ARVALID, sARActive, sReadIdle)
              |  }
              |  is(sARActive) {
              |    readState := Mux(io.S_AXI_ARVALID & io.S_AXI_ARREADY, sRActive, sARActive)
              |
              |    when(io.S_AXI_ARVALID & io.S_AXI_ARREADY) {
              |      r_readAddr := io.S_AXI_ARADDR
              |    }
              |  }
              |  is(sRActive) {
              |    ${memReadST}
              |  }
              |  is(sReadEnd) {
              |    readState := Mux(io.S_AXI_RVALID & io.S_AXI_RREADY, sReadIdle, sReadEnd)
              |  }
              |}
              |
              |// write address channel
              |io.S_AXI_AWREADY := r_s_axi_awready
              |
              |// write channel
              |io.S_AXI_WREADY  := r_s_axi_wready
              |
              |// write response channel
              |io.S_AXI_BRESP   := 0.U
              |io.S_AXI_BVALID  := r_s_axi_bvalid
              |
              |// read address channel
              |io.S_AXI_ARREADY := r_s_axi_arready
              |
              |// read channel
              |io.S_AXI_RDATA   := r_s_axi_rdata
              |io.S_AXI_RRESP   := 0.U
              |io.S_AXI_RVALID  := r_s_axi_rvalid
            """

        val genVerilgoAxi4LiteST: ST =
          st"""
              |val ADDR_LSB: Int = (C_S_AXI_DATA_WIDTH / 32) + 1
              |
              |// registers for diff channels
              |// write address channel
              |val r_s_axi_awready = RegInit(true.B)
              |val r_s_axi_awaddr  = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
              |
              |// write data channel
              |val r_s_axi_wready  = RegInit(true.B)
              |val r_s_axi_wdata   = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
              |
              |// write response channel
              |val r_s_axi_bvalid  = RegInit(false.B)
              |
              |// read address channel
              |val r_s_axi_arready = RegInit(true.B)
              |val r_s_axi_araddr  = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
              |
              |// read data channel
              |val r_s_axi_rvalid  = RegInit(false.B)
              |val r_s_axi_rdata   = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
              |
              |// registers for valid and ready
              |// r_control(0) -- valid
              |// r_control(1) -- ready
              |// r_control(2) -- DP
              |val initControlVals = Seq(0.U(C_S_AXI_DATA_WIDTH.W), 0.U(C_S_AXI_DATA_WIDTH.W), 0.U(C_S_AXI_DATA_WIDTH.W))
              |val r_control = RegInit(VecInit(initControlVals))
              |r_valid := r_control(0)(0).asBool
              |r_control(1) := r_ready.asUInt
              |r_control(2) := DP
              |
              |// write logic
              |val r_aw_valid = RegInit(false.B)
              |val r_w_valid  = RegInit(false.B)
              |when(io.S_AXI_AWVALID & io.S_AXI_AWREADY) {
              |  r_s_axi_awready           := false.B
              |  r_s_axi_awaddr            := io.S_AXI_AWADDR(C_S_AXI_ADDR_WIDTH - 1, ADDR_LSB)
              |  r_aw_valid                := true.B
              |}
              |
              |when(io.S_AXI_WVALID & io.S_AXI_WREADY) {
              |  r_s_axi_wready            := false.B
              |  r_s_axi_wdata             := io.S_AXI_WDATA
              |  r_w_valid                 := true.B
              |}
              |
              |when(r_aw_valid & r_w_valid) {
              |  r_s_axi_bvalid            := true.B
              |  r_control(r_s_axi_awaddr) := r_s_axi_wdata
              |
              |  r_aw_valid                := false.B
              |  r_w_valid                 := false.B
              |}
              |
              |when(io.S_AXI_BVALID & io.S_AXI_BREADY) {
              |  r_s_axi_bvalid            := false.B
              |  r_s_axi_awready           := true.B
              |  r_s_axi_wready            := true.B
              |}
              |
              |// read logic
              |val r_ar_valid = RegInit(false.B)
              |
              |when(io.S_AXI_ARVALID & io.S_AXI_ARREADY) {
              |  r_s_axi_arready           := false.B
              |  r_s_axi_araddr            := io.S_AXI_ARADDR(C_S_AXI_ADDR_WIDTH - 1, ADDR_LSB)
              |  r_ar_valid                := true.B
              |}
              |
              |when(r_ar_valid) {
              |  r_s_axi_rvalid            := true.B
              |  r_s_axi_rdata             := r_control(r_s_axi_araddr)
              |  r_ar_valid                := false.B
              |}
              |
              |when(io.S_AXI_RVALID & io.S_AXI_RREADY) {
              |  r_s_axi_rvalid            := false.B
              |  r_s_axi_arready           := true.B
              |}
              |
              |// write address channel
              |io.S_AXI_AWREADY := r_s_axi_awready
              |
              |// write channel
              |io.S_AXI_WREADY  := r_s_axi_wready
              |
              |// write response channel
              |io.S_AXI_BRESP   := 0.U
              |io.S_AXI_BVALID  := r_s_axi_bvalid
              |
              |// read address channel
              |io.S_AXI_ARREADY := r_s_axi_arready
              |
              |// read channel
              |io.S_AXI_RDATA   := r_s_axi_rdata
              |io.S_AXI_RRESP   := 0.U
              |io.S_AXI_RVALID  := r_s_axi_rvalid
            """

        if (anvil.config.genVerilog && (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4)) {
          return genVerilgoAxi4LiteST
        } else {
          return simAxi4LiteST
        }
      }

      val axi4FullMasterST: ST =
        st"""
            |// master logic
            |// master write address channel
            |val M_AXI_AWID    = Output(UInt(1.W))
            |val M_AXI_AWADDR  = Output(UInt(C_M_AXI_ADDR_WIDTH.W))
            |val M_AXI_AWLEN   = Output(UInt(8.W))
            |val M_AXI_AWSIZE  = Output(UInt(3.W))
            |val M_AXI_AWBURST = Output(UInt(2.W))
            |val M_AXI_AWLOCK  = Output(Bool())
            |val M_AXI_AWCACHE = Output(UInt(4.W))
            |val M_AXI_AWPROT  = Output(UInt(3.W))
            |val M_AXI_AWQOS   = Output(UInt(4.W))
            |val M_AXI_AWUSER  = Output(UInt(1.W))
            |val M_AXI_AWVALID = Output(Bool())
            |val M_AXI_AWREADY = Input(Bool())
            |
            |// master write data channel
            |val M_AXI_WDATA  = Output(UInt(C_M_AXI_DATA_WIDTH.W))
            |val M_AXI_WSTRB  = Output(UInt((C_M_AXI_DATA_WIDTH/8).W))
            |val M_AXI_WLAST  = Output(Bool())
            |val M_AXI_WUSER  = Output(UInt(1.W))
            |val M_AXI_WVALID = Output(Bool())
            |val M_AXI_WREADY = Input(Bool())
            |
            |// master write response channel
            |val M_AXI_BID    = Input(UInt(1.W))
            |val M_AXI_BRESP  = Input(UInt(2.W))
            |val M_AXI_BUSER  = Input(UInt(1.W))
            |val M_AXI_BVALID = Input(Bool())
            |val M_AXI_BREADY = Output(Bool())
            |
            |// master read address channel
            |val M_AXI_ARID    = Output(UInt(1.W))
            |val M_AXI_ARADDR  = Output(UInt(C_M_AXI_ADDR_WIDTH.W))
            |val M_AXI_ARLEN   = Output(UInt(8.W))
            |val M_AXI_ARSIZE  = Output(UInt(3.W))
            |val M_AXI_ARBURST = Output(UInt(2.W))
            |val M_AXI_ARLOCK  = Output(Bool())
            |val M_AXI_ARCACHE = Output(UInt(4.W))
            |val M_AXI_ARPROT  = Output(UInt(3.W))
            |val M_AXI_ARQOS   = Output(UInt(4.W))
            |val M_AXI_ARUSER  = Output(UInt(1.W))
            |val M_AXI_ARVALID = Output(Bool())
            |val M_AXI_ARREADY = Input(Bool())
            |
            |// master read data channel
            |val M_AXI_RID    = Input(UInt(1.W))
            |val M_AXI_RDATA  = Input(UInt(C_M_AXI_DATA_WIDTH.W))
            |val M_AXI_RRESP  = Input(UInt(2.W))
            |val M_AXI_RLAST  = Input(Bool())
            |val M_AXI_RUSER  = Input(UInt(1.W))
            |val M_AXI_RVALID = Input(Bool())
            |val M_AXI_RREADY = Output(Bool())
          """

      val axi4FullMasterConnectionST: ST =
        st"""
            |io.M_AXI_AWID    := ${sharedMemName}.io.M_AXI_AWID
            |io.M_AXI_AWADDR  := ${sharedMemName}.io.M_AXI_AWADDR
            |io.M_AXI_AWLEN   := ${sharedMemName}.io.M_AXI_AWLEN
            |io.M_AXI_AWSIZE  := ${sharedMemName}.io.M_AXI_AWSIZE
            |io.M_AXI_AWBURST := ${sharedMemName}.io.M_AXI_AWBURST
            |io.M_AXI_AWLOCK  := ${sharedMemName}.io.M_AXI_AWLOCK
            |io.M_AXI_AWCACHE := ${sharedMemName}.io.M_AXI_AWCACHE
            |io.M_AXI_AWPROT  := ${sharedMemName}.io.M_AXI_AWPROT
            |io.M_AXI_AWQOS   := ${sharedMemName}.io.M_AXI_AWQOS
            |io.M_AXI_AWUSER  := ${sharedMemName}.io.M_AXI_AWUSER
            |io.M_AXI_AWVALID := ${sharedMemName}.io.M_AXI_AWVALID
            |${sharedMemName}.io.M_AXI_AWREADY := io.M_AXI_AWREADY
            |
            |io.M_AXI_WDATA   := ${sharedMemName}.io.M_AXI_WDATA
            |io.M_AXI_WSTRB   := ${sharedMemName}.io.M_AXI_WSTRB
            |io.M_AXI_WLAST   := ${sharedMemName}.io.M_AXI_WLAST
            |io.M_AXI_WUSER   := ${sharedMemName}.io.M_AXI_WUSER
            |io.M_AXI_WVALID  := ${sharedMemName}.io.M_AXI_WVALID
            |${sharedMemName}.io.M_AXI_WREADY := io.M_AXI_WREADY
            |
            |${sharedMemName}.io.M_AXI_BID    := io.M_AXI_BID
            |${sharedMemName}.io.M_AXI_BRESP  := io.M_AXI_BRESP
            |${sharedMemName}.io.M_AXI_BUSER  := io.M_AXI_BUSER
            |${sharedMemName}.io.M_AXI_BVALID := io.M_AXI_BVALID
            |io.M_AXI_BREADY := ${sharedMemName}.io.M_AXI_BREADY
            |
            |io.M_AXI_ARID    := ${sharedMemName}.io.M_AXI_ARID
            |io.M_AXI_ARADDR  := ${sharedMemName}.io.M_AXI_ARADDR
            |io.M_AXI_ARLEN   := ${sharedMemName}.io.M_AXI_ARLEN
            |io.M_AXI_ARSIZE  := ${sharedMemName}.io.M_AXI_ARSIZE
            |io.M_AXI_ARBURST := ${sharedMemName}.io.M_AXI_ARBURST
            |io.M_AXI_ARLOCK  := ${sharedMemName}.io.M_AXI_ARLOCK
            |io.M_AXI_ARCACHE := ${sharedMemName}.io.M_AXI_ARCACHE
            |io.M_AXI_ARPROT  := ${sharedMemName}.io.M_AXI_ARPROT
            |io.M_AXI_ARQOS   := ${sharedMemName}.io.M_AXI_ARQOS
            |io.M_AXI_ARUSER  := ${sharedMemName}.io.M_AXI_ARUSER
            |io.M_AXI_ARVALID := ${sharedMemName}.io.M_AXI_ARVALID
            |${sharedMemName}.io.M_AXI_ARREADY := io.M_AXI_ARREADY
            |
            |${sharedMemName}.io.M_AXI_RID    := io.M_AXI_RID
            |${sharedMemName}.io.M_AXI_RDATA  := io.M_AXI_RDATA
            |${sharedMemName}.io.M_AXI_RRESP  := io.M_AXI_RRESP
            |${sharedMemName}.io.M_AXI_RLAST  := io.M_AXI_RLAST
            |${sharedMemName}.io.M_AXI_RUSER  := io.M_AXI_RUSER
            |${sharedMemName}.io.M_AXI_RVALID := io.M_AXI_RVALID
            |io.M_AXI_RREADY := ${sharedMemName}.io.M_AXI_RREADY
          """

      return st"""
                 |import chisel3._
                 |import chisel3.util._
                 |import chisel3.experimental._
                 |
                 |${if(!anvil.config.useIP && anvil.config.cpMax > 0) findChiselModule(LabelToFsmIP()).get.moduleST else st""}
                 |
                 |import ${name}._
                 |class ${name} (val C_S_AXI_DATA_WIDTH: Int = ${if(anvil.config.genVerilog && (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4)) 64 else 32},
                 |               val C_S_AXI_ADDR_WIDTH: Int = ${if(anvil.config.genVerilog && (anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4)) 8 else log2Up(anvil.config.memory)},
                 |               val C_M_AXI_ADDR_WIDTH: Int = 32,
                 |               val C_M_AXI_DATA_WIDTH: Int = 64,
                 |               val C_M_TARGET_SLAVE_BASE_ADDR: BigInt = BigInt("00000000", 16),
                 |               val MEMORY_DEPTH: Int = ${anvil.config.memory},
                 |               val ARRAY_REG_WIDTH:    Int = 8,
                 |               val ARRAY_REG_DEPTH:    Int = ${anvil.config.memory},
                 |               ${if (!anvil.config.splitTempSizes) "val GENERAL_REG_WIDTH:   Int = 64," else ""}
                 |               ${if (!anvil.config.splitTempSizes) s"val GENERAL_REG_DEPTH:   Int = ${maxRegisters.maxCount}," else ""}
                 |               val STACK_POINTER_WIDTH: Int = ${anvil.spTypeByteSize * 8},
                 |               val CODE_POINTER_WIDTH:  Int = ${anvil.cpTypeByteSize * 8}) extends Module {
                 |
                 |  val io = IO(new Bundle{
                 |    // write address channel
                 |    val S_AXI_AWADDR  = Input(UInt(C_S_AXI_ADDR_WIDTH.W))
                 |    val S_AXI_AWPROT  = Input(UInt(3.W))
                 |    val S_AXI_AWVALID = Input(Bool())
                 |    val S_AXI_AWREADY = Output(Bool())
                 |
                 |    // write data channel
                 |    val S_AXI_WDATA  = Input(UInt(C_S_AXI_DATA_WIDTH.W))
                 |    val S_AXI_WSTRB  = Input(UInt((C_S_AXI_DATA_WIDTH/8).W))
                 |    val S_AXI_WVALID = Input(Bool())
                 |    val S_AXI_WREADY = Output(Bool())
                 |
                 |    // write response channel
                 |    val S_AXI_BRESP  = Output(UInt(2.W))
                 |    val S_AXI_BVALID = Output(Bool())
                 |    val S_AXI_BREADY = Input(Bool())
                 |
                 |    // read address channel
                 |    val S_AXI_ARADDR  = Input(UInt(C_S_AXI_ADDR_WIDTH.W))
                 |    val S_AXI_ARPROT  = Input(UInt(3.W))
                 |    val S_AXI_ARVALID = Input(Bool())
                 |    val S_AXI_ARREADY = Output(Bool())
                 |
                 |    // read data channel
                 |    val S_AXI_RDATA  = Output(UInt(C_S_AXI_DATA_WIDTH.W))
                 |    val S_AXI_RRESP  = Output(UInt(2.W))
                 |    val S_AXI_RVALID = Output(Bool())
                 |    val S_AXI_RREADY = Input(Bool())
                 |
                 |    ${if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4) axi4FullMasterST else st""}
                 |  })
                 |
                 |  ${if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Default) s"val ${sharedMemName} = RegInit(VecInit(Seq.fill(ARRAY_REG_DEPTH)(0.U(ARRAY_REG_WIDTH.W))))" else ""}
                 |  // reg for general purpose
                 |  ${if (!anvil.config.splitTempSizes) s"val ${generalRegName} = RegInit(VecInit(Seq.fill(GENERAL_REG_DEPTH)(0.U(GENERAL_REG_WIDTH.W))))" else s"${generalPurposeRegisterST.render}"}
                 |  // reg for code pointer
                 |  ${cpST(name)}
                 |  // reg for stack pointer
                 |  val SP = RegInit(0.U(STACK_POINTER_WIDTH.W))
                 |  // reg for display pointer
                 |  val DP = RegInit(0.U(64.W))
                 |  // reg for index in memcopy
                 |  val Idx = RegInit(0.U(16.W))
                 |  // reg for recording how many rounds needed for the left bytes
                 |  val LeftByteRounds = RegInit(0.U(8.W))
                 |  val IdxLeftByteRounds = RegInit(0.U(8.W))
                 |  ${if(anvil.config.useIP) "val indexerValid = RegInit(false.B)" else ""}
                 |
                 |  // registers for valid and ready
                 |  val r_valid = RegInit(false.B)
                 |  val r_ready = RegInit(0.U(2.W))
                 |
                 |  ${if(anvil.config.useIP) instanceDeclST else st""}
                 |  ${if(anvil.config.cpMax > 0) insDeclST(LabelToFsmIP(), 1) else st""}
                 |  ${if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4) axi4FullMasterConnectionST else st""}
                 |
                 |  init(this)
                 |
                 |  ${axi4LiteInterfaceST}
                 |
                 |}
                 |
                 |${(stateMachineST, "")}
                 |object ${name} {
                 |  def init(o: ${name}): Unit = {
                 |    import o._
                 |    ${if(anvil.config.useIP) instancePortFuncST else st""}
                 |    ${if(anvil.config.useIP) instancePortCallST else st""}
                 |  }
                 |}
                 |${(stateFunctionObjectST, "\n")}
          """

    }

    @pure def procedureST(stateMachineST: ST, stateFunctionObjectST: ST): ST = {
      //println(stateMachineST.render)
      println(stateFunctionObjectST.render)

      return st"""
                 |import chisel3._
                 |import chisel3.util._
                 |import chisel3.experimental._
                 |
                 |${if(!anvil.config.useIP && anvil.config.cpMax > 0) findChiselModule(LabelToFsmIP()).get.moduleST else st""}
                 |
                 |import ${name}._
                 |class ${name} (addrWidth: Int, dataWidth: Int, cpWidth: Int, idWidth: Int, depth: Int) extends Module {
                 |
                 |  val io = IO(new Bundle{
                 |    val routeIn     = Flipped(Valid(new Packet(idWidth, cpWidth)))
                 |    val routeOut    = Valid(new Packet(idWidth, cpWidth))
                 |  })
                 |
                 |  ${globalTempST}
                 |  ${cpST(name)}
                 |  // reg for recording how many rounds needed for the left bytes
                 |  val LeftByteRounds = RegInit(0.U(8.W))
                 |  val IdxLeftByteRounds = RegInit(0.U(8.W))
                 |  ${if (anvil.config.useIP) "val indexerValid = RegInit(false.B)" else ""}
                 |
                 |  val r_srcID      = RegInit(2.U(idWidth.W))
                 |  val r_srcCP      = RegInit(0.U(cpWidth.W))
                 |  val r_srcResAddr = Reg(UInt(addrWidth.W))
                 |  val r_res        = Reg(UInt(dataWidth.W))
                 |
                 |  val r_routeIn        = RegInit(0.U.asTypeOf(new Packet(idWidth, cpWidth)))
                 |  val r_routeIn_valid  = RegInit(false.B)
                 |  val r_routeOut       = Reg(new Packet(idWidth, cpWidth))
                 |  val r_routeOut_valid = RegInit(false.B)
                 |
                 |  r_routeIn         := io.routeIn.bits
                 |  r_routeIn_valid   := io.routeIn.valid
                 |  io.routeOut.bits  := r_routeOut
                 |  io.routeOut.valid := r_routeOut_valid
                 |
                 |${(stateMachineST, "")}
                 |
                 |}
                 |${(stateFunctionObjectST, "\n")}
               """
    }

    val basicBlockST = processBasicBlock(name, o.body.asInstanceOf[AST.IR.Body.Basic].blocks, hwLog)

    return procedureST(basicBlockST._1, basicBlockST._2)
  }

  @pure def processBasicBlock(name: String, bs: ISZ[AST.IR.BasicBlock], hwLog: HwSynthesizer2.HwLog): (ST, ST) = {
    for(b <- bs) {
      if(b.label > hwLog.maxNumLabel) {
        hwLog.maxNumLabel = b.label
      }
    }

    val ipPortLogic = HwSynthesizer2.IpPortAssign(anvil, ipAlloc, ISZ[ST](), ipModules, InputMap.empty, ISZ[ST](), ISZ[ST]())
    @pure def basicBlockST(grounds: HashSMap[Z, ST], functions: ISZ[ST]): (ST, ST) = {
      var stateSTs: ISZ[ST] = ISZ[ST]()
      stateSTs = stateSTs :+
        st"""
            |is(0.U) {
            |  r_routeOut_valid := false.B
            |  when(r_routeIn_valid) {
            |      r_srcCP := r_routeIn.srcCP
            |      r_srcID := r_routeIn.srcID
            |      ${name}CP  := r_routeIn.dstCP
            |  }
            |}
          """
      for(pair <- grounds.entries) {
        stateSTs = stateSTs :+ pair._2
      }

      var fmsSTs: ISZ[ST] = ISZ[ST]()

      var objectStateMachineST: ISZ[ISZ[ST]] = ISZ[ISZ[ST]]()
      objectStateMachineST = objectStateMachineST :+ ISZ[ST]()
      for(i <- 0 until(stateSTs.size)) {
        val idxStateMachine = i / 1024
        if(idxStateMachine >= objectStateMachineST.size) {
          objectStateMachineST = objectStateMachineST :+ ISZ[ST]()
        }

        val updatedST = objectStateMachineST(idxStateMachine) :+ stateSTs(i)
        objectStateMachineST = objectStateMachineST(idxStateMachine ~> updatedST)
      }

      for(j <- 0 until(objectStateMachineST.size)) {
        fmsSTs = fmsSTs :+
          st"""
              |object StateMachine_0_${j} {
              |  def stateMachine_0_${j}(o:${name}): Unit = {
              |    import o._
              |    switch(${name}CP) {
              |      ${(objectStateMachineST(j), "\n")}
              |    }
              |  }
              |}
            """
      }

      return (
        st"""${(fmsSTs, "\n")}""",
        st"""${(functions, "")}"""
      )
    }

    @pure def groundST(b: AST.IR.BasicBlock, ground: ST, jump: ST): (ST, ST) = {
      var commentST = ISZ[ST]()

      for(g <- b.grounds) {
        commentST = commentST :+ g.prettyST(anvil.printer)
      }
      commentST = commentST :+ b.jump.prettyST(anvil.printer)

      val jumpST: ST = {
        if(hwLog.isIndexerInCurrentBlock() && !hwLog.isMemCpyInCurrentBlock()) {
          val jST = processJumpIntrinsic(name, hwLog.stateBlock.get, ipPortLogic, hwLog)
          val indexerName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get
          st"""
              |when(${indexerName}_${hwLog.activeIndexerIndex}.io.valid) {
              |  ${jST.render}
              |  ${indexerName}_${hwLog.activeIndexerIndex}.io.ready := false.B
              |}
            """
        }
        else if(!hwLog.isMemCpyInCurrentBlock()) {
          jump
        } else {
          st""
        }
      }

      if(b.label > 1) {
        val functionDefinitionST: ST =
          st"""
              |object Block_${b.label} {
              |  def block_${b.label}(o: ${name}): Unit = {
              |    import o._
              |    /*
              |    ${(commentST, "\n")}
              |    */
              |    ${(ground, "")}
              |    ${jumpST}
              |  }
              |}
              """
        val functionCallST: ST = {
          if(anvil.config.cpMax <= 0)
            st"""
                |is(${b.label}.U) {
                |  Block_${b.label}.block_${b.label}(o)
                |}
                """
          else
            st"""
                |is(${b.label % (anvil.config.cpMax)}.U) {
                |  Block_${b.label}.block_${b.label}(o)
                |}
              """
        }
        return (functionCallST, functionDefinitionST)
      } else {
        return (st"", st"")
      }
    }

    var allGroundsST: HashSMap[Z, ST] = HashSMap.empty[Z, ST]
    var allFunctionsST = ISZ[ST]()

    for (b <- bs) {
      hwLog.stateBlock = MSome(b)
      hwLog.currentLabel = b.label

      if(b.label != 0) {
        val processedGroundST = processGround(name, b.grounds, ipPortLogic, hwLog)
        var jump = processJumpIntrinsic(name, b, ipPortLogic, hwLog)
        if(ipPortLogic.whenCondST.nonEmpty) {
          jump =
            st"""
                |when(${(ipPortLogic.whenCondST, " & ")}) {
                |  ${(ipPortLogic.whenStmtST, "\n")}
                |  ${jump}
                |}
              """
        }
        val g = groundST(b, processedGroundST, jump)
        ipPortLogic.whenCondST = ISZ[ST]()
        ipPortLogic.whenStmtST = ISZ[ST]()

        allGroundsST = allGroundsST + b.label ~> g._1
        allFunctionsST = allFunctionsST :+ g._2
      }

      hwLog.indexerInCurrentBlock = F
      hwLog.memCpyInCurrentBlock = F

    }

    return basicBlockST(allGroundsST, allFunctionsST)
  }

  @pure def processGround(name: String, gs: ISZ[AST.IR.Stmt.Ground], ipPortLogic: HwSynthesizer2.IpPortAssign, hwLog: HwSynthesizer2.HwLog): ST = {
    var groundST = ISZ[ST]()

    for(g <- gs) {
      g match {
        case g: AST.IR.Stmt.Assign => {
          groundST = groundST :+ processStmtAssign(g, ipPortLogic, hwLog)
        }
        case g: AST.IR.Stmt.Intrinsic => {
          groundST = groundST :+ processStmtIntrinsic(name, g, ipPortLogic, hwLog)
        }
        case _ => {
          halt(s"processGround unimplemented")
        }
      }

      ipPortLogic.transform_langastIRStmtGround(g)
      groundST = groundST ++ ipPortLogic.sts

      ipPortLogic.sts = ISZ[ST]()
      ipPortLogic.inputMap = InputMap.empty
    }

    return st"""${(groundST, "\n")}"""
  }

  @pure def processJumpIntrinsic(name: String, b: AST.IR.BasicBlock, ipPortLogic: HwSynthesizer2.IpPortAssign, hwLog: HwSynthesizer2.HwLog): ST = {
    var intrinsicST: ISZ[ST] = ISZ[ST]()
    val j = b.jump

    @pure def jumpSplitCpST(label: Z): ST = {
      var sts: ISZ[ST] = ISZ[ST]()
      val curCpIdx = getCpIndex(hwLog.currentLabel)._1
      val (nextCpIdx, nextPosIdx) = getCpIndex(label)
      if(curCpIdx == nextCpIdx) {
        sts = sts :+ st"${name}CP(${curCpIdx}.U) := ${nextPosIdx}.U"
      } else {
        sts = sts :+
          st"""
              |broadcastBuffer.io.in(${curCpIdx}.U).valid      := true.B
              |broadcastBuffer.io.in(${curCpIdx}.U).bits.index := ${nextCpIdx}.U
              |broadcastBuffer.io.in(${curCpIdx}.U).bits.state := ${nextPosIdx}.U
            """
        sts = sts :+ st"${name}CP(${curCpIdx}.U) := ${anvil.config.cpMax}.U"
      }

      return st"${(sts, "\n")}"
    }

    j match {
      case AST.IR.Jump.Intrinsic(intrinsic: Intrinsic.GotoLocal) => {
        val targetAddrST: ST = processExpr(AST.IR.Exp.Temp(intrinsic.loc, anvil.cpType, intrinsic.pos), F, ipPortLogic, hwLog)
        if (intrinsic.isTemp) {
          if(anvil.config.cpMax <= 0) {
            intrinsicST = intrinsicST :+ st"${name}CP := ${targetAddrST}"
          } else {
            var portSTs: ISZ[ST] = ISZ[ST]()
            val instanceName: String = getIpInstanceName(LabelToFsmIP()).get
            portSTs = portSTs :+ st"${instanceName}.io.label := ${targetAddrST}"
            portSTs = portSTs :+ st"${instanceName}.io.start := Mux(${instanceName}.io.valid, false.B, true.B)"
            portSTs = portSTs :+ st"${instanceName}.io.originalCpIndex := ${getCpIndex(hwLog.currentLabel)._1}.U"
            portSTs = portSTs :+
              st"""
                  |when(${instanceName}.io.valid) {
                  |  when(${instanceName}.io.isSameCpIndex) {
                  |    ${name}CP(${instanceName}.io.cpIndex) := ${instanceName}.io.stateIndex
                  |  } .otherwise {
                  |    broadcastBuffer.io.in(${getCpIndex(hwLog.currentLabel)._1}).valid      := true.B
                  |    broadcastBuffer.io.in(${getCpIndex(hwLog.currentLabel)._1}).bits.index := ${instanceName}.io.cpIndex
                  |    broadcastBuffer.io.in(${getCpIndex(hwLog.currentLabel)._1}).bits.state := ${instanceName}.io.stateIndex
                  |    ${name}CP(${getCpIndex(hwLog.currentLabel)._1}.U) := ${anvil.config.cpMax}.U
                  |  }
                  |}
                """
            intrinsicST = intrinsicST :+ st"${(portSTs, "\n")}"
          }
        } else {
          var returnAddrST = ISZ[ST]()
          val offsetST: ST = if (intrinsic.loc < 0) st"- ${-intrinsic.loc}" else st"+ ${intrinsic.loc}"

          for (i <- (anvil.cpTypeByteSize - 1) to 0 by -1) {
            if (i == 0) {
              returnAddrST = returnAddrST :+ st"${sharedMemName}(SP ${offsetST.render}.U + ${i}.U)"
            } else {
              returnAddrST = returnAddrST :+ st"${sharedMemName}(SP ${offsetST.render}.U + ${i}.U),"
            }
          }

          intrinsicST = intrinsicST :+
            st"""
                |${name}CP := Cat(
                |  ${(returnAddrST, "\n")}
                |)
            """
        }
      }
      case AST.IR.Jump.Intrinsic(intrinsic: Intrinsic.GotoGlobal) => {
        if(anvil.config.cpMax <= 0) {
          intrinsicST = intrinsicST :+
            st"""
                |${name}CP := ${globalName(intrinsic.name)}
              """
        } else {
          var portSTs: ISZ[ST] = ISZ[ST]()
          val instanceName: String = getIpInstanceName(LabelToFsmIP()).get
          portSTs = portSTs :+ st"${instanceName}.io.label := ${globalName(intrinsic.name)}"
          portSTs = portSTs :+ st"${instanceName}.io.start := Mux(${instanceName}.io.valid, false.B, true.B)"
          portSTs = portSTs :+ st"${instanceName}.io.originalCpIndex := ${getCpIndex(hwLog.currentLabel)._1}.U"
          portSTs = portSTs :+
            st"""
                |when(${instanceName}.io.valid) {
                |  when(${instanceName}.io.isSameCpIndex) {
                |    ${name}CP(${instanceName}.io.cpIndex) := ${instanceName}.io.stateIndex
                |  } .otherwise {
                |    broadcastBuffer.io.in(${getCpIndex(hwLog.currentLabel)._1}).valid      := true.B
                |    broadcastBuffer.io.in(${getCpIndex(hwLog.currentLabel)._1}).bits.index := ${instanceName}.io.cpIndex
                |    broadcastBuffer.io.in(${getCpIndex(hwLog.currentLabel)._1}).bits.state := ${instanceName}.io.stateIndex
                |    ${name}CP(${getCpIndex(hwLog.currentLabel)._1}.U) := ${anvil.config.cpMax}.U
                |  }
                |}
                """
          intrinsicST = intrinsicST :+ st"${(portSTs, "\n")}"
        }
      }
      case j: AST.IR.Jump.Goto => {
        if(anvil.config.cpMax <= 0) {
          intrinsicST = intrinsicST :+ st"${name}CP := ${j.label}.U"
        } else {
          intrinsicST = intrinsicST :+ jumpSplitCpST(j.label)
        }
      }
      case j: AST.IR.Jump.If => {
        val cond = processExpr(j.cond, F, ipPortLogic, hwLog)
        if(anvil.config.cpMax <= 0) {
          intrinsicST = intrinsicST :+ st"${name}CP := Mux((${cond.render}.asUInt) === 1.U, ${j.thenLabel}.U, ${j.elseLabel}.U)"
        } else {
          val thenST: ST = jumpSplitCpST(j.thenLabel)
          val elseST: ST = jumpSplitCpST(j.elseLabel)

          val finalST: ST =
            st"""
                |when((${cond.render}.asUInt) === 1.U){
                |  ${thenST}
                |} .otherwise {
                |  ${elseST}
                |}
              """

          intrinsicST = intrinsicST :+ finalST
        }
      }
      case j: AST.IR.Jump.Switch => {
        val condExprST = processExpr(j.exp, F, ipPortLogic, hwLog)

        val tmpWire = st"__tmp_${hwLog.tmpWireCount}"
        hwLog.tmpWireCount = hwLog.tmpWireCount + 1

        val defaultStatementST: ST = j.defaultLabelOpt match {
          case Some(x) => if(anvil.config.cpMax <= 0) st"${name}CP := ${x}.U" else jumpSplitCpST(x)
          case None() => st""
        }

        var isStatementST = ISZ[ST]()
        for(i <- j.cases) {
          isStatementST = isStatementST :+
            st"""
                |is(${processExpr(i.value, F, ipPortLogic, hwLog).render}) {
                |  ${if(anvil.config.cpMax <=0) st"${name}CP := ${i.label}.U" else jumpSplitCpST(i.label)}
                |}
              """
        }

        intrinsicST = intrinsicST :+
          st"""
              |val ${tmpWire.render} = ${condExprST.render}
              |${defaultStatementST.render}
              |switch(${tmpWire.render}) {
              |  ${(isStatementST, "\n")}
              |}
            """
      }
      case j: AST.IR.Jump.Return => {
      }
      case _ => {
        halt(s"processJumpIntrinsic unimplemented")
      }
    }

    ipPortLogic.transform_langastIRJump(j)
    intrinsicST = intrinsicST ++ ipPortLogic.sts

    ipPortLogic.sts = ISZ[ST]()
    //ipPortLogic.inputMap = InputMap.empty

    return st"""${(intrinsicST, "\n")}"""
  }

  @strictpure def isIntExp(exp: AST.IR.Exp): B = exp match {
    case exp: AST.IR.Exp.Int => T
    case _ => F
  }

  @strictpure def isBoolExp(exp: AST.IR.Exp): B = exp match {
    case exp: AST.IR.Exp.Bool => T
    case _ => F
  }

  @pure def getGeneralRegName(tipe: AST.Typed): String = {
    val t: AST.Typed = if(anvil.isScalar(tipe)) tipe else anvil.spType
    return s"${generalRegName}${if(anvil.isSigned(t)) "S" else "U"}${anvil.typeBitSize(t)}"
  }

  @pure def log2Up(x: Z): Z = {
    if (x <= 1) {
      return 0
    }

    var result: Z = 0
    var value: Z = x - 1

    while (value > 0) {
      value = value / 2
      result = result + 1
    }

    return result
  }

  @pure def processStmtIntrinsic(name: String, i: AST.IR.Stmt.Intrinsic, ipPortLogic: HwSynthesizer2.IpPortAssign, hwLog: HwSynthesizer2.HwLog): ST = {
    var intrinsicST = st""

    i match {
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.AlignRw) => {
        val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
        ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}.io.mode := 0.U"

        if(intrinsic.isRead) {
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.readValid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${globalName(Util.readAlignRes)} := ${indexerInstanceName}.io.readData"
          intrinsicST =
            st"""
                |${indexerInstanceName}.io.mode := 1.U
                |${indexerInstanceName}.io.readAddr := ${globalName(Util.readAlignAddr)}
              """
        } else {
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.writeValid"
          intrinsicST =
            st"""
                |${indexerInstanceName}.io.mode := 2.U
                |${indexerInstanceName}.io.writeAddr := ${globalName(Util.writeAlignAddr)}
                |${indexerInstanceName}.io.writeData := ${globalName(Util.writeAlignValue)}
              """
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.TempLoad) => {
        if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          val readAddrST: ST = processExpr(intrinsic.base, F, ipPortLogic, hwLog)
          val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
          val tempST: ST = st"${if (!anvil.config.splitTempSizes) s"${generalRegName}(${intrinsic.temp}.U)" else s"${getGeneralRegName(intrinsic.tipe)}(${intrinsic.temp}.U)"}"
          val byteST: ST = st"(${intrinsic.bytes * 8 - 1}, 0)"
          val signedST: ST = if(intrinsic.isSigned && anvil.config.splitTempSizes) st".asSInt" else st""
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val readOffsetST: ST = if(intrinsic.offset < 0) st"(${intrinsic.offset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.offset}.U"
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.readValid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${tempST.render} := ${indexerInstanceName}.io.readData${byteST.render}${signedST.render}"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}.io.mode := 0.U"
          intrinsicST =
            st"""
                |${indexerInstanceName}.io.mode := 1.U
                |${indexerInstanceName}.io.readAddr := ${readAddrST.render}
                |${indexerInstanceName}.io.readOffset := ${readOffsetST.render}
                |${indexerInstanceName}.io.readLen := ${intrinsic.bytes}.U
              """
        } else {
          var internalST = ISZ[ST]()
          val rhsOffsetST = processExpr(intrinsic.rhsOffset, F, ipPortLogic, hwLog)
          val tmpWire = st"__tmp_${hwLog.tmpWireCount}"

          for (i <- (intrinsic.bytes - 1) to 0 by -1) {
            if (i == 0) {
              internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U)"
            } else {
              internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U),"
            }
          }

          val padST = st".asSInt.pad(${if (!anvil.config.splitTempSizes) "GENERAL_REG_WIDTH" else s"${anvil.typeBitSize(intrinsic.tipe)}"})"
          val placeholder: String = if (hwLog.isIndexerInCurrentBlock()) "  " else ""
          val indexerInstanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get

          intrinsicST =
            st"""
                |val ${tmpWire} = (${rhsOffsetST.render}).asUInt
                |${if (hwLog.isIndexerInCurrentBlock()) s"when(${indexerInstanceName}_${hwLog.activeIndexerIndex}.io.valid){" else ""}
                |${placeholder}${if (!anvil.config.splitTempSizes) s"${generalRegName}(${intrinsic.temp}.U)" else s"${getGeneralRegName(intrinsic.tipe)}(${intrinsic.temp}.U)"} := Cat(
                |  ${placeholder}${(internalST, "\n")}
                |)${placeholder}${if (intrinsic.isSigned) s"${padST.render}" else ""}${if (!anvil.config.splitTempSizes) ".asUInt" else ""}
                |${if (hwLog.isIndexerInCurrentBlock()) "}" else ""}
            """
          hwLog.tmpWireCount = hwLog.tmpWireCount + 1
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Erase) => {
        if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val eraseBaseST: ST = processExpr(intrinsic.base, F, ipPortLogic, hwLog)
          val eraseOffsetST: ST = if(intrinsic.offset < 0) st"(${intrinsic.offset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.offset}.U"
          val eraseBytesST: ST = st"${intrinsic.bytes}.U"
          val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.dmaValid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}.io.mode := 0.U"
          val ioDmaDstOffsetST: ST = st"${indexerInstanceName}.io.dmaDstOffset := ${eraseOffsetST.render}"
          intrinsicST =
            st"""
                |${indexerInstanceName}.io.mode := 3.U
                |${indexerInstanceName}.io.dmaSrcAddr := 0.U
                |${indexerInstanceName}.io.dmaDstAddr := ${eraseBaseST.render}
                |${indexerInstanceName}.io.dmaSrcLen := 0.U
                |${indexerInstanceName}.io.dmaDstLen := ${eraseBytesST.render}
                |${if(!anvil.config.alignAxi4) ioDmaDstOffsetST.render else ""}
              """
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Copy) => {
        if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val dmaDstAddrST: ST = processExpr(intrinsic.lbase, F, ipPortLogic, hwLog)
          val dmaDstOffsetST: ST = if(intrinsic.loffset < 0) st"(${intrinsic.loffset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.loffset}.U"
          val dmaSrcLenST: ST = processExpr(intrinsic.rhsBytes, F, ipPortLogic, hwLog)
          val dmaSrcAddrST: ST = processExpr(intrinsic.rhs, F, ipPortLogic, hwLog)
          val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.dmaValid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}.io.mode := 0.U"
          val ioDmaDstOffsetST: ST = st"${indexerInstanceName}.io.dmaDstOffset := ${dmaDstOffsetST.render}"
          intrinsicST =
            st"""
                |${indexerInstanceName}.io.mode := 3.U
                |${indexerInstanceName}.io.dmaSrcAddr := ${dmaSrcAddrST.render}
                |${indexerInstanceName}.io.dmaDstAddr := ${dmaDstAddrST.render}
                |${indexerInstanceName}.io.dmaSrcLen := ${dmaSrcLenST.render}
                |${indexerInstanceName}.io.dmaDstLen := ${intrinsic.lhsBytes}.U
                |${if(!anvil.config.alignAxi4) ioDmaDstOffsetST.render else ""}
              """
        } else {
          hwLog.memCpyInCurrentBlock = T

          // acquire the source and destination address
          val lhsAddrST = processExpr(intrinsic.lhsOffset, F, ipPortLogic, hwLog)
          val rhsAddrST = processExpr(intrinsic.rhs, F, ipPortLogic, hwLog)

          val tmpWireLhsST = st"__tmp_${hwLog.tmpWireCount}"
          hwLog.tmpWireCount = hwLog.tmpWireCount + 1
          val tmpWireRhsST = st"__tmp_${hwLog.tmpWireCount}"
          hwLog.tmpWireCount = hwLog.tmpWireCount + 1
          val totalSizeWireST = st"__tmp_${hwLog.tmpWireCount}"
          hwLog.tmpWireCount = hwLog.tmpWireCount + 1
          val leftByteStartST = st"__tmp_${hwLog.tmpWireCount}"
          hwLog.tmpWireCount = hwLog.tmpWireCount + 1

          // compute how many bytes needed for memory copy transfer
          val rhsBytesSt = processExpr(intrinsic.rhsBytes, F, ipPortLogic, hwLog)
          var BytesTransferST = ISZ[ST]()
          for (i <- 0 to (anvil.config.copySize - 1)) {
            BytesTransferST = BytesTransferST :+ st"${sharedMemName}(${tmpWireLhsST.render} + Idx + ${i}.U) := ${sharedMemName}(${tmpWireRhsST.render} + Idx + ${i}.U)"
          }

          // get the jump statement ST
          val jumpST = processJumpIntrinsic(name, hwLog.stateBlock.get, ipPortLogic, hwLog)
          val indexerInstanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get
          val indexerReadyDisableStr: String = if (hwLog.isIndexerInCurrentBlock()) s"${indexerInstanceName}_${hwLog.activeIndexerIndex}.io.ready := false.B" else ""
          val indexerValidStr: String = if (hwLog.isIndexerInCurrentBlock()) s"when(${indexerInstanceName}_${hwLog.activeIndexerIndex}.io.valid) {indexerValid := true.B; ${indexerReadyDisableStr}}" else ""
          val indexerConditionStr: String = if (hwLog.isIndexerInCurrentBlock()) "indexerValid & " else ""

          intrinsicST =
            st"""
                |val ${tmpWireLhsST.render} = ${lhsAddrST.render}
                |val ${tmpWireRhsST.render} = ${rhsAddrST.render}
                |val ${totalSizeWireST.render} = ${rhsBytesSt.render}
                |
                |${indexerValidStr}
                |when(${indexerConditionStr}Idx < ${totalSizeWireST.render}) {
                |  ${(BytesTransferST, "\n")}
                |  Idx := Idx + ${anvil.config.copySize}.U
                |  LeftByteRounds := ${totalSizeWireST.render} - Idx
                |} .elsewhen(${indexerConditionStr}IdxLeftByteRounds < LeftByteRounds) {
                |  val ${leftByteStartST.render} = Idx - ${anvil.config.copySize}.U
                |  ${sharedMemName}(${tmpWireLhsST.render} + ${leftByteStartST.render} + IdxLeftByteRounds) := ${sharedMemName}(${tmpWireRhsST.render} + ${leftByteStartST.render} + IdxLeftByteRounds)
                |  IdxLeftByteRounds := IdxLeftByteRounds + 1.U
                |} ${if (hwLog.isIndexerInCurrentBlock()) ".elsewhen(indexerValid) {" else ".otherwise {"}
                |  Idx := 0.U
                |  IdxLeftByteRounds := 0.U
                |  LeftByteRounds := 0.U
                |  ${jumpST.render}
                |  ${if (hwLog.isIndexerInCurrentBlock()) "indexerValid := false.B" else ""}
                |}
            """
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Store) => {
        @strictpure def isLhsOffsetIndexing(e: AST.IR.Exp): B = e match {
          case AST.IR.Exp.Intrinsic(in: Intrinsic.Indexing) => T
          case _ => F
        }
        if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val writeAddrST: ST = processExpr(intrinsic.base, F, ipPortLogic, hwLog)
          val writeOffsetST: ST = if(intrinsic.offset < 0) st"(${intrinsic.offset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.offset}.U"
          val writeLenST: ST = st"${intrinsic.bytes}.U"
          val writeDataST: ST = processExpr(intrinsic.rhs, F, ipPortLogic, hwLog)
          val signedST: ST = if(intrinsic.isSigned) st".asUInt" else st""
          val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.writeValid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}.io.mode := 0.U"
          intrinsicST =
            st"""
                |${indexerInstanceName}.io.mode := 2.U
                |${indexerInstanceName}.io.writeAddr := ${writeAddrST.render}
                |${indexerInstanceName}.io.writeOffset := ${writeOffsetST.render}
                |${indexerInstanceName}.io.writeLen := ${writeLenST.render}
                |${indexerInstanceName}.io.writeData := ${writeDataST.render}${signedST.render}
              """
        } else {
          val lhsOffsetST = processExpr(intrinsic.lhsOffset, F, ipPortLogic, hwLog)
          val rhsST = processExpr(intrinsic.rhs, intrinsic.isSigned, ipPortLogic, hwLog)
          var shareMemAssign = ISZ[ST]()
          val tmpWireLhsST = st"__tmp_${hwLog.tmpWireCount}"
          hwLog.tmpWireCount = hwLog.tmpWireCount + 1
          val tmpWireRhsST = st"__tmp_${hwLog.tmpWireCount}"
          hwLog.tmpWireCount = hwLog.tmpWireCount + 1
          val tmpWireRhsContent: ST = if (isIntExp(intrinsic.rhs)) {
            st"${rhsST}"
          } else {
            rhsST
          }

          if (isLhsOffsetIndexing(intrinsic.lhsOffset)) {
            val indexerInstanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get
            shareMemAssign = shareMemAssign :+
              st"when(${indexerInstanceName}_${hwLog.activeIndexerIndex}.io.valid){"
          }

          for (i <- 0 to (intrinsic.bytes - 1) by 1) {
            shareMemAssign = shareMemAssign :+
              st"${if (isLhsOffsetIndexing(intrinsic.lhsOffset)) "  " else ""}${sharedMemName}(${tmpWireLhsST} + ${i}.U) := ${tmpWireRhsST}(${(i) * 8 + 7}, ${(i) * 8})"
          }

          if (isLhsOffsetIndexing(intrinsic.lhsOffset)) {
            shareMemAssign = shareMemAssign :+
              st"}"
          }

          val storeDataST = st"${if (anvil.typeBitSize(intrinsic.rhs.tipe) < (intrinsic.bytes * 8)) s".pad(${intrinsic.bytes * 8})" else ""}"

          intrinsicST =
            st"""
                |val ${tmpWireLhsST} = ${lhsOffsetST.render}
                |val ${tmpWireRhsST} = (${tmpWireRhsContent.render}${if (!anvil.config.splitTempSizes) "" else storeDataST.render}).asUInt
                |${(shareMemAssign, "\n")}
            """
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.RegisterAssign) => {
        val targetReg: String = if(intrinsic.isSP) "SP" else "DP"
        if(anvil.config.useIP) {
          var leftST: ST = st""
          var rightST: ST = st""
          var isPlus: B = F
          val regValueST: ST = processExpr(intrinsic.value, F, ipPortLogic, hwLog)
          intrinsic.value match {
            case AST.IR.Exp.Int(_, v, _) => {
              if (v < 0) {
                leftST = st"${targetReg}"
                isPlus = F
                rightST = st"${-v}.U"
              }
              else {
                leftST = st"${targetReg}"
                isPlus = T
                rightST = st"${v}.U"
              }
            }
            case _ => {
              if (intrinsic.isInc) {
                leftST = st"${targetReg}"
                isPlus = T
                rightST = regValueST
              }
            }
          }

          if(intrinsic.isInc) {
            val ipT: IpType = if(isPlus) BinaryIP(AST.IR.Exp.Binary.Op.Add, F) else BinaryIP(AST.IR.Exp.Binary.Op.Sub, F)
            val allocIndex: Z = getIpAllocIndex(intrinsic.value)
            var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
            val indexerInstanceName: String = getIpInstanceName(ipT).get
            hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt") +
              "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
            insertIPInput(ipT, populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
            ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
            intrinsicST =
              st"""
                  |${targetReg} := ${indexerInstanceName}_${allocIndex}.io.out"""
          } else {
            intrinsicST =
              st"""
                  |${targetReg} := ${regValueST}"""
          }
        }
        else {
          val updateContentST: ST = intrinsic.value match {
            case AST.IR.Exp.Int(_, v, _) => if (intrinsic.isInc) if (v < 0) st"${targetReg} - ${-v}.U" else st"${targetReg} + ${v}.U" else st"${processExpr(intrinsic.value, F, ipPortLogic, hwLog)}"
            case _ => if (intrinsic.isInc) st"${targetReg} + ${processExpr(intrinsic.value, F, ipPortLogic, hwLog)}" else st"${processExpr(intrinsic.value, F, ipPortLogic, hwLog)}"
          }

          intrinsicST =
            st"""
              |${targetReg} := ${updateContentST.render}"""
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Decl) => {

      }
    }

    return intrinsicST
  }

  @strictpure def isSignedExp(e: AST.IR.Exp): B =
    if(anvil.isScalar(e.tipe)) {
      if(anvil.isSigned(e.tipe)) T
      else F
    } else {
      anvil.isSigned(anvil.spType)
    }

  @pure def processStmtAssign(a: AST.IR.Stmt.Assign, ipPortLogic: HwSynthesizer2.IpPortAssign, hwLog: HwSynthesizer2.HwLog): ST = {
    var assignST: ST = st""

    @strictpure def isIntrinsicLoad(e: AST.IR.Exp): B = e match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => T
      case _ => F
    }

    @strictpure def getBaseOffsetOfIntrinsicLoad(e: AST.IR.Exp): Option[(AST.IR.Exp, Z)] = e match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => Some((intrinsic.base, intrinsic.offset))
      case _ => None()
    }

    a match {
      case a: AST.IR.Stmt.Assign.Global => {
        val lhsST: ST = globalName(a.name)
        val rhsST = processExpr(a.rhs, F, ipPortLogic, hwLog)
        if(isIntrinsicLoad(a.rhs)) {
          if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
            val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
            val readAddrST: ST = processExpr(getBaseOffsetOfIntrinsicLoad(a.rhs).get._1, F, ipPortLogic, hwLog)
            val offsetWidth: Z = log2Up(anvil.config.memory * 8)
            val intrinsicOffset: Z = getBaseOffsetOfIntrinsicLoad(a.rhs).get._2
            val readOffsetST: ST = if(intrinsicOffset < 0) st"(${intrinsicOffset}).S(${offsetWidth}.W).asUInt" else st"${intrinsicOffset}.U"
            ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${lhsST.render} := ${rhsST.render}"
            assignST =
              st"""
                  |${indexerInstanceName}.io.mode := 1.U
                  |${indexerInstanceName}.io.readAddr := ${readAddrST.render}
                  |${indexerInstanceName}.io.readOffset := ${readOffsetST.render}
                  |${indexerInstanceName}.io.readLen := ${anvil.typeByteSize(a.rhs.tipe)}.U
                """
          } else {
            assignST =
              st"""
                  |${lhsST} := Cat{
                  |  ${rhsST.render}
                  |}
                """
          }
        } else {
          val lhsContentST: ST = st"${if(isSignedExp(a.rhs)) "(" else ""}${rhsST.render}${if(isSignedExp(a.rhs)) ").asUInt" else ""}"
          val finalST = st"${lhsST} := ${if(!anvil.config.splitTempSizes) lhsContentST.render else s"${rhsST.render}"}"

          assignST =
            st"""
                |${finalST.render}
              """
        }
      }
      case a: AST.IR.Stmt.Assign.Temp => {
        val regNo = a.lhs
        val lhsST: ST = if(!anvil.config.splitTempSizes)  st"${generalRegName}(${regNo}.U)" else st"${getGeneralRegName(a.rhs.tipe)}(${regNo}.U)"
        val rhsST = processExpr(a.rhs, F, ipPortLogic, hwLog)
        if(isIntrinsicLoad(a.rhs)) {
          if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
            val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
            val readAddrST: ST = processExpr(getBaseOffsetOfIntrinsicLoad(a.rhs).get._1, F, ipPortLogic, hwLog)
            val offsetWidth: Z = log2Up(anvil.config.memory * 8)
            val intrinsicOffset: Z = getBaseOffsetOfIntrinsicLoad(a.rhs).get._2
            val readOffsetST: ST = if(intrinsicOffset < 0) st"(${intrinsicOffset}).S(${offsetWidth}.W).asUInt" else st"${intrinsicOffset}.U"
            ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${lhsST.render} := ${rhsST.render}"
            assignST =
              st"""
                  |${indexerInstanceName}.io.mode := 1.U
                  |${indexerInstanceName}.io.readAddr := ${readAddrST.render}
                  |${indexerInstanceName}.io.readOffset := ${readOffsetST.render}
                  |${indexerInstanceName}.io.readLen := ${anvil.typeByteSize(a.rhs.tipe)}.U
                """
          } else {
            assignST =
              st"""
                  |${lhsST} := Cat{
                  |  ${rhsST.render}
                  |}
                """
          }
        } else {
          val lhsContentST: ST = st"${if(isSignedExp(a.rhs)) "(" else ""}${rhsST.render}${if(isSignedExp(a.rhs)) ").asUInt" else ""}"
          val finalST = st"${lhsST} := ${if(!anvil.config.splitTempSizes) lhsContentST.render else s"${rhsST.render}"}"

          assignST =
            st"""
                |${finalST.render}
              """
        }
      }
      case _ => {
        halt(s"processStmtAssign unimplemented")
      }
    }

    return assignST
  }

  @pure def getIpAllocIndex(e: AST.IR.Exp): Z = {
    val index: Z = ipAlloc.allocMap.get(Util.IpAlloc.Ext.exp(e)) match {
      case Some(n) => n
      case None() => halt(s"not found index in function getIpAllocIndex, exp is ${e.prettyST(anvil.printer)}")
    }
    return index
  }

  @strictpure def globalName(name: ISZ[String]): ST = st"global_${(name, "_")}"

  @pure def processExpr(exp: AST.IR.Exp, isForcedSign: B, ipPortLogic: HwSynthesizer2.IpPortAssign, hwLog: HwSynthesizer2.HwLog): ST = {
    var exprST = st""

    exp match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Register) => {
        exprST = if(intrinsic.isSP) st"SP" else st"DP"
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => {
        if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
          val byteST: ST = st"(${intrinsic.bytes * 8 - 1}, 0)"
          val signedST: ST = if(intrinsic.isSigned) st".asSInt" else st""
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.readValid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}.io.mode := 0.U"
          exprST = st"${indexerInstanceName}.io.readData${byteST.render}${signedST.render}"
        } else {
          var rhsExprST = ISZ[ST]()
          val rhsExpr = processExpr(intrinsic.rhsOffset, F, ipPortLogic, hwLog)
          for (i <- intrinsic.bytes - 1 to 0 by -1) {
            if (i == 0) {
              rhsExprST = rhsExprST :+ st"${sharedMemName}(${rhsExpr.render} + ${i}.U)"
            } else {
              rhsExprST = rhsExprST :+ st"${sharedMemName}(${rhsExpr.render} + ${i}.U),"
            }
          }
          exprST =
            st"""
                |Cat(
                |  ${(rhsExprST, "\n")}
                |)${if (intrinsic.isSigned) ".asSInt" else ""}"""
        }
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Indexing) => {
        hwLog.indexerInCurrentBlock = T
        val allocIndex = getIpAllocIndex(exp)
        hwLog.activeIndexerIndex = allocIndex

        val baseOffsetST: ST = processExpr(intrinsic.baseOffset, F, ipPortLogic, hwLog)
        val dataOffset: Z = intrinsic.dataOffset
        val indexST: ST = processExpr(intrinsic.index, F, ipPortLogic, hwLog)
        val mask: Z = intrinsic.maskOpt match {
          case Some(z) => z
          case None() => 0xFFFF
        }
        val elementSize: Z = intrinsic.elementSize

        var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
        hashSMap = hashSMap +
          "baseOffset" ~> (st"${baseOffsetST.render}", "UInt") +
          "dataOffset" ~> (st"${dataOffset}.U", "UInt") +
          "index" ~> (st"${indexST.render}", "UInt") +
          "elementSize" ~> (st"${elementSize}.U", "UInt") +
          "mask" ~> (st"${mask}.U", "UInt") +
          "ready" ~> (st"true.B", "Bool")

        insertIPInput(IntrinsicIP(defaultIndexing), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
        val indexerInstanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get

        exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
      }
      case exp: AST.IR.Exp.Temp => {
        val noSplitST: ST = st"${generalRegName}(${exp.n}.U)${if(isSignedExp(exp)) ".asSInt" else ""}"
        val splitST: ST = st"${getGeneralRegName(exp.tipe)}(${exp.n}.U)"
        exprST = if(!anvil.config.splitTempSizes) noSplitST else splitST
      }
      case exp: AST.IR.Exp.Bool => {
        exprST = exp.value match {
          case T => st"1.U"
          case F => st"0.U"
        }
      }
      case exp: AST.IR.Exp.Int => {
        val valuePostfix: String = isForcedSign match {
          case T => "S"
          case _ => if(anvil.isSigned(exp.tipe)) "S" else "U"
        }
        exprST = st"${if(exp.value > 2147483647 || exp.value < -2147483648) s"BigInt(\"${exp.value}\")" else s"${exp.value}"}.${valuePostfix}(${anvil.typeByteSize(exp.tipe)*8}.W)"
      }
      case exp: AST.IR.Exp.GlobalVarRef => {
        exprST = globalName(exp.name)
      }
      case exp: AST.IR.Exp.Type => {
        val splitStr: String = if(anvil.typeBitSize(exp.exp.tipe)== anvil.typeBitSize(exp.t)) "" else s".pad(${anvil.typeBitSize(exp.t)})"
        exprST = st"${processExpr(exp.exp, F, ipPortLogic, hwLog)}${if(anvil.isSigned(exp.t)) ".asSInt" else ".asUInt"}${if(!anvil.config.splitTempSizes) "" else splitStr}"
      }
      case exp: AST.IR.Exp.Unary => {
        val variableST = processExpr(exp.exp, F, ipPortLogic, hwLog)
        val isUnsigned = !anvil.isSigned(exp.tipe)
        val opString: String = exp.op match {
          case lang.ast.Exp.UnaryOp.Not => "!"
          case lang.ast.Exp.UnaryOp.Plus => "+"
          case lang.ast.Exp.UnaryOp.Minus => "-"
          case lang.ast.Exp.UnaryOp.Complement => "~"
        }
        exprST = opString match {
          case "-" => st"${opString}${if(isUnsigned) s"${variableST.render}.asSInt" else s"${variableST.render}"}"
          case _ => st"${opString}${variableST.render}"
        }
      }
      case exp: AST.IR.Exp.Binary => {
        val isSIntOperation = isSignedExp(exp.left) || isSignedExp(exp.right)
        val isBoolOperation = isBoolExp(exp.left) || isBoolExp(exp.right)
        val leftST = st"${processExpr(exp.left, F, ipPortLogic, hwLog).render}${if(isSIntOperation && (!isSignedExp(exp.left))) ".asSInt" else ""}"
        val rightST = st"${processExpr(exp.right, F, ipPortLogic, hwLog).render}${if(isSIntOperation && (!isSignedExp(exp.right))) ".asSInt" else ""}"
        exp.op match {
          case AST.IR.Exp.Binary.Op.Add => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Add, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Add, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              exprST = st"(${leftST.render} + ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Sub => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Sub, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Sub, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              exprST = st"(${leftST.render} - ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Mul => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if (isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Mul, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Mul, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              //ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}_${allocIndex}.io.start := RegNext(false.B)"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              exprST = st"(${leftST.render} * ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Div => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if (isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Div, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Div, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              //ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}_${allocIndex}.io.start := RegNext(false.B)"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.quotient"
            } else {
              exprST = st"(${leftST.render} / ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Rem => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if (isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Rem, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Rem, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.remainder"
            } else {
              exprST = st"(${leftST.render} % ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.And => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation || isBoolOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val signed: B = if (!isSIntOperation || isBoolOperation) F else T
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.And, signed)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.And, signed), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              exprST = st"(${leftST.render} & ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Or  => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation || isBoolOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val signed: B = if (!isSIntOperation || isBoolOperation) F else T
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Or, signed)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Or, signed), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              exprST = st"(${leftST.render} | ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Xor => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation || isBoolOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val signed: B = if (!isSIntOperation || isBoolOperation) F else T
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Xor, signed)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Xor, signed), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              exprST = st"(${leftST.render} ^ ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.CondAnd => {
            halt(s"processExpr, you got an error about Op.CondAnd")
          }
          case AST.IR.Exp.Binary.Op.CondOr => {
            halt(s"processExpr, you got an error about Op.CondOr")
          }
          case AST.IR.Exp.Binary.Op.Eq => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation || isBoolOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val signed: B = if (!isSIntOperation || isBoolOperation) F else T
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Eq, signed)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Eq, signed), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out.asUInt"
            } else {
              exprST = st"(${leftST.render} === ${rightST.render}).asUInt"
            }
          }
          case AST.IR.Exp.Binary.Op.Ne => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation || isBoolOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val signed: B = if (!isSIntOperation || isBoolOperation) F else T
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Ne, signed)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Ne, signed), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out.asUInt"
            } else {
              exprST = st"(${leftST.render} =/= ${rightST.render}).asUInt"
            }
          }
          case AST.IR.Exp.Binary.Op.Ge => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Ge, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Ge, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out.asUInt"
            } else {
              exprST = st"(${leftST.render} >= ${rightST.render}).asUInt"
            }
          }
          case AST.IR.Exp.Binary.Op.Gt => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Gt, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Gt, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out.asUInt"
            } else {
              exprST = st"(${leftST.render} > ${rightST.render}).asUInt"
            }
          }
          case AST.IR.Exp.Binary.Op.Le => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Le, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Le, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out.asUInt"
            } else {
              exprST = st"(${leftST.render} <= ${rightST.render}).asUInt"
            }
          }
          case AST.IR.Exp.Binary.Op.Lt => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Lt, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Lt, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out.asUInt"
            } else {
              exprST = st"(${leftST.render} < ${rightST.render}).asUInt"
            }
          }
          case AST.IR.Exp.Binary.Op.Shr => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}.asUInt", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Shr, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Shr, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              val right: ST = if(anvil.typeBitSize(exp.right.tipe) > 7) st"${rightST.render}(6,0)" else st"${rightST.render}"
              exprST = st"((${leftST.render})${if(anvil.isSigned(exp.left.tipe)) ".asSInt" else ".asUInt"} >> ${right.render}${if(anvil.isSigned(exp.right.tipe)) ".asUInt" else ""})"
            }
          }
          case AST.IR.Exp.Binary.Op.Ushr => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}.asUInt", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Ushr, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Ushr, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              val right: ST = if(anvil.typeBitSize(exp.right.tipe) > 7) st"${rightST.render}(6,0)" else st"${rightST.render}"
              exprST = st"(((${leftST.render})${if(anvil.isSigned(exp.left.tipe)) ".asUInt" else ""} >> ${right.render}${if(anvil.isSigned(exp.right.tipe)) ".asUInt" else ""})${if(anvil.isSigned(exp.left.tipe)) ".asSInt" else ""})"
            }
          }
          case AST.IR.Exp.Binary.Op.Shl => {
            if(anvil.config.useIP) {
              val allocIndex: Z = getIpAllocIndex(exp)
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(!isSIntOperation) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}.asUInt", "UInt")
              }
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Shl, isSIntOperation)).get
              hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Shl, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
              exprST = st"${indexerInstanceName}_${allocIndex}.io.out"
            } else {
              val right: ST = if(anvil.typeBitSize(exp.right.tipe) > 7) st"${rightST.render}(6,0)" else st"${rightST.render}"
              exprST = st"((${leftST.render})${if(anvil.isSigned(exp.left.tipe)) ".asSInt" else ".asUInt"} << ${right.render}${if(anvil.isSigned(exp.right.tipe)) ".asUInt" else ""})"
            }
          }
          case _ => {
            halt(s"processExpr AST.IR.Exp.Binary unimplemented")
          }
        }
      }
      case _ => {
        halt(s"processExpr unimplemented, ${exp.prettyST(anvil.printer).render}")
      }
    }

    return exprST
  }
}

object HwSynthesizer2 {
  val defaultIndexing: Intrinsic.Indexing = Intrinsic.Indexing(baseOffset = AST.IR.Exp.Bool(F, Position.none),
    dataOffset = 0,
    index = AST.IR.Exp.Bool(F, Position.none),
    maskOpt = None(),
    elementSize = 0,
    tipe = AST.Typed.b,
    pos = Position.none)

  @record @unclonable class HwLog(var tmpWireCount: Z,
                                  var stateBlock: MOption[AST.IR.BasicBlock],
                                  var memCpyInCurrentBlock: B,
                                  var indexerInCurrentBlock: B,
                                  var activeIndexerIndex: Z,
                                  var currentLabel: Z,
                                  var maxNumLabel: Z) extends MAnvilIRTransformer{

    @pure def isMemCpyInCurrentBlock(): B = {
      return memCpyInCurrentBlock
    }

    @pure def isIndexerInCurrentBlock(): B = {
      return indexerInCurrentBlock
    }

  }

  @record @unclonable class IpPortAssign(val anvil: Anvil,
                                         val ipAlloc: Util.IpAlloc,
                                         var sts: ISZ[ST],
                                         val ipModules: ISZ[ChiselModule],
                                         var inputMap: InputMap,
                                         var whenCondST: ISZ[ST],
                                         var whenStmtST: ISZ[ST]) extends MAnvilIRTransformer {
    @pure def getInputPort(ip: IpType): HashSMap[Z, HashSMap[String, ChiselModule.Input]] = {
      return inputMap.ipMap.get(ip).get
    }

    @pure def getIpInstanceName(ip: IpType): Option[String] = {
      for(i <- 0 until ipModules.size) {
        if(ipModules(i).expression == ip) {
          return Some(ipModules(i).instanceName)
        }
      }
      return None()
    }

    @strictpure def isSignedExp(e: AST.IR.Exp): B =
      if(anvil.isScalar(e.tipe)) {
        if(anvil.isSigned(e.tipe)) T
        else F
      } else {
        anvil.isSigned(anvil.spType)
      }

    @pure def binExp(o: AST.IR.Exp): Unit = {
      @pure def inputLogic(ipt: IpType): Unit = {
        val instanceIndex: Z = ipAlloc.allocMap.get(Util.IpAlloc.Ext.exp(o)).get
        val instanceName: String = getIpInstanceName(ipt).get
        val inputs: HashSMap[Z, HashSMap[String, ChiselModule.Input]] = getInputPort(ipt)
        val h: HashSMap[String, ChiselModule.Input] = inputs.get(instanceIndex).get
        for (entry <- h.entries) {
          sts = sts :+ st"${instanceName}_${instanceIndex}.io.${entry._1} := ${entry._2.stateValue.value}"
        }
      }
      o match {
        case o: AST.IR.Exp.Binary =>
          if(anvil.config.useIP) {
            val signed: B = isSignedExp(o.left) || isSignedExp(o.right)
            inputLogic(BinaryIP(o.op, signed))
          }
        case _ =>
      }
    }

    override def pre_langastIRExpBinary(o: Exp.Binary): MAnvilIRTransformer.PreResult[IR.Exp] = {
      binExp(o)
      return MAnvilIRTransformer.PreResult_langastIRExpBinary
    }

    override def preIntrinsicCopy(o: Intrinsic.Copy): MAnvilIRTransformer.PreResult[Intrinsic.Copy] = {
      if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Default){
        binExp(o.lhsOffset)
      }
      return MAnvilIRTransformer.PreResultIntrinsicCopy
    }

    override def preIntrinsicTempLoad(o: Intrinsic.TempLoad): MAnvilIRTransformer.PreResult[Intrinsic.TempLoad] = {
      if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Default) {
        binExp(o.rhsOffset)
      }
      return MAnvilIRTransformer.PreResultIntrinsicTempLoad
    }

    override def preIntrinsicLoad(o: Intrinsic.Load): MAnvilIRTransformer.PreResult[Intrinsic.Load] = {
      if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Default) {
        binExp(o.rhsOffset)
      }
      return MAnvilIRTransformer.PreResultIntrinsicLoad
    }

    override def preIntrinsicStore(o: Intrinsic.Store): MAnvilIRTransformer.PreResult[Intrinsic.Store] = {
      if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Default) {
        binExp(o.lhsOffset)
      }
      return MAnvilIRTransformer.PreResultIntrinsicStore
    }

    override def preIntrinsicIndexing(o: Intrinsic.Indexing): MAnvilIRTransformer.PreResult[Intrinsic.Indexing] = {
      if(anvil.config.useIP) {
        val instanceIndex: Z = ipAlloc.allocMap.get(Util.IpAlloc.Ext.exp(AST.IR.Exp.Intrinsic(o))).get
        val instanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get
        val inputs: HashSMap[Z, HashSMap[String, ChiselModule.Input]] = getInputPort(IntrinsicIP(defaultIndexing))
        val h: HashSMap[String, ChiselModule.Input] = inputs.get(instanceIndex).get
        for (entry <- h.entries) {
          sts = sts :+ st"${instanceName}_${instanceIndex}.io.${entry._1} := ${entry._2.stateValue.value}"
        }
      }
      return MAnvilIRTransformer.PreResultIntrinsicIndexing
    }

    override def preIntrinsicRegisterAssign(o: Intrinsic.RegisterAssign): MAnvilIRTransformer.PreResult[Intrinsic.RegisterAssign] = {
      if(anvil.config.useIP) {
        if (o.isInc) {
          val ipT: IpType = o.value match {
            case AST.IR.Exp.Int(_, v, _) => {
              if (v < 0) BinaryIP(AST.IR.Exp.Binary.Op.Sub, F)
              else BinaryIP(AST.IR.Exp.Binary.Op.Add, F)
            }
            case _ => BinaryIP(AST.IR.Exp.Binary.Op.Add, F)
          }
          val instanceIndex: Z = ipAlloc.allocMap.get(Util.IpAlloc.Ext.exp(o.value)).get
          val instanceName: String = getIpInstanceName(ipT).get
          val inputs: HashSMap[Z, HashSMap[String, ChiselModule.Input]] = getInputPort(ipT)
          val h: HashSMap[String, ChiselModule.Input] = inputs.get(instanceIndex).get
          for (entry <- h.entries) {
            sts = sts :+ st"${instanceName}_${instanceIndex}.io.${entry._1} := ${entry._2.stateValue.value}"
          }
        }
      }
      return MAnvilIRTransformer.PreResultIntrinsicRegisterAssign
    }
  }
}