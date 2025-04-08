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
import org.sireum.lang.ast.IR.Jump
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Resolver.{QName, addBuiltIns, typeParamMap}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}

object TmpWireCount {
  var count: Z = 0
  def getCurrent: Z = {
    return count
  }
  def incCount(): Unit = {
    count = count + 1
  }
}

object BlockLog {
  var currentBlock: MOption[AST.IR.BasicBlock] = MNone()

  def getBlock: AST.IR.BasicBlock = {
    return currentBlock.get
  }

  def setBlock(b: AST.IR.BasicBlock):B = {
    currentBlock = MSome(b)
    return T
  }
}

object MemCopyLog {
  var flagMemCopyInBlock: B = F
  def isMemCopyInBlock(): B = {
    return flagMemCopyInBlock
  }

  def enableFlagMemCopyInBlock(): Unit = {
    flagMemCopyInBlock = T
  }

  def disableFlagMemCopyInBlock(): Unit = {
    flagMemCopyInBlock = F
  }
}

object DivRemLog {
  var customDivRemST: ST = st""
  var isCustomDivRem: B = F
  var byteNum: Z = 0
  var isDiv: B = F
  var isSigned: B = F
}

@datatype trait HwModule {
  @strictpure def moduleName: String
  @strictpure def instanceName: String
  @strictpure def moduleST: ST
  @strictpure def instanceDeclST: ST
  @strictpure def instancePortFuncST(bothDeclAndPort: B): ST
  @strictpure def instancePortCallST: ST
}

@datatype trait ChiselModule extends HwModule {
  @pure def signed: B
  @pure def modName: String
  @pure def modST(signed: B): ST
  @pure def insName: String
  @pure def maxNumInstance: Z
  @pure def width: Z
  @pure def inputs: ISZ[HashSMap[String, ChiselModule.Input]]
  @strictpure override def moduleName: String = modName
  @strictpure override def instanceName: String = insName
  @strictpure override def moduleST: ST = modST(signed)
  @pure def acutalInputSize: Z = {
    for(i <- 0 until inputs.size) {
      if(inputs(i).isEmpty) {
        return i
      }
    }
    return maxNumInstance
  }
  @pure override def instanceDeclST: ST = {
    val moduleInstances: ST = {
      val actualSize: Z = acutalInputSize
      val modDeclIns: ISZ[ST] = {
        for(i <- 0 until actualSize) yield
          st"""val ${instanceName}_${i} = Module(new ${moduleName}(${width}))"""
      }

      st"""
          |${(modDeclIns, "\n")}
        """
    }
    return moduleInstances
  }
  @pure override def instancePortCallST: ST = {
    var portCallST: ISZ[ST] = ISZ()
    for(i <- 0 until acutalInputSize) {
      portCallST = portCallST :+ st"init${instanceName}_${i}()"
    }
    return st"""
        |${(portCallST, "\n")}
      """
  }
  @pure override def instancePortFuncST(bothDeclAndPort: B): ST = {

    @strictpure def inputPortListST(modIdx: Z): ST = {
      val targetInstanceInputs: HashSMap[String, ChiselModule.Input] = inputs(modIdx)
      val muxLogicST: ISZ[ST] = {
        for(entry <- targetInstanceInputs.entries) yield
          st"o.${instanceName}_${modIdx}.io.${entry._1} := ${entry._2.prettyST}"
      }

      st"""
          |def init${instanceName}_${modIdx}() = {
          |  ${(muxLogicST, "\n")}
          |}
        """
    }

    @pure def inputPortListSTWithoutMux(modIdx: Z): ST = {
      @strictpure def defaultValue(portValueType: String): String = {
        portValueType match {
          case "UInt" => "0.U"
          case "SInt" => "0.S"
          case _ => "false.B"
        }
      }
      val targetInstanceInputs: HashSMap[String, ChiselModule.Input] = inputs(modIdx)
      val muxLogicST: ISZ[ST] = {
        for(entry <- targetInstanceInputs.entries) yield
          st"o.${instanceName}_${modIdx}.io.${entry._1} := ${defaultValue(entry._2.portValueType)}"
      }

      return st"""
          |def init${instanceName}_${modIdx}() = {
          |  ${(muxLogicST, "\n")}
          |}
        """
    }


    val instancePort: ST = {
      val actualSize: Z = acutalInputSize
      val modPortIns: ISZ[ST] = {
        for(i <- 0 until actualSize) yield
          st"""${(inputPortListST(i), "\n")}"""
      }
      val modPortInsWithoutMux: ISZ[ST] = {
        for(i <- 0 until actualSize) yield
          st"""${(inputPortListSTWithoutMux(i), "\n")}"""
      }

      if(bothDeclAndPort) {
        st"""
            |${(modPortIns, "\n")}
        """
      } else {
        st"""
            |${(modPortInsWithoutMux, "\n")}
        """
      }
    }

    return st"""
               |${(instancePort, "\n")}
               """
  }
}

object ChiselModule {
  @datatype class StateValue(val state: Z, val value: String) {
  }

  @datatype class Input(val stateValue: ISZ[StateValue], val portName: String, val portValueType: String) {
    @strictpure def defaultValue: String = {
      portValueType match {
        case "UInt" => "0.U"
        case "SInt" => "0.S"
        case _ => "false.B"
      }
    }
    @strictpure def prettyST: ST = st"${(for(sv <- stateValue) yield st"Mux(o.CP === ${sv.state}.U, ${sv.value}, ${defaultValue})", " |\n")}"
    @strictpure def +(v: StateValue): Input = Input(stateValue :+ v, portName, portValueType)
  }

  @datatype class InstanceVector(val modInstanceName: String, val usageVector: ISZ[(Z,Z,B)], val maxNumInstances: Z, val inputs: ISZ[HashSMap[String, Input]], val blockStartInstanceIndex: Z) {
    @strictpure def sortUsageVector: ISZ[(Z,Z,B)] = {
      val sortedUsageVector = ops.ISZOps(usageVector).sortWith( (a, b) =>
        if(a._2 != b._2) a._2 < b._2
        else a._1 < b._1
      )
      sortedUsageVector
    }

    @pure def clearUsageVector: InstanceVector = {
      val clearedUsageVector: ISZ[(Z,Z,B)] = usageVector.map(x => (x._1, x._2, F))
      return InstanceVector(modInstanceName, clearedUsageVector, maxNumInstances, inputs, blockStartInstanceIndex)
    }

    @pure def initializeBlockStartInstanceIndex: InstanceVector = {
      val sortedVector = sortUsageVector
      for(i <- 0 until sortedVector.size) {
        if(sortedVector(i)._3 == F) {
          return InstanceVector(modInstanceName, usageVector, maxNumInstances, inputs, sortedVector(i)._1)
        }
      }
      return InstanceVector(modInstanceName, usageVector, maxNumInstances, inputs, 0)
    }

    @pure def getVectorIndex(v: ISZ[(Z,Z,B)]): Z = {
      for(i <- 0 until v.size) {
        if(v(i)._3 == F && v(i)._1 >= blockStartInstanceIndex) {
          return i
        }
      }
      return -1
    }

    @pure def appendUsageVector(num: Z): InstanceVector = {
      var tempVector = ISZ[(Z,Z,B)]()
      var tempInputs = ISZ[HashSMap[String, Input]]()
      for(i <- 0 until num) {
        tempVector = tempVector :+ (maxNumInstances + i, 0, F)
        tempInputs = tempInputs :+ HashSMap.empty[String, Input]
      }
      return InstanceVector(modInstanceName, usageVector ++ tempVector, maxNumInstances + num, inputs ++ tempInputs, blockStartInstanceIndex)
    }

    @pure def initializeUsageVector: InstanceVector = {
      var tempVector = ISZ[(Z,Z,B)]()
      var tempInputs = ISZ[HashSMap[String, Input]]()
      for(i <- 0 until maxNumInstances) {
        tempVector = tempVector :+ (i, 0, F)
        tempInputs = tempInputs :+ HashSMap.empty[String, Input]
      }
      return InstanceVector(modInstanceName, tempVector, maxNumInstances, tempInputs, blockStartInstanceIndex)
    }

    @pure def addInput(inputList: HashSMap[String, Input]): (InstanceVector,Z) = {
      val allSlotUsed: B = getVectorIndex(sortUsageVector) == -1
      val originalInstance: InstanceVector = if(!allSlotUsed) this else this.appendUsageVector(1)
      val sortedVector: ISZ[(Z,Z,B)] = originalInstance.sortUsageVector
      val index: Z = originalInstance.getVectorIndex(sortedVector)
      val usage: Z = sortedVector(index)._2
      val instanceIndex: Z = sortedVector(index)._1
      var updatedTargetMod: HashSMap[String, Input] = originalInstance.inputs(instanceIndex)
      for(entry <- inputList.entries) {
        val inputPort: Option[Input] = updatedTargetMod.get(entry._1)
        val updatedPort: Input = inputPort match {
          case Some(i) => i + entry._2.stateValue(0)
          case None() => Input(entry._2.stateValue, entry._2.portName, entry._2.portValueType)
        }
        updatedTargetMod = updatedTargetMod + entry._1 ~> updatedPort
      }
      val updatedInputs: ISZ[HashSMap[String, Input]] = originalInstance.inputs(instanceIndex ~> updatedTargetMod)
      val updatedVector: ISZ[(Z,Z,B)] = sortedVector(index ~> (instanceIndex, usage + 1, T))
      return (InstanceVector(originalInstance.modInstanceName, updatedVector, originalInstance.maxNumInstances, updatedInputs, blockStartInstanceIndex), instanceIndex)
    }

    @pure def populateInputs(label: Z, hashSMap: HashSMap[String, (ST, String)]) : (InstanceVector,Z) = {
      var inputList: HashSMap[String, Input] = HashSMap.empty
      for(entry <- hashSMap.entries) {
        val stateValue: ISZ[StateValue] = ISZ(StateValue(label, entry._2._1.render))
        inputList = inputList + entry._1 ~> Input(stateValue, entry._1, entry._2._2)
      }
      return addInput(inputList)
    }
  }
}

@datatype class Adder(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val maxNumOfInstance: Z,
                      val widthOfPort: Z,
                      val inputList: ISZ[HashSMap[String, ChiselModule.Input]]) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def modName: String = moduleDeclarationName
  @strictpure override def insName: String = moduleInstanceName
  @strictpure override def maxNumInstance: Z = maxNumOfInstance
  @strictpure override def width: Z = widthOfPort
  @strictpure override def inputs: ISZ[HashSMap[String, ChiselModule.Input]] = inputList
  @strictpure def modST(signed: B): ST = {
    val portType: ST = if(signed) st"SInt" else st"UInt"
    st"""
        |class ${modName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(${width}.W))
        |        val b = Input(${portType}(${width}.W))
        |        val op = Input(Bool())
        |        val out = Output(${portType}(${width}.W))
        |    })
        |
        |    io.out := Mux(io.op, io.a + io.b, io.a - io.b)
        |}
      """
  }
}

@record class HwSynthesizer(val anvil: Anvil) {
  val sharedMemName: String = "arrayRegFiles"
  val generalRegName: String = "generalRegFiles"

  var adderUnsigned64Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderUnsigned64", ISZ[(Z,Z,B)](), 10, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector
  var adderSigned64Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderSigned64", ISZ[(Z,Z,B)](), 1, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector
  var adderUnsigned32Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderUnsigned32", ISZ[(Z,Z,B)](), 10, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector
  var adderSigned32Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderSigned32", ISZ[(Z,Z,B)](), 1, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector
  var adderUnsigned16Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderUnsigned16", ISZ[(Z,Z,B)](), 10, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector
  var adderSigned16Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderSigned16", ISZ[(Z,Z,B)](), 1, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector
  var adderUnsigned8Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderUnsigned8", ISZ[(Z,Z,B)](), 10, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector
  var adderSigned8Instance: ChiselModule.InstanceVector = ChiselModule.InstanceVector("adderSigned8", ISZ[(Z,Z,B)](), 1, ISZ[HashSMap[String, ChiselModule.Input]](), 0).initializeUsageVector

  /*
    Notes/links:
    * Slang IR: https://github.com/sireum/slang/blob/master/ast/shared/src/main/scala/org/sireum/lang/ast/IR.scala
    * Anvil IR Intrinsic: https://github.com/sireum/anvil/blob/master/shared/src/main/scala/org/sireum/anvil/Intrinsic.scala
   */
  def printProcedure(name: String, o: AST.IR.Procedure, output: Anvil.Output, maxRegisters: Util.TempVector): Unit = {
    var r = HashSMap.empty[ISZ[String], ST]
    val processedProcedureST = processProcedure(name, o, maxRegisters)
    r = r + ISZ(name) ~> o.prettyST(anvil.printer)
    output.add(T, ISZ("chisel/src/main/scala", s"chisel-${name}.scala"), processedProcedureST)
    output.add(T, ISZ("chisel", "build.sbt"), buildSbtST())
    output.add(T, ISZ("chisel", "project", "build.properties"), st"sbt.version=${output.sbtVersion}")

    if (anvil.config.genVerilog) {
      output.add(T, ISZ("chisel/src/test/scala", s"${name}VerilogGeneration.scala"), verilogGenerationST(name))
    }
    if (anvil.config.axi4) {
      output.add(T, ISZ("chisel/src/test/scala", s"AXIWrapperChiselGenerated${name}VerilogGeneration.scala"), axiWrapperVerilogGenerationST(name))
    }
    anvil.config.simOpt match {
      case Some(simConfig) => output.add(T, ISZ("chisel/src/test/scala", s"${name}Bench.scala"), testBenchST(name, simConfig.cycles))
      case _ =>
    }

    return
  }

  @pure def axiWrapperVerilogGenerationST(moduleName: String): ST = {
    val verilogGenST: ST =
      st"""
          |import chisel3.stage.{ChiselStage,ChiselGeneratorAnnotation}
          |
          |object AXIWrapperChiselGenerated${moduleName}VerilogGeneration extends App {
          |  (new ChiselStage).execute(
          |    Array("--target-dir", "generated_verilog"),
          |    Seq(ChiselGeneratorAnnotation(() => new AXIWrapperChiselGenerated${moduleName}()))
          |  )
          |}
          |
        """

    return verilogGenST
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
          |      dut.clock.setTimeout(3000)
          |
          |      dut.reset.poke(true.B)
          |      for (i <- 0 until (5)) {
          |        dut.clock.step()
          |      }
          |      dut.reset.poke(false.B)
          |      dut.clock.step()
          |
          |      dut.io.arrayWe.poke(true.B)
          |      dut.io.arrayWriteAddr.poke(0.U)
          |      dut.io.arrayWData.poke("hFFFFFFFF".U)
          |      dut.io.arrayStrb.poke("b1111".U)
          |      dut.clock.step()
          |
          |      dut.io.arrayWe.poke(true.B)
          |      dut.io.arrayWriteAddr.poke(4.U)
          |      dut.io.arrayWData.poke("hFFFFFFFF".U)
          |      dut.io.arrayStrb.poke("b1111".U)
          |      dut.clock.step()
          |
          |      dut.io.arrayWe.poke(false.B)
          |      dut.io.valid.poke(true.B)
          |      for(i <- 0 until ${cycles}) {
          |        dut.clock.step()
          |      }
          |
          |    }
          |  }
          |}
        """

    return benchST
  }

  @pure def buildSbtST(): ST = {
    val sbtST: ST =
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

    return sbtST
  }

  @pure def processProcedure(name: String, o: AST.IR.Procedure, maxRegisters: Util.TempVector): ST = {

    @strictpure def axi4WrapperST(): ST =
      st"""
          |class AXIWrapperChiselGenerated${name}(val C_S_AXI_DATA_WIDTH:  Int = 32,
          |                                         val C_S_AXI_ADDR_WIDTH:  Int = 32,
          |                                         val ARRAY_REG_WIDTH:     Int = 8,
          |                                         val ARRAY_REG_DEPTH:     Int = ${anvil.config.memory},
          |                                         ${if(!anvil.config.splitTempSizes) "val GENERAL_REG_WIDTH:   Int = 64," else ""}
          |                                         ${if(!anvil.config.splitTempSizes) s"val GENERAL_REG_DEPTH:   Int = ${maxRegisters.maxCount}," else ""}
          |                                         val STACK_POINTER_WIDTH: Int = ${anvil.spTypeByteSize*8},
          |                                         val CODE_POINTER_WIDTH:  Int = ${anvil.cpTypeByteSize*8})  extends Module {
          |    val io = IO(new Bundle{
          |        // write address channel
          |        val S_AXI_AWADDR  = Input(UInt(C_S_AXI_ADDR_WIDTH.W))
          |        val S_AXI_AWPROT  = Input(UInt(3.W))
          |        val S_AXI_AWVALID = Input(Bool())
          |        val S_AXI_AWREADY = Output(Bool())

          |        // write data channel
          |        val S_AXI_WDATA  = Input(SInt(C_S_AXI_DATA_WIDTH.W))
          |        val S_AXI_WSTRB  = Input(UInt((C_S_AXI_DATA_WIDTH/8).W))
          |        val S_AXI_WVALID = Input(Bool())
          |        val S_AXI_WREADY = Output(Bool())

          |        // write response channel
          |        val S_AXI_BRESP  = Output(UInt(2.W))
          |        val S_AXI_BVALID = Output(Bool())
          |        val S_AXI_BREADY = Input(Bool())

          |        // read address channel
          |        val S_AXI_ARADDR  = Input(UInt(C_S_AXI_ADDR_WIDTH.W))
          |        val S_AXI_ARPROT  = Input(UInt(3.W))
          |        val S_AXI_ARVALID = Input(Bool())
          |        val S_AXI_ARREADY = Output(Bool())

          |        // read data channel
          |        val S_AXI_RDATA  = Output(SInt(C_S_AXI_DATA_WIDTH.W))
          |        val S_AXI_RRESP  = Output(UInt(2.W))
          |        val S_AXI_RVALID = Output(Bool())
          |        val S_AXI_RREADY = Input(Bool())
          |    })
          |
          |    val lowActiveReset = !reset.asBool
          |  withReset(lowActiveReset) {
          |
          |    // AXI4LITE signals, the signals need to be saved
          |    val axi_awaddr  = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
          |    val axi_araddr  = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
          |    // AXI4LITE output signal
          |    val axi_awready = Reg(Bool())
          |    val axi_wready  = Reg(Bool())
          |    val axi_bresp   = Reg(UInt(2.W))
          |    val axi_bvalid  = Reg(Bool())
          |    val axi_arready = Reg(Bool())
          |    val axi_rdata   = Reg(SInt(C_S_AXI_DATA_WIDTH.W))
          |    val axi_rresp   = Reg(UInt(2.W))
          |    val axi_rvalid  = Reg(Bool())
          |
          |
          |    // Example-specific design signals
          |    // local parameter for addressing 32 bit / 64 bit C_S_AXI_DATA_WIDTH
          |    // ADDR_LSB is used for addressing 32/64 bit registers/memories
          |    // ADDR_LSB = 2 for 32 bits (n downto 2)
          |    // ADDR_LSB = 3 for 64 bits (n downto 3)
          |    val ADDR_LSB: Int = (C_S_AXI_DATA_WIDTH/32) + 1
          |    val OPT_MEM_ADDR_BITS: Int = 10
          |
          |    //----------------------------------------------
          |    //-- Signals for user logic register space example
          |    //------------------------------------------------
          |    val slv_reg_rden = Wire(Bool())
          |    val slv_reg_wren = Wire(Bool())
          |    val reg_data_out = Wire(SInt(C_S_AXI_DATA_WIDTH.W))
          |    val aw_en        = Reg(Bool())
          |
          |    // Registers for target module port
          |    val io_valid_reg = Reg(UInt(32.W))
          |    val io_ready_reg = Reg(UInt(32.W))
          |
          |    // instantiate the target module
          |    val arrayReadAddrValid = (axi_araddr(log2Ceil(ARRAY_REG_DEPTH), 0) >= 8.U) && ((axi_araddr(log2Ceil(ARRAY_REG_DEPTH), 0) + 3.U) < (ARRAY_REG_DEPTH.U + 8.U))
          |    val arrayWriteAddrValid = (axi_awaddr(log2Ceil(ARRAY_REG_DEPTH), 0) >= 8.U) && ((axi_awaddr(log2Ceil(ARRAY_REG_DEPTH), 0) + 3.U) < (ARRAY_REG_DEPTH.U + 8.U))
          |    val arrayWriteValid = slv_reg_wren & arrayWriteAddrValid
          |    val arrayReadValid = arrayReadAddrValid & axi_arready & io.S_AXI_ARVALID & ~axi_rvalid
          |    val arrayReady = axi_araddr(log2Ceil(ARRAY_REG_DEPTH), 0) === 4.U
          |    val mod${name} = Module(new ${name}(C_S_AXI_DATA_WIDTH  = C_S_AXI_DATA_WIDTH ,
          |                                                C_S_AXI_ADDR_WIDTH  = C_S_AXI_ADDR_WIDTH ,
          |                                                ARRAY_REG_WIDTH     = ARRAY_REG_WIDTH    ,
          |                                                ARRAY_REG_DEPTH     = ARRAY_REG_DEPTH    ,
          |                                                ${if(!anvil.config.splitTempSizes) "GENERAL_REG_WIDTH   = GENERAL_REG_WIDTH  ," else ""}
          |                                                ${if(!anvil.config.splitTempSizes) "GENERAL_REG_DEPTH   = GENERAL_REG_DEPTH  ," else ""}
          |                                                STACK_POINTER_WIDTH = STACK_POINTER_WIDTH,
          |                                                CODE_POINTER_WIDTH  = CODE_POINTER_WIDTH  ))
          |    mod${name}.io.valid := Mux(io_valid_reg(0) & (io_ready_reg === 2.U), true.B, false.B)
          |    io_ready_reg := mod${name}.io.ready
          |    mod${name}.io.arrayRe := arrayReadValid
          |    mod${name}.io.arrayWe := arrayWriteValid
          |    mod${name}.io.arrayStrb := Mux(arrayWriteValid, io.S_AXI_WSTRB, 0.U)
          |    mod${name}.io.arrayWriteAddr := Mux(arrayWriteValid,
          |                                                    Cat(axi_awaddr(log2Ceil(ARRAY_REG_DEPTH) - 1, ADDR_LSB), 0.U(ADDR_LSB.W)) - 8.U,
          |                                                    0.U)
          |    mod${name}.io.arrayReadAddr  := Mux(arrayReadValid,
          |                                                    Cat(axi_araddr(log2Ceil(ARRAY_REG_DEPTH) - 1, ADDR_LSB), 0.U(ADDR_LSB.W)) - 8.U,
          |                                                    0.U)
          |    mod${name}.io.arrayWData := Mux(arrayWriteValid, io.S_AXI_WDATA.asUInt, 0.U)
          |
          |    when(arrayReady) {
          |        reg_data_out := io_ready_reg.asSInt
          |    } .elsewhen(arrayReadValid) {
          |        reg_data_out := mod${name}.io.arrayRData.asSInt
          |    } .otherwise {
          |        reg_data_out := 0.S
          |    }
          |
          |    when(lowActiveReset.asBool) {
          |        io_ready_reg := 0.U
          |    } .otherwise {
          |        io_ready_reg := mod${name}.io.ready
          |    }
          |
          |    // I/O Connections assignments
          |    io.S_AXI_AWREADY := axi_awready;
          |    io.S_AXI_WREADY  := axi_wready;
          |    io.S_AXI_BRESP   := axi_bresp;
          |    io.S_AXI_BVALID	 := axi_bvalid;
          |    io.S_AXI_ARREADY := axi_arready;
          |    io.S_AXI_RDATA   := axi_rdata;
          |    io.S_AXI_RRESP   := axi_rresp;
          |    io.S_AXI_RVALID  := axi_rvalid;
          |
          |    // Implement axi_awready generation
          |    // axi_awready is asserted for one S_AXI_ACLK clock cycle when both
          |    // S_AXI_AWVALID and S_AXI_WVALID are asserted. axi_awready is
          |    // de-asserted when reset is low.
          |    when(lowActiveReset.asBool) {
          |        axi_awready := false.B
          |        aw_en       := true.B
          |    } .otherwise {
          |        when(~axi_awready && io.S_AXI_AWVALID && io.S_AXI_WVALID && aw_en) {
          |            // slave is ready to accept write address when
          |            // there is a valid write address and write data
          |            // on the write address and data bus. This design
          |            // expects no outstanding transactions.
          |            axi_awready := true.B
          |            aw_en       := false.B
          |        } .elsewhen(io.S_AXI_BREADY && axi_bvalid) {
          |            // the current operation is finished
          |            // prepare for the next write operation
          |            axi_awready := false.B
          |            aw_en       := true.B
          |        } .otherwise {
          |            axi_awready  := false.B
          |        }
          |    }
          |
          |    // Implement axi_awaddr latching
          |    // This process is used to latch the address when both
          |    // S_AXI_AWVALID and S_AXI_WVALID are valid.
          |    when(lowActiveReset.asBool) {
          |        axi_awaddr := 0.U
          |    } .otherwise {
          |        when(~axi_awready && io.S_AXI_AWVALID && io.S_AXI_WVALID && aw_en) {
          |            axi_awaddr := io.S_AXI_AWADDR
          |        }
          |    }
          |
          |    // Implement axi_wready generation
          |    // axi_wready is asserted for one S_AXI_ACLK clock cycle when both
          |    // S_AXI_AWVALID and S_AXI_WVALID are asserted. axi_wready is
          |    // de-asserted when reset is low.
          |    when(lowActiveReset.asBool) {
          |        axi_wready := false.B
          |    } .otherwise {
          |        when(~axi_wready && io.S_AXI_WVALID && io.S_AXI_AWVALID && aw_en) {
          |            // slave is ready to accept write data when
          |            // there is a valid write address and write data
          |            // on the write address and data bus. This design
          |            // expects no outstanding transactions.
          |            axi_wready := true.B
          |        } .otherwise {
          |            axi_wready := false.B
          |        }
          |    }
          |
          |    // Implement memory mapped register select and write logic generation
          |    // The write data is accepted and written to memory mapped registers when
          |    // axi_awready, S_AXI_WVALID, axi_wready and S_AXI_WVALID are asserted. Write strobes are used to
          |    // select byte enables of slave registers while writing.
          |    // These registers are cleared when reset (active low) is applied.
          |    // Slave register write enable is asserted when valid address and data are available
          |    // and the slave is ready to accept the write address and write data.
          |    slv_reg_wren := axi_wready && io.S_AXI_WVALID && axi_awready && io.S_AXI_AWVALID
          |
          |    val writeEffectiveAddr = axi_awaddr(log2Ceil(ARRAY_REG_DEPTH), 0)
          |
          |    when(lowActiveReset.asBool) {
          |        io_valid_reg := 0.U
          |    } .otherwise {
          |        when(slv_reg_wren && writeEffectiveAddr === 0.U) {
          |                io_valid_reg := io.S_AXI_WDATA.asUInt
          |        }
          |    }
          |
          |    // Implement write response logic generation
          |    // The write response and response valid signals are asserted by the slave
          |    // when axi_wready, S_AXI_WVALID, axi_wready and S_AXI_WVALID are asserted.
          |    // This marks the acceptance of address and indicates the status of
          |    // write transaction.
          |    when(lowActiveReset.asBool) {
          |        axi_bvalid := false.B
          |        axi_bresp  := 0.U
          |    } .otherwise {
          |        when(axi_awready && io.S_AXI_AWVALID && ~axi_bvalid && axi_wready && io.S_AXI_WVALID) {
          |            axi_bvalid := true.B
          |            axi_bresp  := 0.U
          |        } .otherwise {
          |            when(io.S_AXI_BREADY && axi_bvalid) {
          |                axi_bvalid := false.B
          |            }
          |        }
          |    }
          |
          |    // Implement axi_arready generation
          |    // axi_arready is asserted for one S_AXI_ACLK clock cycle when
          |    // S_AXI_ARVALID is asserted. axi_awready is
          |    // de-asserted when reset (active low) is asserted.
          |    // The read address is also latched when S_AXI_ARVALID is
          |    // asserted. axi_araddr is reset to zero on reset assertion.
          |    when(lowActiveReset.asBool) {
          |        axi_arready := false.B
          |        axi_araddr  := 0.U
          |    } .otherwise {
          |        when(~axi_arready && io.S_AXI_ARVALID) {
          |            // indicates that the slave has acceped the valid read address
          |            axi_arready := true.B
          |            axi_araddr  := io.S_AXI_ARADDR
          |        } .otherwise {
          |            axi_arready := false.B
          |        }
          |    }
          |
          |    // Implement axi_arvalid generation
          |    // axi_rvalid is asserted for one S_AXI_ACLK clock cycle when both
          |    // S_AXI_ARVALID and axi_arready are asserted. The slave registers
          |    // data are available on the axi_rdata bus at this instance. The
          |    // assertion of axi_rvalid marks the validity of read data on the
          |    // bus and axi_rresp indicates the status of read transaction.axi_rvalid
          |    // is deasserted on reset (active low). axi_rresp and axi_rdata are
          |    // cleared to zero on reset (active low).
          |    when(lowActiveReset.asBool) {
          |        axi_rvalid := false.B
          |        axi_rresp  := 0.U
          |    } .otherwise {
          |        when(axi_arready && io.S_AXI_ARVALID && ~axi_rvalid) {
          |            axi_rvalid := true.B
          |            axi_rresp  := 0.U
          |        } .elsewhen(axi_rvalid && io.S_AXI_RREADY) {
          |            axi_rvalid := false.B
          |        }
          |    }
          |
          |    // Implement memory mapped register select and read logic generation
          |    // Slave register read enable is asserted when valid address is available
          |    // and the slave is ready to accept the read address.
          |    slv_reg_rden := axi_arready & io.S_AXI_ARVALID & ~axi_rvalid;
          |
          |    // Output register or memory read data
          |    when(lowActiveReset.asBool) {
          |        axi_rdata := 0.S
          |    } .otherwise {
          |        // When there is a valid read address (S_AXI_ARVALID) with
          |        // acceptance of read address by the slave (axi_arready),
          |        // output the read dada
          |        when(slv_reg_rden) {
          |            axi_rdata := reg_data_out
          |        }
          |    }
          |  }
          |}
        """

    @strictpure def dividerST(): ST =
      st"""
          |class PipelinedDivMod(val N: Int) extends Module {
          |  val io = IO(new Bundle {
          |    val a = Input(UInt(N.W))
          |    val b = Input(UInt(N.W))
          |    val start = Input(Bool())
          |    val valid = Output(Bool())
          |    val quotient = Output(UInt(N.W))
          |    val remainder = Output(UInt(N.W))
          |  })
          |
          |  val dividend = RegInit(0.U(N.W))
          |  val divisor = RegInit(0.U(N.W))
          |  val quotient = RegInit(0.U(N.W))
          |  val remainder = RegInit(0.U(N.W))
          |  val count = RegInit((N - 1).U((1+log2Ceil(N)).W))
          |  val busy = RegInit(false.B)
          |
          |  when(io.start && !busy) {
          |    dividend := io.a
          |    divisor := io.b
          |    quotient := 0.U
          |    remainder := 0.U
          |    count := N.U
          |    busy := true.B
          |  }.elsewhen(busy) {
          |    when(count === 0.U) {
          |      busy := false.B
          |    } .otherwise {
          |      val shifted = remainder << 1 | (dividend >> (N - 1))
          |      remainder := shifted
          |
          |      when (shifted >= divisor) {
          |        remainder := shifted - divisor
          |        quotient := (quotient << 1) | 1.U
          |      } .otherwise {
          |        quotient := quotient << 1
          |      }
          |
          |      dividend := dividend << 1
          |      count := count - 1.U
          |    }
          |  }
          |
          |  io.quotient := quotient
          |  io.remainder := remainder
          |  io.valid := !busy
          |}
        """

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
        generalRegST = generalRegST :+ st"val ${entry._1} = Reg(Vec(${entry._2._2}, ${if(entry._2._3) "SInt" else "UInt"}(${entry._2._1}.W)))"
      }

      return st"${(generalRegST, "\n")}"
    }

    @pure def procedureST(stateMachineST: ST): ST = {
      val adderUnsigned64Module: Adder = Adder(F, "AdderUnsigned64", "adderUnsigned64", adderUnsigned64Instance.maxNumInstances, 64, adderUnsigned64Instance.inputs)
      val adderSigned64Module: Adder = Adder(T, "AdderSigned64", "adderSigned64", adderSigned64Instance.maxNumInstances, 64, adderSigned64Instance.inputs)
      val adderUnsigned32Module: Adder = Adder(F, "AdderUnsigned32", "adderUnsigned32", adderUnsigned32Instance.maxNumInstances, 32, adderUnsigned32Instance.inputs)
      val adderSigned32Module: Adder = Adder(T, "AdderSigned32", "adderSigned32", adderSigned32Instance.maxNumInstances, 32, adderSigned32Instance.inputs)
      val adderUnsigned16Module: Adder = Adder(F, "AdderUnsigned16", "adderUnsigned16", adderUnsigned16Instance.maxNumInstances, 16, adderUnsigned16Instance.inputs)
      val adderSigned16Module: Adder = Adder(T, "AdderSigned16", "adderSigned16", adderSigned16Instance.maxNumInstances, 16, adderSigned16Instance.inputs)
      val adderUnsigned8Module: Adder = Adder(F, "AdderUnsigned8", "adderUnsigned8", adderUnsigned8Instance.maxNumInstances, 8, adderUnsigned8Instance.inputs)
      val adderSigned8Module: Adder = Adder(T, "AdderSigned8", "adderSigned8", adderSigned8Instance.maxNumInstances, 8, adderSigned8Instance.inputs)

      val adderModuleDeclST: ST = {
        var moduleST: ISZ[ST] = ISZ()
        moduleST = moduleST :+ adderUnsigned64Module.moduleST
        moduleST = moduleST :+ adderSigned64Module.moduleST
        moduleST = moduleST :+ adderUnsigned32Module.moduleST
        moduleST = moduleST :+ adderSigned32Module.moduleST
        moduleST = moduleST :+ adderUnsigned16Module.moduleST
        moduleST = moduleST :+ adderSigned16Module.moduleST
        moduleST = moduleST :+ adderUnsigned8Module.moduleST
        moduleST = moduleST :+ adderSigned8Module.moduleST
        st"""${(moduleST, "\n")}"""
      }

      val adderInstanceDeclST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        instanceST = instanceST :+ adderUnsigned64Module.instanceDeclST
        instanceST = instanceST :+ adderSigned64Module.instanceDeclST
        instanceST = instanceST :+ adderUnsigned32Module.instanceDeclST
        instanceST = instanceST :+ adderSigned32Module.instanceDeclST
        instanceST = instanceST :+ adderUnsigned16Module.instanceDeclST
        instanceST = instanceST :+ adderSigned16Module.instanceDeclST
        instanceST = instanceST :+ adderUnsigned8Module.instanceDeclST
        instanceST = instanceST :+ adderSigned8Module.instanceDeclST
        st"""${(instanceST, "\n")}"""
      }

      val adderInstancePortFuncST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        instanceST = instanceST :+ adderUnsigned64Module.instancePortFuncST(anvil.config.mux)
        instanceST = instanceST :+ adderSigned64Module.instancePortFuncST(anvil.config.mux)
        instanceST = instanceST :+ adderUnsigned32Module.instancePortFuncST(anvil.config.mux)
        instanceST = instanceST :+ adderSigned32Module.instancePortFuncST(anvil.config.mux)
        instanceST = instanceST :+ adderUnsigned16Module.instancePortFuncST(anvil.config.mux)
        instanceST = instanceST :+ adderSigned16Module.instancePortFuncST(anvil.config.mux)
        instanceST = instanceST :+ adderUnsigned8Module.instancePortFuncST(anvil.config.mux)
        instanceST = instanceST :+ adderSigned8Module.instancePortFuncST(anvil.config.mux)
        st"""${(instanceST, "\n")}"""
      }

      val adderInstancePortCallST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        instanceST = instanceST :+ adderUnsigned64Module.instancePortCallST
        instanceST = instanceST :+ adderSigned64Module.instancePortCallST
        instanceST = instanceST :+ adderUnsigned32Module.instancePortCallST
        instanceST = instanceST :+ adderSigned32Module.instancePortCallST
        instanceST = instanceST :+ adderUnsigned16Module.instancePortCallST
        instanceST = instanceST :+ adderSigned16Module.instancePortCallST
        instanceST = instanceST :+ adderUnsigned8Module.instancePortCallST
        instanceST = instanceST :+ adderSigned8Module.instancePortCallST
        st"""${(instanceST, "\n")}"""
      }

      return st"""
          |import chisel3._
          |import chisel3.util._
          |import chisel3.experimental._
          |
          |${if (anvil.config.customDivRem) dividerST().render else ""}
          |${if (anvil.config.alu) adderModuleDeclST else st""}
          |
          |import ${name}._
          |class ${name} (val C_S_AXI_DATA_WIDTH:  Int = 32,
          |               val C_S_AXI_ADDR_WIDTH:  Int = 32,
          |               val ARRAY_REG_WIDTH:     Int = 8,
          |               val ARRAY_REG_DEPTH:     Int = ${anvil.config.memory},
          |               ${if (!anvil.config.splitTempSizes) "val GENERAL_REG_WIDTH:   Int = 64," else ""}
          |               ${if (!anvil.config.splitTempSizes) s"val GENERAL_REG_DEPTH:   Int = ${maxRegisters.maxCount}," else ""}
          |               val STACK_POINTER_WIDTH: Int = ${anvil.spTypeByteSize * 8},
          |               val CODE_POINTER_WIDTH:  Int = ${anvil.cpTypeByteSize * 8}) extends Module {
          |
          |    val io = IO(new Bundle{
          |        val valid          = Input(Bool())
          |        val ready          = Output(UInt(2.W))
          |        val arrayRe        = Input(Bool())
          |        val arrayWe        = Input(Bool())
          |        val arrayStrb      = Input(UInt((C_S_AXI_DATA_WIDTH/8).W))
          |        val arrayReadAddr  = Input(UInt((log2Ceil(ARRAY_REG_DEPTH)).W))
          |        val arrayWriteAddr = Input(UInt((log2Ceil(ARRAY_REG_DEPTH)).W))
          |        val arrayWData     = Input(UInt(C_S_AXI_DATA_WIDTH.W))
          |        val arrayRData     = Output(UInt(C_S_AXI_DATA_WIDTH.W))
          |    })
          |
          |    // reg for share array between software and IP
          |    val ${sharedMemName} = Reg(Vec(ARRAY_REG_DEPTH, UInt(ARRAY_REG_WIDTH.W)))
          |    // reg for general purpose
          |    ${if (!anvil.config.splitTempSizes) s"val ${generalRegName} = Reg(Vec(GENERAL_REG_DEPTH, UInt(GENERAL_REG_WIDTH.W)))" else s"${generalPurposeRegisterST.render}"}
          |    // reg for code pointer
          |    val CP = RegInit(2.U(CODE_POINTER_WIDTH.W))
          |    // reg for stack pointer
          |    val SP = RegInit(0.U(STACK_POINTER_WIDTH.W))
          |    // reg for display pointer
          |    val DP = RegInit(0.U(64.W))
          |    // reg for index in memcopy
          |    val Idx = RegInit(0.U(16.W))
          |    // reg for recording how many rounds needed for the left bytes
          |    val LeftByteRounds = RegInit(0.U(8.W))
          |    val IdxLeftByteRounds = RegInit(0.U(8.W))
          |
          |    ${if (anvil.config.customDivRem) "// divider" else ""}
          |    ${if (anvil.config.customDivRem) "val divider64 = Module(new PipelinedDivMod(64))" else ""}
          |    ${if (anvil.config.customDivRem) "divider64.io.a := 1.U" else ""}
          |    ${if (anvil.config.customDivRem) "divider64.io.b := 1.U" else ""}
          |    ${if (anvil.config.customDivRem) "divider64.io.start := false.B" else ""}
          |    ${if (anvil.config.customDivRem) "val divider32 = Module(new PipelinedDivMod(32))" else ""}
          |    ${if (anvil.config.customDivRem) "divider32.io.a := 1.U" else ""}
          |    ${if (anvil.config.customDivRem) "divider32.io.b := 1.U" else ""}
          |    ${if (anvil.config.customDivRem) "divider32.io.start := false.B" else ""}
          |    ${if (anvil.config.customDivRem) "val dividerStart = RegInit(false.B)" else ""}
          |
          |    ${if(anvil.config.alu) adderInstanceDeclST else st""}
          |    init(this)
          |
          |    // write operation
          |    for(byteIndex <- 0 until (C_S_AXI_DATA_WIDTH/8)) {
          |      when(io.arrayWe & (io.arrayStrb(byteIndex.U) === 1.U)) {
          |        ${sharedMemName}(io.arrayWriteAddr + byteIndex.U) := io.arrayWData((byteIndex * 8) + 7, byteIndex * 8)
          |      }
          |    }
          |
          |    // read operation
          |    io.arrayRData := Mux(io.arrayRe, Cat(${sharedMemName}(io.arrayReadAddr + 3.U),
          |                                         ${sharedMemName}(io.arrayReadAddr + 2.U),
          |                                         ${sharedMemName}(io.arrayReadAddr + 1.U),
          |                                         ${sharedMemName}(io.arrayReadAddr + 0.U)), 0.U)
          |
          |    io.ready := Mux(CP === 0.U, 0.U, Mux(CP === 1.U, 1.U, 2.U))
          |
          |    ${(stateMachineST, "")}
          |
          |}
          |
          |object ${name} {
          |  def init(o: ${name}) {
          |    import o._
          |    ${if(anvil.config.alu) adderInstancePortFuncST.render else ""}
          |    ${if(anvil.config.alu) adderInstancePortCallST else st""}
          |  }
          |}
          |
          |${if (anvil.config.axi4) axi4WrapperST().render else ""}
          """
    }

    val basicBlockST = processBasicBlock(o.body.asInstanceOf[AST.IR.Body.Basic].blocks)

    return procedureST(basicBlockST)
  }

  @pure def processBasicBlock(bs: ISZ[AST.IR.BasicBlock]): ST = {
    @strictpure def basicBlockST(grounds: ISZ[ST]): ST =
      st"""
          |switch(CP) {
          |  is(2.U) {
          |    CP := Mux(io.valid, 3.U, CP)
          |  }
          |  ${(grounds, "")}
          |}"""

    @pure def instanceVectorWithoutMux(ins: ChiselModule.InstanceVector): ST = {
      var portLogicST: ISZ[ST] = ISZ()
      for(i <- 0 until ins.maxNumInstances) {
        if(ins.usageVector(i)._3) {
          val insName = s"${ins.modInstanceName}_${ins.usageVector(i)._1}"
          for(entry <- ins.inputs(ins.usageVector(i)._1).entries) {
            val inputValue = entry._2.stateValue
            if(inputValue.size > 0) {
              portLogicST = portLogicST :+ st"${insName}.io.${entry._2.portName} := ${inputValue(inputValue.size - 1).value}"
            }
          }
        }
      }
        return st"""
              |${(portLogicST, "\n")}"""
    }

    @pure def adderWithoutMuxST: ST = {
      var addersST: ISZ[ST] = ISZ()
      addersST = addersST :+ instanceVectorWithoutMux(adderUnsigned64Instance)
      addersST = addersST :+ instanceVectorWithoutMux(adderSigned64Instance)
      addersST = addersST :+ instanceVectorWithoutMux(adderUnsigned32Instance)
      addersST = addersST :+ instanceVectorWithoutMux(adderSigned32Instance)
      addersST = addersST :+ instanceVectorWithoutMux(adderUnsigned16Instance)
      addersST = addersST :+ instanceVectorWithoutMux(adderSigned16Instance)
      addersST = addersST :+ instanceVectorWithoutMux(adderUnsigned8Instance)
      addersST = addersST :+ instanceVectorWithoutMux(adderSigned8Instance)
      return st"""
          |${(addersST, "\n")}"""
    }

    @pure def groundST(b: AST.IR.BasicBlock, ground: ST, jump: ST): ST = {
      var commentST = ISZ[ST]()

      for(g <- b.grounds) {
        commentST = commentST :+ g.prettyST(anvil.printer)
      }
      commentST = commentST :+ b.jump.prettyST(anvil.printer)

      if(b.label > 1) {
        return st"""
                   |is(${b.label}.U) {
                   |  /*
                   |  ${(commentST, "\n")}
                   |  */
                   |  ${(ground, "")}
                   |  ${if(anvil.config.alu && !anvil.config.mux) adderWithoutMuxST.render else ""}
                   |  ${if(!MemCopyLog.isMemCopyInBlock() & !DivRemLog.isCustomDivRem) jump.render else st""}
                   |}
                 """
      } else {
        return st""
      }
    }

    var groundsST = ISZ[ST]()

    for (b <- bs) {
      BlockLog.setBlock(b)

      if(b.label != 0) {
        val jump = processJumpIntrinsic(b)
        groundsST = groundsST :+ groundST(b, processGround(b.grounds), jump)
      }

      MemCopyLog.disableFlagMemCopyInBlock()
      DivRemLog.isCustomDivRem = F
      DivRemLog.isDiv = F
      DivRemLog.customDivRemST = st""
      DivRemLog.byteNum = 0
      DivRemLog.isSigned = F

      if(anvil.config.alu) {
        adderUnsigned64Instance = adderUnsigned64Instance.clearUsageVector
        adderUnsigned64Instance = adderUnsigned64Instance.initializeBlockStartInstanceIndex
        adderSigned64Instance = adderSigned64Instance.clearUsageVector
        adderSigned64Instance = adderSigned64Instance.initializeBlockStartInstanceIndex
        adderUnsigned32Instance = adderUnsigned32Instance.clearUsageVector
        adderUnsigned32Instance = adderUnsigned32Instance.initializeBlockStartInstanceIndex
        adderSigned32Instance = adderSigned32Instance.clearUsageVector
        adderSigned32Instance = adderSigned32Instance.initializeBlockStartInstanceIndex
        adderUnsigned16Instance = adderUnsigned16Instance.clearUsageVector
        adderUnsigned16Instance = adderUnsigned16Instance.initializeBlockStartInstanceIndex
        adderSigned16Instance = adderSigned16Instance.clearUsageVector
        adderSigned16Instance = adderSigned16Instance.initializeBlockStartInstanceIndex
        adderUnsigned8Instance = adderUnsigned8Instance.clearUsageVector
        adderUnsigned8Instance = adderUnsigned8Instance.initializeBlockStartInstanceIndex
        adderSigned8Instance = adderSigned8Instance.clearUsageVector
        adderSigned8Instance = adderSigned8Instance.initializeBlockStartInstanceIndex
      }
    }

    return basicBlockST(groundsST)
  }

  @pure def processGround(gs: ISZ[AST.IR.Stmt.Ground]): ST = {
    var groundST = ISZ[ST]()

    for(g <- gs) {
      g match {
        case g: AST.IR.Stmt.Assign => {
          groundST = groundST :+ processStmtAssign(g)
        }
        case g: AST.IR.Stmt.Intrinsic => {
          groundST = groundST :+ processStmtIntrinsic(g)
        }
        case _ => {
          halt(s"processGround unimplemented")
        }
      }
    }

    return st"""
               |${(groundST, "")}"""
  }

  @pure def processJumpIntrinsic(b: AST.IR.BasicBlock): ST = {
    var intrinsicST = st""
    val j = b.jump

    j match {
      case AST.IR.Jump.Intrinsic(intrinsic: Intrinsic.GotoLocal) => {
        if (intrinsic.isTemp) {
          intrinsicST =
            st"""
                |CP := ${processExpr(AST.IR.Exp.Temp(intrinsic.loc, anvil.cpType, intrinsic.pos), F)}
            """
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

          intrinsicST =
            st"""
                |CP := Cat(
                |  ${(returnAddrST, "\n")}
                |)
            """
        }
      }
      case j: AST.IR.Jump.Goto => {
        intrinsicST = st"CP := ${j.label}.U"
      }
      case j: AST.IR.Jump.If => {
        val cond = processExpr(j.cond, F)
        intrinsicST = st"CP := Mux((${cond.render}.asUInt) === 1.U, ${j.thenLabel}.U, ${j.elseLabel}.U)"
      }
      case j: AST.IR.Jump.Switch => {
        val condExprST = processExpr(j.exp, F)

        val tmpWire = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()

        val defaultStatementST: ST = j.defaultLabelOpt match {
          case Some(x) => st"CP := ${x}.U"
          case None() => st""
        }

        var isStatementST = ISZ[ST]()
        for(i <- j.cases) {
          isStatementST = isStatementST :+
            st"""
                |is(${processExpr(i.value, F).render}) {
                |  CP := ${i.label}.U
                |}
              """
        }

        intrinsicST =
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

    return intrinsicST
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

  @pure def processStmtIntrinsic(i: AST.IR.Stmt.Intrinsic): ST = {
    var intrinsicST = st""

    i match {
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.TempLoad) => {
        var internalST = ISZ[ST]()
        val rhsOffsetST = processExpr(intrinsic.rhsOffset, F)
        val tmpWire = st"__tmp_${TmpWireCount.getCurrent}"

        for(i <- (intrinsic.bytes - 1) to 0 by -1) {
          if(i == 0) {
            internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U)"
          } else {
            internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U),"
          }
        }

        val padST = st".asSInt.pad(${if(!anvil.config.splitTempSizes) "GENERAL_REG_WIDTH" else s"${anvil.typeBitSize(intrinsic.tipe)}"})"

        intrinsicST =
          st"""
              |val ${tmpWire} = (${rhsOffsetST.render}).asUInt
              |${if(!anvil.config.splitTempSizes) s"${generalRegName}(${intrinsic.temp}.U)" else s"${getGeneralRegName(intrinsic.tipe)}(${intrinsic.temp}.U)"} := Cat(
              |  ${(internalST, "\n")}
              |)${if(intrinsic.isSigned) s"${padST.render}" else ""}${if(!anvil.config.splitTempSizes) ".asUInt" else ""}
            """
        TmpWireCount.incCount()
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Copy) => {
        MemCopyLog.enableFlagMemCopyInBlock()

        // acquire the source and destination address
        val lhsAddrST = processExpr(intrinsic.lhsOffset, F)
        val rhsAddrST = processExpr(intrinsic.rhs, F)

        val tmpWireLhsST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()
        val tmpWireRhsST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()
        val totalSizeWireST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()
        val leftByteStartST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()

        // compute how many bytes needed for memory copy transfer
        val rhsBytesSt = processExpr(intrinsic.rhsBytes, F)
        var BytesTransferST = ISZ[ST]()
        for(i <- 0 to (anvil.config.copySize - 1)) {
          BytesTransferST = BytesTransferST :+ st"${sharedMemName}(${tmpWireLhsST.render} + Idx + ${i}.U) := ${sharedMemName}(${tmpWireRhsST.render} + Idx + ${i}.U)"
        }

        // get the jump statement ST
        val jumpST = processJumpIntrinsic(BlockLog.getBlock)

        intrinsicST =
          st"""
              |val ${tmpWireLhsST.render} = ${lhsAddrST.render}
              |val ${tmpWireRhsST.render} = ${rhsAddrST.render}
              |val ${totalSizeWireST.render} = ${rhsBytesSt.render}
              |
              |when(Idx < ${totalSizeWireST.render}) {
              |  ${(BytesTransferST, "\n")}
              |  Idx := Idx + ${anvil.config.copySize}.U
              |  LeftByteRounds := ${totalSizeWireST.render} - Idx
              |} .elsewhen(IdxLeftByteRounds < LeftByteRounds) {
              |  val ${leftByteStartST.render} = Idx - ${anvil.config.copySize}.U
              |  ${sharedMemName}(${tmpWireLhsST.render} + ${leftByteStartST.render} + IdxLeftByteRounds) := ${sharedMemName}(${tmpWireRhsST.render} + ${leftByteStartST.render} + IdxLeftByteRounds)
              |  IdxLeftByteRounds := IdxLeftByteRounds + 1.U
              |} .otherwise {
              |  Idx := 0.U
              |  IdxLeftByteRounds := 0.U
              |  LeftByteRounds := 0.U
              |  ${jumpST.render}
              |}
            """

      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Store) => {
        val lhsOffsetST = processExpr(intrinsic.lhsOffset, F)
        val rhsST = processExpr(intrinsic.rhs, intrinsic.isSigned)
        var shareMemAssign = ISZ[ST]()
        val tmpWireLhsST = st"__tmp_${TmpWireCount.getCurrent}"
        val tmpWireRhsST = st"__tmp_${TmpWireCount.getCurrent + 1}"
        val tmpWireRhsContent: ST = if(isIntExp(intrinsic.rhs)) {
          st"${rhsST}"
        } else {
          rhsST
        }

        for(i <- 0 to (intrinsic.bytes - 1) by 1) {
          shareMemAssign = shareMemAssign :+
            st"${sharedMemName}(${tmpWireLhsST} + ${i}.U) := ${tmpWireRhsST}(${(i)*8+7}, ${(i)*8})"
        }

        val storeDataST = st"${if(anvil.typeBitSize(intrinsic.rhs.tipe) < (intrinsic.bytes * 8)) s".pad(${intrinsic.bytes * 8})" else ""}"

        intrinsicST =
          st"""
              |val ${tmpWireLhsST} = ${lhsOffsetST.render}
              |val ${tmpWireRhsST} = (${tmpWireRhsContent.render}${if(!anvil.config.splitTempSizes) "" else storeDataST.render}).asUInt
              |${(shareMemAssign, "\n")}
            """
        TmpWireCount.incCount()
        TmpWireCount.incCount()
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.RegisterAssign) => {
        val targetReg: String = if(intrinsic.isSP) "SP" else "DP"
        val updateContentST: ST = intrinsic.value match {
          case AST.IR.Exp.Int(_, v, _) => if (intrinsic.isInc) if (v < 0) st"${targetReg} - ${-v}.U" else st"${targetReg} + ${v}.U" else st"${processExpr(intrinsic.value, F)}"
          case _ => if(intrinsic.isInc) st"${targetReg} + ${processExpr(intrinsic.value, F)}" else st"${processExpr(intrinsic.value, F)}"
        }

        intrinsicST =
          st"""
              |${targetReg} := ${updateContentST.render}
            """
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

  @pure def processStmtAssign(a: AST.IR.Stmt.Assign): ST = {
    var assignST: ST = st""

    @strictpure def isIntrinsicLoad(e: AST.IR.Exp): B = e match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => T
      case _ => F
    }

    a match {
      case a: AST.IR.Stmt.Assign.Temp => {
        val regNo = a.lhs
        val lhsST: ST = if(!anvil.config.splitTempSizes)  st"${generalRegName}(${regNo}.U)" else st"${getGeneralRegName(a.rhs.tipe)}(${regNo}.U)"
        val rhsST = processExpr(a.rhs, F)
        if(isIntrinsicLoad(a.rhs)) {
          assignST =
            st"""
                |${lhsST} := Cat{
                |  ${rhsST.render}
                |}"""
        } else {
          var targetST = st""
          var finalST = st""
          if(DivRemLog.isCustomDivRem) {
            if(DivRemLog.isDiv) {
              if(DivRemLog.byteNum == 4) {
                val padStr: String = if(!anvil.config.splitTempSizes) ".pad(64)" else ""
                targetST = if(DivRemLog.isSigned) st"Mux(a_neg ^ b_neg, -divider32.io.quotient.asSInt${padStr}, divider32.io.quotient.asSInt${padStr})" else st"divider32.io.quotient"
              } else if(DivRemLog.byteNum == 8) {
                targetST = if(DivRemLog.isSigned) st"Mux(a_neg ^ b_neg, -divider64.io.quotient.asSInt, divider64.io.quotient.asSInt)" else st"divider64.io.quotient"
              } else {
                targetST = st""
              }
            } else {
              if(DivRemLog.byteNum == 4) {
                val padStr: String = if(!anvil.config.splitTempSizes) ".pad(64)" else ""
                targetST = if(DivRemLog.isSigned) st"Mux(a_neg, -divider32.io.remainder.asSInt${padStr}, divider32.io.remainder.asSInt${padStr})" else st"divider32.io.remainder"
              } else if(DivRemLog.byteNum == 8) {
                targetST = if(DivRemLog.isSigned) st"Mux(a_neg, -divider64.io.remainder.asSInt, divider64.io.remainder.asSInt)" else st"divider64.io.remainder"
              } else {
                targetST = st""
              }
            }
          } else {
            targetST = rhsST
          }

          val lhsContentST: ST = st"${if(isSignedExp(a.rhs)) "(" else ""}${targetST.render}${if(isSignedExp(a.rhs)) ").asUInt" else ""}"
          if(DivRemLog.isCustomDivRem) {
            if(DivRemLog.byteNum == 4) {
              finalST =
                st"""
                    |when(dividerStart & divider32.io.valid) {
                    |  ${lhsST} := ${if(!anvil.config.splitTempSizes) lhsContentST.render else s"${targetST.render}"}
                    |  ${processJumpIntrinsic(BlockLog.getBlock).render}
                    |  dividerStart := false.B
                    |}
                  """
            } else if(DivRemLog.byteNum == 8) {
              finalST =
                st"""
                    |when(dividerStart & divider64.io.valid) {
                    |  ${lhsST} := ${if(!anvil.config.splitTempSizes) lhsContentST.render else s"${targetST.render}"}
                    |  ${processJumpIntrinsic(BlockLog.getBlock).render}
                    |  dividerStart := false.B
                    |}
                  """
            } else {
              finalST = st""
            }
          } else {
            finalST = st"${lhsST} := ${if(!anvil.config.splitTempSizes) lhsContentST.render else s"${targetST.render}"}"
          }

          assignST =
            st"""
                |${if(DivRemLog.isCustomDivRem) DivRemLog.customDivRemST.render else ""}
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

  @strictpure def isBoolType(t: AST.Typed): B = t == AST.Typed.b
  @strictpure def is1BitVector(t: AST.Typed): B = anvil.subZOpt(t) match {
    case Some(info) => info.ast.isBitVector && info.ast.bitWidth == 1
    case _ => F
  }

  @pure def processExpr(exp: AST.IR.Exp, isForcedSign: B): ST = {
    var exprST = st""

    exp match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Register) => {
        exprST = if(intrinsic.isSP) st"SP" else st"DP"
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => {
        var rhsExprST = ISZ[ST]()
        val rhsExpr = processExpr(intrinsic.rhsOffset, F)
        for(i <- intrinsic.bytes-1 to 0 by -1) {
          if(i == 0) {
            rhsExprST = rhsExprST :+ st"${sharedMemName}(${rhsExpr.render} + ${i}.U)"
          } else {
            rhsExprST = rhsExprST :+ st"${sharedMemName}(${rhsExpr.render} + ${i}.U),"
          }
        }
        exprST =
          st"""
              |Cat(
              |  ${(rhsExprST, "\n")}
              |)${if(intrinsic.isSigned) ".asSInt" else ""}"""
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
      case exp: AST.IR.Exp.Type => {
        val splitStr: String = if(anvil.typeBitSize(exp.exp.tipe)== anvil.typeBitSize(exp.t)) "" else s".pad(${anvil.typeBitSize(exp.t)})"
        exprST = st"${processExpr(exp.exp, F)}${if(anvil.isSigned(exp.t)) ".asSInt" else ".asUInt"}${if(!anvil.config.splitTempSizes) "" else splitStr}"
      }
      case exp: AST.IR.Exp.Unary => {
        val variableST = processExpr(exp.exp, F)
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
        val leftST = st"${processExpr(exp.left, F).render}${if(isSIntOperation && (!isSignedExp(exp.left))) ".asSInt" else ""}"
        val rightST = st"${processExpr(exp.right, F).render}${if(isSIntOperation && (!isSignedExp(exp.right))) ".asSInt" else ""}"
        val expByteSize: Z = if(anvil.isScalar(exp.left.tipe)) anvil.typeByteSize(exp.left.tipe) else anvil.typeByteSize(anvil.spType)
        exp.op match {
          case AST.IR.Exp.Binary.Op.Add => {
            @pure def updateAdderInstance(signed: B, byteSize: Z, hashSMap: HashSMap[String, (ST, String)]): Z = {
              if(signed) {
                byteSize match {
                  case 1 => {
                    val res = adderSigned8Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderSigned8Instance = res._1
                    return res._2
                  }
                  case 2 => {
                    val res = adderSigned16Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderSigned16Instance = res._1
                    return res._2
                  }
                  case 4 => {
                    val res = adderSigned32Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderSigned32Instance = res._1
                    return res._2
                  }
                  case 8 => {
                    val res = adderSigned64Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderSigned64Instance = res._1
                    return res._2
                  }
                  case _ => return -1
                }
              } else {
                byteSize match {
                  case 1 => {
                    val res = adderUnsigned8Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderUnsigned8Instance = res._1
                    return res._2
                  }
                  case 2 => {
                    val res = adderUnsigned16Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderUnsigned16Instance = res._1
                    return res._2
                  }
                  case 4 => {
                    val res = adderUnsigned32Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderUnsigned32Instance = res._1
                    return res._2
                  }
                  case 8 => {
                    val res = adderUnsigned64Instance.populateInputs(BlockLog.getBlock.label, hashSMap)
                    adderUnsigned64Instance = res._1
                    return res._2
                  }
                  case _ => return -1
                }
              }
            }
            @pure def adderIPPortST(signed: B, byteSize: Z): ST = {
              var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
              if(signed) {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt") + "op" ~> (st"true.B", "Bool")
              } else {
                hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt") + "op" ~> (st"true.B", "Bool")
              }
              val instanceIndex: Z = updateAdderInstance(signed, byteSize, hashSMap)
              val resST: ST = if(signed) {
                byteSize match {
                  case 1 => st"${adderSigned8Instance.modInstanceName}_${instanceIndex}"
                  case 2 => st"${adderSigned16Instance.modInstanceName}_${instanceIndex}"
                  case 4 => st"${adderSigned32Instance.modInstanceName}_${instanceIndex}"
                  case 8 => st"${adderSigned64Instance.modInstanceName}_${instanceIndex}"
                  case _ => halt("not implemented in adderIPPortST")
                }
              } else {
                byteSize match {
                  case 1 => st"${adderUnsigned8Instance.modInstanceName}_${instanceIndex}"
                  case 2 => st"${adderUnsigned16Instance.modInstanceName}_${instanceIndex}"
                  case 4 => st"${adderUnsigned32Instance.modInstanceName}_${instanceIndex}"
                  case 8 => st"${adderUnsigned64Instance.modInstanceName}_${instanceIndex}"
                  case _ => halt("not implemented in adderIPPortST")
                }
              }

              return resST
            }
            if(anvil.config.alu) {
              exprST = st"${if(isSIntOperation) s"${adderIPPortST(T, expByteSize).render}.io.out" else s"${adderIPPortST(F, expByteSize).render}.io.out"}"
            } else {
              exprST = st"(${leftST.render} + ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Sub => {
            exprST = st"(${leftST.render} - ${rightST.render})"
          }
          case AST.IR.Exp.Binary.Op.Mul => {
            exprST = st"(${leftST.render} * ${rightST.render})"
          }
          case AST.IR.Exp.Binary.Op.Div => {
            if(anvil.config.customDivRem) {
              var signedNumberExtraST = st""
              if(anvil.isSigned(exp.left.tipe)) {
                if(anvil.typeByteSize(exp.left.tipe) == 4) {
                  signedNumberExtraST =
                    st"""
                        |val a_neg = ${leftST.render}(31)
                        |val b_neg = ${rightST.render}(31)
                        |val a_abs = Mux(a_neg, -${leftST.render}, ${leftST.render}).asUInt
                        |val b_abs = Mux(b_neg, -${rightST.render}, ${rightST.render}).asUInt
                    """
                } else if(anvil.typeByteSize(exp.left.tipe) == 8) {
                  signedNumberExtraST =
                    st"""
                        |val a_neg = ${leftST.render}(63)
                        |val b_neg = ${rightST.render}(63)
                        |val a_abs = Mux(a_neg, -${leftST.render}, ${leftST.render}).asUInt
                        |val b_abs = Mux(b_neg, -${rightST.render}, ${rightST.render}).asUInt
                    """
                } else {
                  signedNumberExtraST = st""
                }
              } else {
                signedNumberExtraST = st""
              }

              if(anvil.typeByteSize(exp.left.tipe) == 4) {
                DivRemLog.customDivRemST =
                  st"""
                      |${signedNumberExtraST.render}
                      |when(!dividerStart) {
                      |  divider32.io.a := ${if(anvil.isSigned(exp.left.tipe)) "a_abs" else s"${leftST.render}(31,0)"}
                      |  divider32.io.b := ${if(anvil.isSigned(exp.right.tipe)) "b_abs" else s"${rightST.render}(31,0)"}
                      |  divider32.io.start := true.B
                      |  dividerStart := true.B
                      |}
                    """
                DivRemLog.isCustomDivRem = T
                DivRemLog.byteNum = 4
                DivRemLog.isDiv = T
                DivRemLog.isSigned = anvil.isSigned(exp.left.tipe) | anvil.isSigned(exp.right.tipe)
              } else if(anvil.typeByteSize(exp.left.tipe) == 8) {
                DivRemLog.customDivRemST =
                  st"""
                      |${signedNumberExtraST.render}
                      |when(!dividerStart) {
                      |  divider64.io.a := ${if(anvil.isSigned(exp.left.tipe)) "a_abs" else s"${leftST.render}"}
                      |  divider64.io.b := ${if(anvil.isSigned(exp.right.tipe)) "b_abs" else s"${rightST.render}"}
                      |  divider64.io.start := true.B
                      |  dividerStart := true.B
                      |}
                    """
                DivRemLog.isCustomDivRem = T
                DivRemLog.byteNum = 8
                DivRemLog.isDiv = T
                DivRemLog.isSigned = anvil.isSigned(exp.left.tipe) | anvil.isSigned(exp.right.tipe)
              } else {
                halt(s"processExpr, you got an error about customDivRem")
              }
            } else {
              exprST = st"(${leftST.render} / ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.Rem => {
            if(anvil.config.customDivRem) {
              var signedNumberExtraST = st""
              if(anvil.isSigned(exp.left.tipe)) {
                if(anvil.typeByteSize(exp.left.tipe) == 4) {
                  signedNumberExtraST =
                    st"""
                        |val a_neg = ${leftST.render}(31)
                        |val b_neg = ${rightST.render}(31)
                        |val a_abs = Mux(a_neg, -${leftST.render}, ${leftST.render}).asUInt
                        |val b_abs = Mux(b_neg, -${rightST.render}, ${rightST.render}).asUInt
                    """
                } else if(anvil.typeByteSize(exp.left.tipe) == 8) {
                  signedNumberExtraST =
                    st"""
                        |val a_neg = ${leftST.render}(63)
                        |val b_neg = ${rightST.render}(63)
                        |val a_abs = Mux(a_neg, -${leftST.render}, ${leftST.render}).asUInt
                        |val b_abs = Mux(b_neg, -${rightST.render}, ${rightST.render}).asUInt
                    """
                } else {
                  signedNumberExtraST = st""
                }
              } else {
                signedNumberExtraST = st""
              }

              if(anvil.typeByteSize(exp.left.tipe) == 4) {
                DivRemLog.customDivRemST =
                  st"""
                      |${signedNumberExtraST.render}
                      |when(!dividerStart) {
                      |  divider32.io.a := ${if(anvil.isSigned(exp.left.tipe)) "a_abs" else s"${leftST.render}(31,0)"}
                      |  divider32.io.b := ${if(anvil.isSigned(exp.right.tipe)) "b_abs" else s"${rightST.render}(31,0)"}
                      |  divider32.io.start := true.B
                      |  dividerStart := true.B
                      |}
                    """
                DivRemLog.isCustomDivRem = T
                DivRemLog.byteNum = 4
                DivRemLog.isDiv = F
                DivRemLog.isSigned = anvil.isSigned(exp.left.tipe) | anvil.isSigned(exp.right.tipe)
              } else if(anvil.typeByteSize(exp.left.tipe) == 8) {
                DivRemLog.customDivRemST =
                  st"""
                      |${signedNumberExtraST.render}
                      |when(!dividerStart) {
                      |  divider64.io.a := ${if(anvil.isSigned(exp.left.tipe)) "a_abs" else s"${leftST.render}"}
                      |  divider64.io.b := ${if(anvil.isSigned(exp.right.tipe)) "b_abs" else s"${rightST.render}"}
                      |  divider64.io.start := true.B
                      |  dividerStart := true.B
                      |}
                    """
                DivRemLog.isCustomDivRem = T
                DivRemLog.byteNum = 8
                DivRemLog.isDiv = F
                DivRemLog.isSigned = anvil.isSigned(exp.left.tipe) | anvil.isSigned(exp.right.tipe)
              } else {
                halt(s"processExpr, you got an error about customDivRem")
              }
            } else {
              exprST = st"(${leftST.render} % ${rightST.render})"
            }
          }
          case AST.IR.Exp.Binary.Op.And => {
            exprST = st"(${leftST.render} & ${rightST.render})"
          }
          case AST.IR.Exp.Binary.Op.Or  => {
            exprST = st"(${leftST.render} | ${rightST.render})"
          }
          case AST.IR.Exp.Binary.Op.Xor => {
            exprST = st"(${leftST.render} ^ ${rightST.render})"
          }
          case AST.IR.Exp.Binary.Op.CondAnd => {
            if(isBoolType(exp.tipe)) {
              exprST = st"(${leftST.render} && ${rightST.render}).asUInt"
            } else if(is1BitVector(exp.tipe)) {
              exprST = st"(${leftST.render}.asBool && ${rightST.render}.asBool).asUInt"
            } else {
              halt(s"processExpr, you got an error about Op.CondAnd")
            }
          }
          case AST.IR.Exp.Binary.Op.CondOr => {
            if(isBoolType(exp.tipe)) {
              exprST = st"(${leftST.render} || ${rightST.render}).asUInt"
            } else if(is1BitVector(exp.tipe)) {
              exprST = st"(${leftST.render}.asBool || ${rightST.render}.asBool).asUInt"
            } else {
              halt(s"processExpr, you got an error about Op.CondOr")
            }
          }
          case AST.IR.Exp.Binary.Op.Eq => {
            exprST = st"(${leftST.render} === ${rightST.render}).asUInt"
          }
          case AST.IR.Exp.Binary.Op.Ne => {
            exprST = st"(${leftST.render} =/= ${rightST.render}).asUInt"
          }
          case AST.IR.Exp.Binary.Op.Ge => {
            exprST = st"(${leftST.render} >= ${rightST.render}).asUInt"
          }
          case AST.IR.Exp.Binary.Op.Gt => {
            exprST = st"(${leftST.render} > ${rightST.render}).asUInt"
          }
          case AST.IR.Exp.Binary.Op.Le => {
            exprST = st"(${leftST.render} <= ${rightST.render}).asUInt"
          }
          case AST.IR.Exp.Binary.Op.Lt => {
            exprST = st"(${leftST.render} < ${rightST.render}).asUInt"
          }
          case AST.IR.Exp.Binary.Op.Shr => {
            val rangeStr: String = if(anvil.typeBitSize(exp.right.tipe) > 20) "(6,0)" else ""
            val right: ST = if(anvil.isSigned(exp.right.tipe)) st"(${rightST.render}${rangeStr}.asUInt & \"b1111111\".U)" else st"(${rightST.render}${rangeStr} & \"b1111111\".U)"
            exprST = st"((${leftST.render})${if(anvil.isSigned(exp.left.tipe)) ".asSInt" else ".asUInt"} >> ${right.render})"
          }
          case AST.IR.Exp.Binary.Op.Ushr => {
            val rangeStr: String = if(anvil.typeBitSize(exp.right.tipe) > 20) "(6,0)" else ""
            val right: ST = if(anvil.isSigned(exp.right.tipe)) st"(${rightST.render}${rangeStr}.asUInt & \"b1111111\".U)" else st"(${rightST.render}${rangeStr} & \"b1111111\".U)"
            exprST = st"((${leftST.render})${if(anvil.isSigned(exp.left.tipe)) ".asSInt" else ".asUInt"} >> ${right.render})"
          }
          case AST.IR.Exp.Binary.Op.Shl => {
            val rangeStr: String = if(anvil.typeBitSize(exp.right.tipe) > 20) "(6,0)" else ""
            val right: ST = if(anvil.isSigned(exp.right.tipe)) st"(${rightST.render}${rangeStr}.asUInt & \"b1111111\".U)" else st"(${rightST.render}${rangeStr} & \"b1111111\".U)"
            exprST = st"((${leftST.render})${if(anvil.isSigned(exp.left.tipe)) ".asSInt" else ".asUInt"} << ${right.render})"
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

object HwSynthesizer {
  @record class AdderCounter(val anvil: Anvil, var sign: Z, var unsign: Z) extends MAnvilIRTransformer {
    override def post_langastIRExpBinary(o: AST.IR.Exp.Binary): MOption[AST.IR.Exp] = {
      if(o.op == AST.IR.Exp.Binary.Op.Add) {
        if(anvil.isSigned(o.left.tipe)) {
          sign = sign + 1
        } else {
          unsign = unsign + 1
        }
      }
      return MNone()
    }
  }
}