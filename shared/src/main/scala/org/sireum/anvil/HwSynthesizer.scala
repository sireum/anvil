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
import org.sireum.anvil.Util.{AnvilIRPrinter, constructLocalId, indexing, spType}
import org.sireum.lang.ast.{IR, Typed}
import org.sireum.lang.ast.IR.{Exp, Jump}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Resolver.{QName, addBuiltIns, typeParamMap}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Position

@sig trait IpType {

}
@datatype class BinaryIP(t: AST.IR.Exp.Binary.Op.Type, signed: B) extends IpType
@datatype class IntrinsicIP(t: AST.IR.Exp.Intrinsic.Type) extends IpType
@datatype class BlockMemoryIP() extends IpType
@datatype class LabelToFsmIP() extends IpType

@record @unclonable class InputMap(var ipMap: HashSMap[IpType, HashSMap[Z, HashSMap[String, ChiselModule.Input]]]) {
}

object InputMap {
  @strictpure def empty: InputMap = InputMap(HashSMap ++ ISZ[(IpType, HashSMap[Z, HashSMap[String, ChiselModule.Input]])](
    BinaryIP(AST.IR.Exp.Binary.Op.Add, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Add, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Sub, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Sub, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.And, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.And, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Or, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Or, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Xor, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Xor, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Eq, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Eq, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Ne, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Ne, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Gt, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Gt, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Ge, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Ge, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Lt, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Lt, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Le, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Le, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Shr, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Shr, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Shl, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Shl, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Ushr, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Ushr, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Mul, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Mul, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Div, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Div, F) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Rem, T) ~> HashSMap.empty,
    BinaryIP(AST.IR.Exp.Binary.Op.Rem, F) ~> HashSMap.empty,
    IntrinsicIP(HwSynthesizer.defaultIndexing) ~> HashSMap.empty,
    BlockMemoryIP() ~> HashSMap.empty,
    LabelToFsmIP() ~> HashSMap.empty
  ))
}

@datatype trait ChiselModule {
  @strictpure def signed: B
  @strictpure def moduleST: ST
  @strictpure def width: Z
  @strictpure def portList: HashSMap[String, String]
  @strictpure def expression: IpType
  @strictpure def moduleName: String
  @strictpure def instanceName: String
}

object ChiselModule {
  @datatype class StateValue(val state: Z, val value: String) {
  }

  @datatype class Input(val stateValue: StateValue, val portValueType: String) {}
}

@datatype class Adder(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: IpType,
                      val nonXilinxIP: B) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    if(nonXilinxIP)
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |    val io = IO(new Bundle{
          |        val a = Input(${portType}(width.W))
          |        val b = Input(${portType}(width.W))
          |        val start = Input(Bool())
          |        val out = Output(${portType}(width.W))
          |        val valid = Output(Bool())
          |    })
          |
          |    val state = RegInit(0.U(2.W))
          |    val regA = Reg(${portType}(width.W))
          |    val regB = Reg(${portType}(width.W))
          |    val result = Reg(${portType}(width.W))
          |
          |    io.valid := Mux(state === 2.U, true.B, false.B)
          |    io.out := Mux(state === 2.U, result, 0.${if(signedPort) "S" else "U"})
          |    switch(state) {
          |        is(0.U) {
          |            state := Mux(io.start, 1.U, 0.U)
          |            regA := Mux(io.start, io.a, regA)
          |            regB := Mux(io.start, io.b, regB)
          |        }
          |        is(1.U) {
          |            result := regA + regB
          |            state := 2.U
          |        }
          |        is(2.U) {
          |            state := 0.U
          |        }
          |    }
          |}
        """
    else
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |    val io = IO(new Bundle{
          |        val a = Input(${portType}(width.W))
          |        val b = Input(${portType}(width.W))
          |        val start = Input(Bool())
          |        val out = Output(${portType}(width.W))
          |        val valid = Output(Bool())
          |    })
          |  val adder = Module(new ${if (signedPort) "XilinxAdderSigned64Wrapper" else "XilinxAdderUnsigned64Wrapper"})
          |  adder.io.clk := clock.asBool
          |  adder.io.A := io.a
          |  adder.io.B := io.b
          |  adder.io.ce := io.start
          |  io.valid := adder.io.valid
          |  io.out := adder.io.S
          |}
        """
  }
}

@datatype class Subtractor(val signedPort: B,
                           val moduleDeclarationName: String,
                           val moduleInstanceName: String,
                           val widthOfPort: Z,
                           val exp: IpType,
                           val nonXilinxIP: B) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    if(nonXilinxIP)
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |    val io = IO(new Bundle{
          |        val a = Input(${portType}(width.W))
          |        val b = Input(${portType}(width.W))
          |        val start = Input(Bool())
          |        val out = Output(${portType}(width.W))
          |        val valid = Output(Bool())
          |    })
          |    val state = RegInit(0.U(2.W))
          |    val regA = Reg(${portType}(width.W))
          |    val regB = Reg(${portType}(width.W))
          |    val result = Reg(${portType}(width.W))
          |
          |    io.valid := Mux(state === 2.U, true.B, false.B)
          |    io.out := Mux(state === 2.U, result, 0.${if (signedPort) "S" else "U"})
          |    switch(state) {
          |        is(0.U) {
          |            state := Mux(io.start, 1.U, 0.U)
          |            regA := Mux(io.start, io.a, regA)
          |            regB := Mux(io.start, io.b, regB)
          |        }
          |        is(1.U) {
          |            result := regA - regB
          |            state := 2.U
          |        }
          |        is(2.U) {
          |            state := 0.U
          |        }
          |    }
          |}
        """
    else
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |    val io = IO(new Bundle{
          |        val a = Input(${portType}(width.W))
          |        val b = Input(${portType}(width.W))
          |        val start = Input(Bool())
          |        val out = Output(${portType}(width.W))
          |        val valid = Output(Bool())
          |    })
          |  val subtractor = Module(new ${if (signedPort) "XilinxSubtractorSigned64Wrapper" else "XilinxSubtractorUnsigned64Wrapper"})
          |  subtractor.io.clk := clock.asBool
          |  subtractor.io.A := io.a
          |  subtractor.io.B := io.b
          |  subtractor.io.ce := io.start
          |  io.valid := subtractor.io.valid
          |  io.out := subtractor.io.S
          |}
        """
  }
}

@datatype class Indexer(val signedPort: B,
                        val moduleDeclarationName: String,
                        val moduleInstanceName: String,
                        val widthOfPort: Z,
                        val exp: IpType,
                        val nonXilinxIP: B) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "baseOffset" ~> "UInt" + "dataOffset" ~> "UInt" + "index" ~> "UInt" +
      "elementSize" ~> "UInt" + "mask" ~> "UInt" + "ready" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure def indexAdderST: ST = {
    st"""
        |class IndexAdder(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(UInt(width.W))
        |        val b = Input(UInt(width.W))
        |        val start = Input(Bool())
        |        val out = Output(UInt(width.W))
        |        val valid = Output(Bool())
        |    })
        |
        |    val add = Module(new XilinxIndexAdderWrapper)
        |    add.io.clk := clock.asBool
        |    add.io.ce  := io.start
        |    add.io.A   := io.a
        |    add.io.B   := io.b
        |    io.valid   := add.io.valid
        |    io.out     := add.io.S
        |}
      """
  }
  @strictpure def indexMultiplierST: ST = {
    st"""
        |class IndexMultiplier(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a     = Input(UInt(width.W))
        |        val b     = Input(UInt(width.W))
        |        val start = Input(Bool())
        |        val out   = Output(UInt(width.W))
        |        val valid = Output(Bool())
        |    })
        |
        |    val mult = Module(new XilinxIndexMultiplierWrapper)
        |    mult.io.clk := clock.asBool
        |    mult.io.ce  := io.start
        |    mult.io.A   := io.a
        |    mult.io.B   := io.b
        |    io.valid    := mult.io.valid
        |    io.out      := mult.io.P
        |}
      """
  }
  @strictpure override def moduleST: ST = {
    if(nonXilinxIP)
      st"""
          |class Indexer(val width: Int = 16) extends Module {
          |    val io = IO(new Bundle{
          |        val baseOffset = Input(UInt(width.W))
          |        val dataOffset = Input(UInt(width.W))
          |        val index = Input(UInt(width.W))
          |        val elementSize = Input(UInt(width.W))
          |        val mask = Input(UInt(width.W))
          |        val ready = Input(Bool())
          |        val valid = Output(Bool())
          |        val out = Output(UInt(width.W))
          |    })
          |
          |    val stateReg = RegInit(0.U(2.W))
          |    switch(stateReg) {
          |        is(0.U) {
          |            stateReg := Mux(io.ready, 1.U, 0.U)
          |        }
          |        is(1.U) {
          |            stateReg := 2.U
          |        }
          |        is(2.U) {
          |            stateReg := 3.U
          |        }
          |        is(3.U) {
          |            stateReg := Mux(!io.ready, 0.U, 3.U)
          |        }
          |    }
          |
          |    io.valid := Mux(stateReg === 3.U, true.B, false.B)
          |
          |    val regBaseAddr = RegNext(io.baseOffset + io.dataOffset)
          |
          |    val regIndex = RegNext(io.index)
          |    val regMult = RegNext(regIndex * io.elementSize)
          |
          |    io.out := RegNext(regBaseAddr + (regMult & io.mask))
          |}
        """
    else
      st"""
          |${indexAdderST}
          |${indexMultiplierST}
          |class Indexer(val width: Int = 16) extends Module {
          |    val io = IO(new Bundle{
          |        val baseOffset = Input(UInt(width.W))
          |        val dataOffset = Input(UInt(width.W))
          |        val index = Input(UInt(width.W))
          |        val elementSize = Input(UInt(width.W))
          |        val mask = Input(UInt(width.W))
          |        val ready = Input(Bool())
          |        val valid = Output(Bool())
          |        val out = Output(UInt(width.W))
          |    })
          |
          |
          |    val sIdle :: sAdd1 :: sMult :: sAdd2 :: sEnd :: Nil = Enum(5)
          |    val stateReg        = RegInit(sIdle)
          |    val regBaseAddr     = Reg(UInt(width.W))
          |    val regIndex        = Reg(UInt(width.W))
          |    val regElementSize  = Reg(UInt(width.W))
          |    val regMult         = Reg(UInt(width.W))
          |    val regMask         = Reg(UInt(width.W))
          |    val result          = Reg(UInt(width.W))
          |
          |    val adder           = Module(new IndexAdder(width))
          |    val multiplier      = Module(new IndexMultiplier(width))
          |
          |    adder.io.a          := 0.U
          |    adder.io.b          := 0.U
          |    adder.io.start      := false.B
          |    multiplier.io.a     := 0.U
          |    multiplier.io.b     := 0.U
          |    multiplier.io.start := false.B
          |
          |    switch(stateReg) {
          |        is(sIdle) {
          |            stateReg       := Mux(io.ready, sAdd1, sIdle)
          |
          |            regIndex       := io.index
          |            regElementSize := io.elementSize
          |            regMask        := io.mask
          |        }
          |        is(sAdd1) {
          |            adder.io.a     := io.baseOffset
          |            adder.io.b     := io.dataOffset
          |            adder.io.start := true.B
          |
          |            when(adder.io.valid) {
          |                adder.io.start      := false.B
          |
          |                stateReg            := sMult
          |                regBaseAddr         := adder.io.out
          |            }
          |        }
          |        is(sMult) {
          |            multiplier.io.a     := regIndex
          |            multiplier.io.b     := regElementSize
          |            multiplier.io.start := true.B
          |
          |            when(multiplier.io.valid) {
          |                multiplier.io.start := false.B
          |                regMult             := multiplier.io.out & regMask
          |                stateReg            := sAdd2
          |            }
          |        }
          |        is(sAdd2) {
          |            adder.io.a     := regBaseAddr
          |            adder.io.b     := regMult
          |            adder.io.start := true.B
          |
          |            when(adder.io.valid) {
          |              adder.io.start := false.B
          |              result         := adder.io.out
          |              stateReg       := sEnd
          |            }
          |        }
          |        is(sEnd) {
          |            stateReg := sIdle
          |        }
          |    }
          |
          |    io.out   := Mux(stateReg === sEnd, result, 0.U)
          |    io.valid := Mux(stateReg === sEnd, true.B, false.B)
          |}
        """
  }
}

@datatype class And(val signedPort: B,
                    val moduleDeclarationName: String,
                    val moduleInstanceName: String,
                    val widthOfPort: Z,
                    val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a & io.b)
        |}
      """
  }
}

@datatype class Or(val signedPort: B,
                   val moduleDeclarationName: String,
                   val moduleInstanceName: String,
                   val widthOfPort: Z,
                   val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a | io.b)
        |}
      """
  }
}

@datatype class Xor(val signedPort: B,
                    val moduleDeclarationName: String,
                    val moduleInstanceName: String,
                    val widthOfPort: Z,
                    val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a ^ io.b)
        |}
      """
  }
}

@datatype class Eq(val signedPort: B,
                   val moduleDeclarationName: String,
                   val moduleInstanceName: String,
                   val widthOfPort: Z,
                   val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(Bool())
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a === io.b)
        |}
      """
  }
}

@datatype class Ne(val signedPort: B,
                   val moduleDeclarationName: String,
                   val moduleInstanceName: String,
                   val widthOfPort: Z,
                   val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(Bool())
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a =/= io.b)
        |}
      """
  }
}

@datatype class Ge(val signedPort: B,
                   val moduleDeclarationName: String,
                   val moduleInstanceName: String,
                   val widthOfPort: Z,
                   val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(Bool())
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a >= io.b)
        |}
      """
  }
}

@datatype class Gt(val signedPort: B,
                   val moduleDeclarationName: String,
                   val moduleInstanceName: String,
                   val widthOfPort: Z,
                   val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(Bool())
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a > io.b)
        |}
      """
  }
}

@datatype class Le(val signedPort: B,
                   val moduleDeclarationName: String,
                   val moduleInstanceName: String,
                   val widthOfPort: Z,
                   val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(Bool())
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a <= io.b)
        |}
      """
  }
}

@datatype class Lt(val signedPort: B,
                   val moduleDeclarationName: String,
                   val moduleInstanceName: String,
                   val widthOfPort: Z,
                   val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(Bool())
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(io.a < io.b)
        |}
      """
  }
}

@datatype class Shr(val signedPort: B,
                    val moduleDeclarationName: String,
                    val moduleInstanceName: String,
                    val widthOfPort: Z,
                    val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> "UInt" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(UInt(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(Mux(io.b > 64.U, ${if(signed) "io.a >> 64.U" else "0.U"}, io.a >> io.b(6,0)))
        |}
      """
  }
}

@datatype class Shl(val signedPort: B,
                    val moduleDeclarationName: String,
                    val moduleInstanceName: String,
                    val widthOfPort: Z,
                    val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> "UInt" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(UInt(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(Mux(io.b > 64.U, ${if(signed) "0.S" else "0.U"}, io.a << io.b(6,0)))
        |}
      """
  }
}

@datatype class Ushr(val signedPort: B,
                     val moduleDeclarationName: String,
                     val moduleInstanceName: String,
                     val widthOfPort: Z,
                     val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> "UInt" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(UInt(width.W))
        |        val start = Input(Bool())
        |        val valid = Output(Bool())
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.valid := RegNext(io.start)
        |    io.out := RegNext(Mux(io.b > 64.U, ${if(signed) "0.S" else "0.U"}, io.a${if(signed) ".asUInt" else ""} >> io.b(6,0))${if(signed) ".asSInt" else ""})
        |}
      """
  }
}

@datatype class Multiplier(val signedPort: B,
                           val moduleDeclarationName: String,
                           val moduleInstanceName: String,
                           val widthOfPort: Z,
                           val exp: IpType,
                           val nonXilinxIP: B) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    if(nonXilinxIP)
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |    val io = IO(new Bundle{
          |        val a = Input(${portType}(width.W))
          |        val b = Input(${portType}(width.W))
          |        val start = Input(Bool())
          |        val out = Output(${portType}(width.W))
          |        val valid = Output(Bool())
          |    })
          |
          |    io.out := io.a * io.b
          |    io.valid := RegNext(RegNext(true.B))
          |}
        """
    else
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |  val io = IO(new Bundle {
          |    val a = Input(${portType}(width.W))
          |    val b = Input(${portType}(width.W))
          |    val start = Input(Bool())
          |    val out = Output(${portType}(width.W))
          |    val valid = Output(Bool())
          |  })
          |  val div = Module(new ${if (signedPort) "XilinxMultiplierSigned64Wrapper" else "XilinxMultiplierUnsigned64Wrapper"})
          |  div.io.clk := clock.asBool
          |  div.io.a := io.a
          |  div.io.b := io.b
          |  div.io.ce := io.start
          |  io.valid := div.io.valid
          |  io.out := div.io.p
          |}
        """
  }
}

@datatype class Division(val signedPort: B,
                         val moduleDeclarationName: String,
                         val moduleInstanceName: String,
                         val widthOfPort: Z,
                         val exp: IpType,
                         val nonXilinxIP: B) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    if(nonXilinxIP)
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |  val io = IO(new Bundle {
        |    val a = Input(${portType}(width.W))
        |    val b = Input(${portType}(width.W))
        |    val start = Input(Bool())
        |    val valid = Output(Bool())
        |    val quotient = Output(${portType}(width.W))
        |    val remainder = Output(${portType}(width.W))
        |  })
        |
        |  val a_neg = io.a(width-1)
        |  val b_neg = io.b(width-1)
        |  val a_abs = Mux(a_neg, -io.a, io.a).asUInt
        |  val b_abs = Mux(b_neg, -io.b, io.b).asUInt
        |
        |  val dividend = RegInit(0.U(width.W))
        |  val divisor = RegInit(0.U(width.W))
        |  val quotient = RegInit(0.U(width.W))
        |  val remainder = RegInit(0.U(width.W))
        |  val count = RegInit((width - 1).U((1+log2Ceil(width)).W))
        |  val busy = RegInit(false.B)
        |
        |  when(io.start && !busy) {
        |    dividend := a_abs
        |    divisor := b_abs
        |    quotient := 0.U
        |    remainder := 0.U
        |    count := width.U
        |    busy := true.B
        |  } .elsewhen(busy) {
        |    when(count === 0.U) {
        |      count := width.U
        |      busy := false.B
        |    } .otherwise {
        |      val shifted = remainder << 1 | (dividend >> (width - 1))
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
        |  io.quotient := Mux(a_neg ^ b_neg, -quotient, quotient)${if(signedPort) ".asSInt" else ""}
        |  io.remainder := Mux(a_neg, -remainder, remainder)${if(signedPort) ".asSInt" else ""}
        |  io.valid := count === 0.U
        |}
      """
    else
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |  val io = IO(new Bundle {
          |    val a = Input(${portType}(width.W))
          |    val b = Input(${portType}(width.W))
          |    val start = Input(Bool())
          |    val valid = Output(Bool())
          |    val quotient = Output(${portType}(width.W))
          |    val remainder = Output(${portType}(width.W))
          |  })
          |  val div = Module(new ${if (signedPort) "XilinxDividerSigned64Wrapper" else "XilinxDividerUnsigned64Wrapper"})
          |  div.io.clock := clock.asBool
          |  div.io.resetn := !reset.asBool
          |  div.io.a := io.a
          |  div.io.b := io.b
          |  div.io.start := io.start
          |  io.valid := div.io.valid
          |  io.quotient := div.io.quotient
          |  io.remainder := div.io.remainder
          |}
        """
  }
}

@datatype class Remainder(val signedPort: B,
                         val moduleDeclarationName: String,
                         val moduleInstanceName: String,
                         val widthOfPort: Z,
                         val exp: IpType,
                         val nonXilinxIP: B) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    if(nonXilinxIP)
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |  val io = IO(new Bundle {
          |    val a = Input(${portType}(width.W))
          |    val b = Input(${portType}(width.W))
          |    val start = Input(Bool())
          |    val valid = Output(Bool())
          |    val quotient = Output(${portType}(width.W))
          |    val remainder = Output(${portType}(width.W))
          |  })
          |
          |  val a_neg = io.a(width-1)
          |  val b_neg = io.b(width-1)
          |  val a_abs = Mux(a_neg, -io.a, io.a).asUInt
          |  val b_abs = Mux(b_neg, -io.b, io.b).asUInt
          |
          |  val dividend = RegInit(0.U(width.W))
          |  val divisor = RegInit(0.U(width.W))
          |  val quotient = RegInit(0.U(width.W))
          |  val remainder = RegInit(0.U(width.W))
          |  val count = RegInit((width - 1).U((1+log2Ceil(width)).W))
          |  val busy = RegInit(false.B)
          |
          |  when(io.start && !busy) {
          |    dividend := a_abs
          |    divisor := b_abs
          |    quotient := 0.U
          |    remainder := 0.U
          |    count := width.U
          |    busy := true.B
          |  } .elsewhen(busy) {
          |    when(count === 0.U) {
          |      count := width.U
          |      busy := false.B
          |    } .otherwise {
          |      val shifted = remainder << 1 | (dividend >> (width - 1))
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
          |  io.quotient := Mux(a_neg ^ b_neg, -quotient, quotient)${if(signedPort) ".asSInt" else ""}
          |  io.remainder := Mux(a_neg, -remainder, remainder)${if(signedPort) ".asSInt" else ""}
          |  io.valid := count === 0.U
          |}
      """
    else
      st"""
          |class ${moduleName}(val width: Int = 64) extends Module {
          |  val io = IO(new Bundle {
          |    val a = Input(${portType}(width.W))
          |    val b = Input(${portType}(width.W))
          |    val start = Input(Bool())
          |    val valid = Output(Bool())
          |    val quotient = Output(${portType}(width.W))
          |    val remainder = Output(${portType}(width.W))
          |  })
          |  val div = Module(new ${if (signedPort) "XilinxDividerSigned64Wrapper" else "XilinxDividerUnsigned64Wrapper"})
          |  div.io.clock := clock.asBool
          |  div.io.resetn := !reset.asBool
          |  div.io.a := io.a
          |  div.io.b := io.b
          |  div.io.start := io.start
          |  io.valid := div.io.valid
          |  io.quotient := div.io.quotient
          |  io.remainder := div.io.remainder
          |}
        """
  }
}

@datatype class BlockMemory(val signedPort: B,
                            val moduleDeclarationName: String,
                            val moduleInstanceName: String,
                            val widthOfBRAM: Z,
                            val depthOfBRAM: Z,
                            val exp: IpType,
                            val nonXilinxIP: B,
                            val erase: B) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfBRAM
  @strictpure def depth: Z = depthOfBRAM
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "mode" ~> "UInt" + "readAddr" ~> "UInt" + "readOffset" ~> "UInt" +
      "readLen" ~> "UInt" + "writeAddr" ~> "UInt" + "writeOffset" ~> "UInt" + "writeLen" ~> "UInt" +
      "writeData" ~> "UInt" + "dmaSrcAddr" ~> "UInt" + "dmaDstAddr" ~> "UInt" + "dmaDstOffset" ~> "UInt" +
      "dmaSrcLen" ~> "UInt" + "dmaDstLen" ~> "UInt"
  }
  @strictpure override def expression: IpType = exp
  @strictpure def bramIpST: ST = {
    st"""
        |class BRAMIP (val depth: Int = 1024, val width: Int = 8) extends Module {
        |    val io = IO(new Bundle{
        |        val ena = Input(Bool())
        |        val wea = Input(Bool())
        |        val addra = Input(UInt(log2Ceil(depth).W))
        |        val dina = Input(UInt(width.W))
        |        val douta = Output(UInt(width.W))
        |
        |        val enb = Input(Bool())
        |        val web = Input(Bool())
        |        val addrb = Input(UInt(log2Ceil(depth).W))
        |        val dinb = Input(UInt(width.W))
        |        val doutb = Output(UInt(width.W))
        |    })
        |
        |    val mem = SyncReadMem(depth, UInt(width.W))
        |
        |    io.douta := 0.U
        |    io.doutb := 0.U
        |
        |    when(io.ena) {
        |      when(io.wea) {
        |        mem.write(io.addra, io.dina)
        |      } .otherwise {
        |        io.douta := mem.read(io.addra)
        |      }
        |    }
        |
        |    when(io.enb) {
        |      when(io.web) {
        |        mem.write(io.addrb, io.dinb)
        |      } .otherwise {
        |        io.doutb := mem.read(io.addrb)
        |      }
        |    }
        |}
      """
  }
  @strictpure override def moduleST: ST = {
    val bramInsST: ST =
      if(nonXilinxIP) st"val bram = Module(new BRAMIP(${depthOfBRAM}, 8))"
      else
        st"""
            |val bram = Module(new XilinxBRAMWrapper)
            |bram.io.clk := clock.asBool
          """
    val dmaZeroOutST: ST =
      if(erase)
        st"""
            |when((r_dmaDstCount >= io.dmaDstLen) & (r_dmaSrcCount >= io.dmaSrcLen)) {
            |  r_dmaState := sDmaDone
            |}
          """
      else
        st"""
            |when(r_dmaSrcCount >= io.dmaSrcLen) {
            |  r_dmaState := sDmaDone
            |}
          """
    st"""
        |${if(nonXilinxIP) bramIpST else st""}
        |class ${moduleName}(val depth: Int = ${depthOfBRAM}, val width: Int = ${widthOfBRAM}) extends Module {
        |  val io = IO(new Bundle {
        |    val mode = Input(UInt(2.W)) // 00 -> disable, 01 -> read, 10 -> write, 11 -> DMA
        |
        |    // Byte level read/write port
        |    val readAddr    = Input(UInt(log2Ceil(depth).W))
        |    val readOffset  = Input(UInt(log2Ceil(depth).W))
        |    val readLen     = Input(UInt(4.W))
        |    val readData    = Output(UInt(64.W))
        |    val readValid   = Output(Bool())
        |
        |    val writeAddr   = Input(UInt(log2Ceil(depth).W))
        |    val writeOffset = Input(UInt(log2Ceil(depth).W))
        |    val writeLen    = Input(UInt(4.W))
        |    val writeData   = Input(UInt(64.W))
        |    val writeValid  = Output(Bool())
        |
        |    // DMA
        |    val dmaSrcAddr   = Input(UInt(log2Ceil(depth).W))  // byte address
        |    val dmaDstAddr   = Input(UInt(log2Ceil(depth).W))  // byte address
        |    val dmaDstOffset = Input(UInt(log2Ceil(depth).W))
        |    val dmaSrcLen    = Input(UInt(log2Ceil(depth).W)) // byte count
        |    val dmaDstLen    = Input(UInt(log2Ceil(depth).W)) // byte count
        |    val dmaValid     = Output(Bool())
        |  })
        |
        |  ${bramInsST}
        |
        |  // BRAM default
        |  bram.io.ena := false.B
        |  bram.io.wea := false.B
        |  bram.io.addra := 0.U
        |  bram.io.dina := 0.U
        |
        |  bram.io.enb := false.B
        |  bram.io.web := false.B
        |  bram.io.addrb := 0.U
        |  bram.io.dinb := 0.U
        |
        |  val w_readEnable  = io.mode === 1.U
        |  val w_writeEnable = io.mode === 2.U
        |  val w_dmaEnable   = io.mode === 3.U
        |
        |  // === READ Operation ===
        |  val sReadIdle :: sReadFirst :: sReadTrans :: sReadEnd :: Nil = Enum(4)
        |
        |  val r_readCnt      = Reg(UInt(4.W))
        |  val r_lastReadCnt  = Reg(UInt(4.W))
        |  val r_readAddr     = Reg(UInt(log2Ceil(depth).W))
        |  val r_readState    = RegInit(sReadIdle)
        |  val r_readBytes    = Reg(Vec(8, UInt(8.W)))
        |
        |  switch(r_readState) {
        |    is(sReadIdle) {
        |      when(w_readEnable) {
        |        r_readState   := sReadFirst
        |        r_readCnt     := 0.U
        |        r_lastReadCnt := 0.U
        |        r_readAddr    := io.readAddr + io.readOffset
        |      }
        |      r_readBytes(0) := 0.U
        |      r_readBytes(1) := 0.U
        |      r_readBytes(2) := 0.U
        |      r_readBytes(3) := 0.U
        |      r_readBytes(4) := 0.U
        |      r_readBytes(5) := 0.U
        |      r_readBytes(6) := 0.U
        |      r_readBytes(7) := 0.U
        |    }
        |    is(sReadFirst) {
        |      bram.io.addra := r_readAddr
        |      bram.io.ena   := true.B
        |      bram.io.wea   := false.B
        |
        |      r_lastReadCnt := r_readCnt
        |      r_readCnt     := r_readCnt + 1.U
        |      r_readAddr    := r_readAddr + 1.U
        |      r_readState   := sReadTrans
        |    }
        |    is(sReadTrans) {
        |      r_readBytes(r_lastReadCnt) := bram.io.douta
        |
        |      bram.io.addra          := r_readAddr
        |      bram.io.ena            := true.B
        |      bram.io.wea            := false.B
        |
        |      r_lastReadCnt          := r_readCnt
        |      r_readCnt              := r_readCnt + 1.U
        |      r_readAddr             := r_readAddr + 1.U
        |
        |      r_readState            := Mux(io.readLen === 1.U, sReadEnd, Mux(r_readCnt < io.readLen, sReadTrans, sReadEnd))
        |    }
        |    is(sReadEnd) {
        |      r_readState   := sReadIdle
        |    }
        |  }
        |
        |  io.readData  := Cat(r_readBytes(7.U),
        |                      r_readBytes(6.U),
        |                      r_readBytes(5.U),
        |                      r_readBytes(4.U),
        |                      r_readBytes(3.U),
        |                      r_readBytes(2.U),
        |                      r_readBytes(1.U),
        |                      r_readBytes(0.U))
        |  io.readValid := Mux(r_readState === sReadEnd, true.B, false.B)
        |
        |  // === WRITE Operation ===
        |  val sWriteIdle :: sWriteTrans :: sWriteEnd :: Nil = Enum(3)
        |
        |  val r_writeCnt      = Reg(UInt(4.W))
        |  val r_writeAddr     = Reg(UInt(log2Ceil(depth).W))
        |  val r_writeState    = RegInit(sWriteIdle)
        |  val r_writeBytes    = Reg(Vec(8, UInt(8.W)))
        |  val r_writeLen      = Reg(UInt(4.W))
        |
        |  switch(r_writeState) {
        |    is(sWriteIdle) {
        |      when(w_writeEnable) {
        |        r_writeState      := sWriteTrans
        |        r_writeCnt        := 0.U
        |        r_writeAddr       := io.writeAddr + io.writeOffset
        |        r_writeLen        := io.writeLen - 1.U
        |
        |        r_writeBytes(0.U) := io.writeData(7, 0)
        |        r_writeBytes(1.U) := io.writeData(15, 8)
        |        r_writeBytes(2.U) := io.writeData(23, 16)
        |        r_writeBytes(3.U) := io.writeData(31, 24)
        |        r_writeBytes(4.U) := io.writeData(39, 32)
        |        r_writeBytes(5.U) := io.writeData(47, 40)
        |        r_writeBytes(6.U) := io.writeData(55, 48)
        |        r_writeBytes(7.U) := io.writeData(63, 56)
        |      }
        |    }
        |    is(sWriteTrans) {
        |      bram.io.addrb := r_writeAddr
        |      bram.io.enb   := true.B
        |      bram.io.web   := true.B
        |      bram.io.dinb  := r_writeBytes(r_writeCnt)
        |
        |      r_writeCnt    := r_writeCnt + 1.U
        |      r_writeAddr   := r_writeAddr + 1.U
        |      r_writeState  := Mux(r_writeCnt < r_writeLen, sWriteTrans, sWriteEnd)
        |    }
        |    is(sWriteEnd) {
        |      r_writeState  := sWriteIdle
        |    }
        |  }
        |
        |  io.writeValid := Mux(r_writeState === sWriteEnd, true.B, false.B)
        |
        |  // DMA logic
        |  val sDmaIdle :: sDmaFirstRead :: sDmaTrans :: sDmaDone :: Nil = Enum(4)
        |
        |  val r_dmaSrcCount = Reg(UInt(log2Ceil(depth).W))
        |  val r_dmaDstCount = Reg(UInt(log2Ceil(depth).W))
        |  val r_dmaSrcAddr  = Reg(UInt(log2Ceil(depth).W))
        |  val r_dmaDstAddr  = Reg(UInt(log2Ceil(depth).W))
        |  val r_dmaState    = RegInit(sDmaIdle)
        |
        |  switch(r_dmaState) {
        |    is(sDmaIdle) {
        |      when(w_dmaEnable) {
        |        r_dmaState    := Mux(io.dmaSrcLen === 0.U, sDmaTrans, sDmaFirstRead)
        |
        |        r_dmaSrcCount := 0.U
        |        r_dmaDstCount := 0.U
        |        r_dmaSrcAddr  := io.dmaSrcAddr
        |        r_dmaDstAddr  := io.dmaDstAddr + io.dmaDstOffset
        |      }
        |    }
        |    is(sDmaFirstRead) {
        |      r_dmaState    := sDmaTrans
        |
        |      // first read
        |      bram.io.addra := r_dmaSrcAddr
        |      bram.io.ena   := true.B
        |      bram.io.wea   := false.B
        |
        |      r_dmaSrcAddr  := r_dmaSrcAddr + 1.U
        |      r_dmaSrcCount := r_dmaSrcCount + 1.U
        |    }
        |    is(sDmaTrans) {
        |      // write the data from the read port
        |      when(r_dmaDstCount < io.dmaDstLen) {
        |        bram.io.addrb := r_dmaDstAddr
        |        bram.io.enb   := true.B
        |        bram.io.web   := true.B
        |        bram.io.dinb  := Mux(r_dmaDstCount >= r_dmaSrcCount, 0.U, bram.io.douta)
        |
        |        r_dmaDstAddr  := r_dmaDstAddr + 1.U
        |        r_dmaDstCount := r_dmaDstCount + 1.U
        |      }
        |
        |      // keep all the data from read port valid
        |      bram.io.ena   := true.B
        |      when(r_dmaSrcCount < io.dmaSrcLen) {
        |        bram.io.addra := r_dmaSrcAddr
        |        bram.io.wea   := false.B
        |
        |        r_dmaSrcAddr  := r_dmaSrcAddr + 1.U
        |        r_dmaSrcCount := r_dmaSrcCount + 1.U
        |      }
        |
        |      ${dmaZeroOutST.render}
        |    }
        |    is(sDmaDone) {
        |      r_dmaState := sDmaIdle
        |    }
        |  }
        |
        |  io.dmaValid := Mux(r_dmaState === sDmaDone, true.B, false.B)
        |}
    """
  }
}

@datatype class LabelToFsm(val signedPort: B,
                           val moduleDeclarationName: String,
                           val moduleInstanceName: String,
                           val widthOfPort: Z,
                           val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "label" ~> "UInt" + "originalCpIndex" ~> "UInt" + "start" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val numOfStates: Int, val cpMax: Int) extends Module {
        |    val cpWidth: Int = (numOfStates / cpMax) + (if(numOfStates % cpMax == 0) 0 else 1)
        |
        |    val io = IO(new Bundle{
        |        val start           = Input(Bool())
        |        val label           = Input(UInt(log2Up(numOfStates).W))
        |        val originalCpIndex = Input(UInt(log2Up(cpWidth).W))
        |        val valid           = Output(Bool())
        |        val isSameCpIndex   = Output(Bool())
        |        val cpIndex         = Output(UInt(log2Up(cpWidth).W))
        |        val stateIndex      = Output(UInt(log2Up(cpMax).W))
        |    })
        |
        |    val sIdle :: sShift :: sCompare :: sEnd :: Nil = Enum(4)
        |    val r_originalCpIndex = Reg(UInt(log2Up(cpWidth).W))
        |    val r_state           = RegInit(sIdle)
        |    val r_label           = Reg(UInt(log2Up(numOfStates).W))
        |    val r_cpIndex         = Reg(UInt(log2Up(cpWidth).W))
        |    val r_stateIndex      = Reg(UInt(log2Up(cpMax).W))
        |    val r_isSameCpIndex   = Reg(Bool())
        |
        |    switch(r_state) {
        |        is(sIdle) {
        |            r_state           := Mux(io.start, sShift, r_state)
        |            r_label           := io.label
        |            r_originalCpIndex := io.originalCpIndex
        |        }
        |        is(sShift) {
        |            r_cpIndex    := r_label >> log2Up(cpMax).U
        |            r_stateIndex := r_label(log2Up(cpMax) - 1, 0)
        |            r_state      := sCompare
        |        }
        |        is(sCompare) {
        |            r_isSameCpIndex := r_cpIndex === r_originalCpIndex
        |            r_state         := sEnd
        |        }
        |        is(sEnd) {
        |            r_state := sIdle
        |        }
        |    }
        |
        |    io.cpIndex       := r_cpIndex
        |    io.isSameCpIndex := r_isSameCpIndex
        |    io.stateIndex    := r_stateIndex
        |    io.valid         := r_state === sEnd
        |}
      """
  }
}

import HwSynthesizer._
@record class HwSynthesizer(val anvil: Anvil) {
  val sharedMemName: String = "arrayRegFiles"
  val generalRegName: String = "generalRegFiles"

  var ipAlloc: Util.IpAlloc = Util.IpAlloc(HashSMap.empty, HashSMap.empty, 0)
  val hwLog: HwSynthesizer.HwLog = HwSynthesizer.HwLog(0, MNone(), F, F, 0, 0, 0)

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
    BlockMemory(T, "BlockMemory", s"${sharedMemName}", 8, anvil.config.memory, BlockMemoryIP(), xilinxIPValid, anvil.config.erase),
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

  @pure def insDeclST(ip: IpType, numInstances: Z): ST = {
    val targetModule: ChiselModule = findChiselModule(ip).get
    val moduleInstances: ST = {
      val modDeclIns: ISZ[ST] = if(targetModule.expression == BlockMemoryIP()) {
        for (i <- 0 until numInstances) yield
          st"""val ${targetModule.instanceName} = Module(new ${targetModule.moduleName}(${targetModule.asInstanceOf[BlockMemory].depth}, ${targetModule.width}))"""
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
  def printProcedure(name: String, o: AST.IR.Procedure, output: Anvil.Output, maxRegisters: Util.TempVector): Unit = {
    if(anvil.config.useIP) {
      ipAlloc = Util.ipAlloc(anvil, o, anvil.config.ipMax)
    }
    var r = HashSMap.empty[ISZ[String], ST]
    val processedProcedureST = processProcedure(name, o, maxRegisters)
    r = r + ISZ(name) ~> o.prettyST(anvil.printer)

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
          |cpMax = ${anvil.config.cpMax}
        """

    output.add(T, ISZ("config.txt"), configST)
    output.add(T, ISZ("chisel/src/main/scala", s"chisel-${name}.scala"), processedProcedureST)
    output.add(T, ISZ("chisel", "build.sbt"), buildSbtST())
    output.add(T, ISZ("chisel", "project", "build.properties"), st"sbt.version=${output.sbtVersion}")

    if(!anvil.config.noXilinxIp) {
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
            |    if (ce)
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
            |    if (ce)
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
            |    if (ce)
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
            |    if (ce)
            |      valid_shift <= ${latencyST.render};
            |    else
            |      valid_shift <= 0;
            |  end
            |
            |  assign valid = valid_shift[LATENCY-1];
            |endmodule
          """
      }
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

      val backslash = "\\"
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
            |set_property -dict [list CONFIG.PSU__USE__M_AXI_GP0 {0} CONFIG.PSU__USE__M_AXI_GP1 {0} CONFIG.PSU__USE__M_AXI_GP2 {1}] [get_bd_cells zynq_ultra_ps_e_0]
            |
            |# /home/kejun/development/HLS_slang/zcu102/InsertSortIP/IP_dir
            |set_property  ip_repo_paths  $$IP_DIR [current_project]
            |update_ip_catalog
            |
            |# instantiate the generated IP
            |create_bd_cell -type ip -vlnv user.org:user:$$IP_NAME:1.0 GeneratedIP
            |apply_bd_automation -rule xilinx.com:bd_rule:axi4 -config { Clk_master {Auto} Clk_slave {Auto} Clk_xbar {Auto} Master {/zynq_ultra_ps_e_0/M_AXI_HPM0_LPD} Slave {/GeneratedIP/io_S_AXI} ddr_seg {Auto} intc_ip {New AXI Interconnect} master_apm {0}}  [get_bd_intf_pins GeneratedIP/io_S_AXI]
            |
            |set_property -dict [list CONFIG.PSU__CRL_APB__PL0_REF_CTRL__FREQMHZ $$FREQ_HZ] [get_bd_cells zynq_ultra_ps_e_0]
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
            |./auto_script.sh . ./ AXIWrapperChiselGenerated${name} TestSystem 100
          """

      val zynqCProgramST: ST =
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
            |    print("GeneralRegFileToBRAM Test\n\r");
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

      output.addPerm(T, ISZ("chisel/../", "test_many.sh"), testManyShScriptST, "+x")
      output.addPerm(T, ISZ("chisel/../", "auto_script.sh"), autoShScriptST, "+x")
      output.add(T, ISZ("chisel/../", "synthesize_zcu102_zynq.tcl"), synthImplST)
      output.add(T, ISZ("chisel/../", "ip_generation.tcl"), ipGenerationTclST)
      output.add(T, ISZ("chisel/src/main/resources/C", "zynq_program.c"), zynqCProgramST)
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxBUFGWrapper.v"), xilinxBUFGWrapperST)
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxAdderSigned64Wrapper.v"), xilinxAddSub64ST(T ,T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxAdderUnsigned64Wrapper.v"), xilinxAddSub64ST(T, F))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxSubtractorSigned64Wrapper.v"), xilinxAddSub64ST(F, T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxSubtractorUnsigned64Wrapper.v"), xilinxAddSub64ST(F, F))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxDividerSigned64Wrapper.v"), xilinxDiv64ST(T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxDividerUnsigned64Wrapper.v"), xilinxDiv64ST(F))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxMultiplierSigned64Wrapper.v"), xilinxMul64ST(T))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxMultiplierUnsigned64Wrapper.v"), xilinxMul64ST(F))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxBRAMWrapper.v"), xilinxBRAMWrapperST)
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxIndexAdderWrapper.v"), xilinxIndexAdderWrapperST(anvil.typeBitSize(spType)))
      output.add(T, ISZ("chisel/src/main/resources/verilog", "XilinxIndexMultiplierWrapper.v"), xilinxIndexMultiplierWrapperST(anvil.typeBitSize(spType)))
    }

    if (anvil.config.genVerilog) {
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
          |    Seq(ChiselGeneratorAnnotation(() => new AXIWrapperChiselGenerated${moduleName}()))
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

  @pure def processProcedure(name: String, o: AST.IR.Procedure, maxRegisters: Util.TempVector): ST = {

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

    @pure def procedureST(stateMachineST: ST, stateFunctionObjectST: ST): ST = {
      val adderSubtractorBlackBoxST =
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
      val multiplierBlackBoxST =
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
            |class XilinxMultiplierSigned64Wrapper extends BlackBox with HasBlackBoxResource {
            |  val io = IO(new Bundle {
            |    val clk = Input(Bool())
            |    val ce = Input(Bool())
            |    val a = Input(UInt(64.W))
            |    val b = Input(UInt(64.W))
            |    val valid = Output(Bool())
            |    val p = Output(UInt(64.W))
            |  })
            |
            |  addResource("/verilog/XilinxMultiplierSigned64Wrapper.v")
            |}
          """
      val divisionBlackBoxST =
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
      val memoryIpST =
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
      val indexIpST =
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
            |
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
      val BUFGST =
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

      val moduleDeclST: ST = {
        var moduleST: ISZ[ST] = ISZ()
        for(i <- 0 until ipModules.size) {
          moduleST = moduleST :+ ipModules(i).moduleST
        }

        if(!anvil.config.noXilinxIp) {
          moduleST = moduleST :+ divisionBlackBoxST
          moduleST = moduleST :+ multiplierBlackBoxST
          moduleST = moduleST :+ adderSubtractorBlackBoxST
          moduleST = moduleST :+ indexIpST
          if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
            moduleST = moduleST :+ memoryIpST
          }
        }

        if(anvil.config.genVerilog) {
          moduleST = moduleST :+ BUFGST
        }

        st"""${(moduleST, "\n")}"""
      }

      val instanceDeclST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for(entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insDeclST(b, entry._2)
        }
        instanceST = instanceST :+ insDeclST(IntrinsicIP(HwSynthesizer.defaultIndexing), ipAlloc.indexingAllocSize)
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
          instanceST = instanceST :+ insDeclST(BlockMemoryIP(), 1)
        }
        if(anvil.config.cpMax > 0) {
          instanceST = instanceST :+ insDeclST(LabelToFsmIP(), 1)
        }
        st"""${(instanceST, "\n")}"""
      }

      val instancePortFuncST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for(entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insPortFuncST(b, entry._2)
        }
        instanceST = instanceST :+ insPortFuncST(IntrinsicIP(HwSynthesizer.defaultIndexing), ipAlloc.indexingAllocSize)
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
          instanceST = instanceST :+ insPortFuncST(BlockMemoryIP(), 1)
        }
        if(anvil.config.cpMax > 0) {
          instanceST = instanceST :+ insPortFuncST(LabelToFsmIP(), 1)
        }
        st"""${(instanceST, "\n")}"""
      }

      val instancePortCallST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for(entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insPortCallST(b, entry._2)
        }
        instanceST = instanceST :+ insPortCallST(IntrinsicIP(HwSynthesizer.defaultIndexing), ipAlloc.indexingAllocSize)
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
          instanceST = instanceST :+ insPortCallST(BlockMemoryIP(), 1)
        }
        if(anvil.config.cpMax > 0) {
          instanceST = instanceST :+ insPortCallST(LabelToFsmIP(), 1)
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
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip)
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
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip)
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

      val horizontalChar: String = "|"
      val topModuleST: ST =
        st"""
            |class AXIWrapperChiselGenerated${name} (
            |               val C_S_AXI_DATA_WIDTH:  Int = 32,
            |               val C_S_AXI_ADDR_WIDTH:  Int = ${log2Up(anvil.config.memory)},
            |               val ARRAY_REG_WIDTH:     Int = 8,
            |               val ARRAY_REG_DEPTH:     Int = ${anvil.config.memory},
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
            |  })
            |
            |  val clk_out = Wire(Clock())
            |  val bufg = Module(new XilinxBUFGWrapper())
            |  bufg.io.I := clock
            |  clk_out := bufg.io.O
            |
            |  withClockAndReset(clk_out, !reset.asBool) {
            |    val mod = Module(new ${name}(
            |      C_S_AXI_DATA_WIDTH  = C_S_AXI_DATA_WIDTH,
            |      C_S_AXI_ADDR_WIDTH  = C_S_AXI_ADDR_WIDTH,
            |      ARRAY_REG_WIDTH     = ARRAY_REG_WIDTH,
            |      ARRAY_REG_DEPTH     = ARRAY_REG_DEPTH,
            |      ${if (!anvil.config.splitTempSizes) "GENERAL_REG_WIDTH    = GENERAL_REG_WIDTH," else ""}
            |      ${if (!anvil.config.splitTempSizes) s"GENERAL_REG_DEPTH    = GENERAL_REG_DEPTH," else ""}
            |      STACK_POINTER_WIDTH = STACK_POINTER_WIDTH,
            |      CODE_POINTER_WIDTH  = CODE_POINTER_WIDTH
            |    ))
            |
            |    mod.io.S_AXI_AWADDR  := io.S_AXI_AWADDR
            |    mod.io.S_AXI_AWPROT  := io.S_AXI_AWPROT
            |    mod.io.S_AXI_AWVALID := io.S_AXI_AWVALID
            |    io.S_AXI_AWREADY     := mod.io.S_AXI_AWREADY
            |
            |    mod.io.S_AXI_WDATA   := io.S_AXI_WDATA
            |    mod.io.S_AXI_WSTRB   := io.S_AXI_WSTRB
            |    mod.io.S_AXI_WVALID  := io.S_AXI_WVALID
            |    io.S_AXI_WREADY      := mod.io.S_AXI_WREADY
            |
            |    io.S_AXI_BRESP       := mod.io.S_AXI_BRESP
            |    io.S_AXI_BVALID      := mod.io.S_AXI_BVALID
            |    mod.io.S_AXI_BREADY  := io.S_AXI_BREADY
            |
            |    mod.io.S_AXI_ARADDR  := io.S_AXI_ARADDR
            |    mod.io.S_AXI_ARPROT  := io.S_AXI_ARPROT
            |    mod.io.S_AXI_ARVALID := io.S_AXI_ARVALID
            |    io.S_AXI_ARREADY     := mod.io.S_AXI_ARREADY
            |
            |    io.S_AXI_RDATA       := mod.io.S_AXI_RDATA
            |    io.S_AXI_RRESP       := mod.io.S_AXI_RRESP
            |    io.S_AXI_RVALID      := mod.io.S_AXI_RVALID
            |    mod.io.S_AXI_RREADY  := io.S_AXI_RREADY
            |  }
            |}
          """

      @pure def cpST: ST = {
        if(anvil.config.cpMax <= 0) {
          return st"""
                     |val CP = RegInit(2.U(CODE_POINTER_WIDTH.W))
                   """
        } else {
          val maxNumCps: Z = (hwLog.maxNumLabel / anvil.config.cpMax) + (if (hwLog.maxNumLabel % anvil.config.cpMax == 0) 0 else 1)
          var vecInitValue: ISZ[ST] = ISZ[ST]()
          var wireInitValue: ISZ[ST] = ISZ[ST]()

          for(i <- 0 until(maxNumCps)) {
            vecInitValue = vecInitValue :+ (
              if(maxNumCps == 1) st"val initVals = Seq(2.U(width.W))"
              else if(i == 0) st"val initVals = Seq(2.U(width.W)"
              else if(i == maxNumCps - 1) st", ${anvil.config.cpMax}.U(width.W))"
              else st", ${anvil.config.cpMax}.U(width.W)"
              )
          }

          for(i <- 0 until(maxNumCps)) {
            wireInitValue = wireInitValue :+ (
              if(maxNumCps == 1) st"val wireInitVals = Seq(${anvil.config.cpMax}.U(width.W))"
              else if(i == 0) st"val wireInitVals = Seq(${anvil.config.cpMax}.U(width.W)"
              else if(i == maxNumCps - 1) st", ${anvil.config.cpMax}.U(width.W))"
              else st", ${anvil.config.cpMax}.U(width.W)"
              )
          }

          return st"""
                     |val width: Int = log2Up(${anvil.config.cpMax + 1})
                     |${(vecInitValue, "")}
                     |val CP = VecInit(initVals.map(v => RegInit(v)))
                     |${(wireInitValue, "")}
                     |val nextCP = WireInit(VecInit(wireInitVals))
                     |"""
        }
      }

      val readyST: ST =
        if(anvil.config.cpMax <= 0)
          st"""
              |r_ready := Mux(CP === 0.U, 1.U, 0.U) | Mux(CP === 1.U, 2.U, 0.U)
            """
        else
          st"""
              |when(CP(0.U) === 0.U) {
              |  r_ready := 1.U
              |} .elsewhen(CP(0.U) === 1.U) {
              |  r_ready := 2.U
              |}
            """

      @pure def udpateCpsST: ST = {
        val maxNumCps: Z = (hwLog.maxNumLabel / anvil.config.cpMax) + (if (hwLog.maxNumLabel % anvil.config.cpMax == 0) 0 else 1)
        var iterateNextCPST: ISZ[ST] = ISZ[ST]()
        for(i <- 0 until maxNumCps) {
          iterateNextCPST = iterateNextCPST :+
            st"""
                |when(r_valid){
                |  CP(${i}.U) := RegNext(nextCP(${i}.U))
                |}"""
        }

        return st"""${(iterateNextCPST, "\n")}"""
      }

      return st"""
          |import chisel3._
          |import chisel3.util._
          |import chisel3.experimental._
          |
          |${if (anvil.config.useIP) moduleDeclST else st""}
          |
          |import ${name}._
          |class ${name} (val C_S_AXI_DATA_WIDTH:  Int = 32,
          |               val C_S_AXI_ADDR_WIDTH:  Int = ${log2Up(anvil.config.memory)},
          |               val ARRAY_REG_WIDTH:     Int = 8,
          |               val ARRAY_REG_DEPTH:     Int = ${anvil.config.memory},
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
          |  })
          |
          |  ${if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Ip) s"val ${sharedMemName} = RegInit(VecInit(Seq.fill(ARRAY_REG_DEPTH)(0.U(ARRAY_REG_WIDTH.W))))" else ""}
          |  // reg for general purpose
          |  ${if (!anvil.config.splitTempSizes) s"val ${generalRegName} = RegInit(VecInit(Seq.fill(GENERAL_REG_DEPTH)(0.U(GENERAL_REG_WIDTH.W))))" else s"${generalPurposeRegisterST.render}"}
          |  // reg for code pointer
          |  ${cpST.render}
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
          |  // registers for diff channels
          |  val r_s_axi_awready = Reg(Bool())
          |  val r_s_axi_wready  = Reg(Bool())
          |  val r_s_axi_bvalid  = Reg(Bool())
          |  val r_s_axi_arready = Reg(Bool())
          |  val r_s_axi_rdata   = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
          |  val r_s_axi_rvalid  = Reg(Bool())
          |
          |  val r_writeAddr     = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
          |  val r_writeData     = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
          |  val r_writeLen      = Reg(UInt((C_S_AXI_DATA_WIDTH / 8).W))
          |
          |  val r_readAddr      = Reg(UInt(C_S_AXI_ADDR_WIDTH.W))
          |  val r_readData      = Reg(UInt(C_S_AXI_DATA_WIDTH.W))
          |  val r_readLen       = Reg(UInt((C_S_AXI_DATA_WIDTH / 8).W))
          |
          |  // registers for valid and ready
          |  val r_valid = RegInit(false.B)
          |  val r_ready = RegInit(0.U(2.W))
          |  ${readyST.render}
          |
          |  ${if(anvil.config.useIP) instanceDeclST else st""}
          |  init(this)
          |
          |  ${if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) bramDefaultPortValueST.render else st""}
          |
          |  // write state machine
          |  val sWriteIdle :: sAWActive :: sWActive :: sBActive:: Nil = Enum(4)
          |  val writeState = RegInit(sWriteIdle)
          |
          |  r_s_axi_awready := Mux(io.S_AXI_AWVALID, true.B ,false.B)
          |  r_s_axi_wready  := Mux((writeState === sAWActive) & io.S_AXI_WVALID,  true.B, false.B)
          |  r_s_axi_bvalid  := Mux((writeState === sWActive)${if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) s"& ${sharedMemName}.io.writeValid" else ""}, true.B, false.B) |
          |                     Mux(io.S_AXI_WVALID & io.S_AXI_WREADY & (r_writeAddr === ${anvil.config.memory}.U), true.B, false.B)
          |  switch(writeState) {
          |    is(sWriteIdle) {
          |      writeState  := Mux(io.S_AXI_AWVALID & io.S_AXI_AWREADY, sAWActive, sWriteIdle)
          |      r_writeAddr := Mux(io.S_AXI_AWVALID & io.S_AXI_AWREADY, io.S_AXI_AWADDR, r_writeAddr)
          |    }
          |    is(sAWActive) {
          |      writeState  := Mux(io.S_AXI_WVALID & io.S_AXI_WREADY, sWActive, sAWActive)
          |      r_writeLen  := Mux(io.S_AXI_WVALID & io.S_AXI_WREADY, PopCount(io.S_AXI_WSTRB), r_writeLen)
          |      r_writeData := Mux(io.S_AXI_WVALID & io.S_AXI_WREADY, io.S_AXI_WDATA, r_writeData)
          |    }
          |    is(sWActive) {
          |      ${memWriteST}
          |    }
          |    is(sBActive) {
          |      writeState := Mux(io.S_AXI_BVALID & io.S_AXI_BREADY, sWriteIdle, sBActive)
          |    }
          |  }
          |
          |  // read state machine
          |  val sReadIdle :: sARActive :: sRActive :: sReadEnd :: Nil = Enum(4)
          |  val readState = RegInit(sReadIdle)
          |
          |  r_s_axi_arready := Mux(io.S_AXI_ARVALID, true.B, false.B)
          |  r_s_axi_rvalid  := Mux((readState === sRActive) ${if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) s" & (${sharedMemName}.io.readValid | r_readAddr === ${anvil.config.memory}.U)" else ""}, true.B, false.B)
          |  switch(readState) {
          |    is(sReadIdle) {
          |      readState := Mux(io.S_AXI_ARVALID, sARActive, sReadIdle)
          |    }
          |    is(sARActive) {
          |      readState := Mux(io.S_AXI_ARVALID & io.S_AXI_ARREADY, sRActive, sARActive)
          |
          |      when(io.S_AXI_ARVALID & io.S_AXI_ARREADY) {
          |        r_readAddr := io.S_AXI_ARADDR
          |      }
          |    }
          |    is(sRActive) {
          |      ${memReadST}
          |    }
          |    is(sReadEnd) {
          |      readState := Mux(io.S_AXI_RVALID & io.S_AXI_RREADY, sReadIdle, sReadEnd)
          |    }
          |  }
          |
          |  // write address channel
          |  io.S_AXI_AWREADY := r_s_axi_awready
          |
          |  // write channel
          |  io.S_AXI_WREADY  := r_s_axi_wready
          |
          |  // write response channel
          |  io.S_AXI_BRESP   := 0.U
          |  io.S_AXI_BVALID  := r_s_axi_bvalid
          |
          |  // read address channel
          |  io.S_AXI_ARREADY := r_s_axi_arready
          |
          |  // read channel
          |  io.S_AXI_RDATA   := r_s_axi_rdata
          |  io.S_AXI_RRESP   := 0.U
          |  io.S_AXI_RVALID  := r_s_axi_rvalid
          |
          |  ${if(anvil.config.cpMax <= 0) st"" else udpateCpsST}
          |  ${(stateMachineST, "")}
          |}
          |
          |object ${name} {
          |  def init(o: ${name}): Unit = {
          |    import o._
          |    ${if(anvil.config.useIP) instancePortFuncST else st""}
          |    ${if(anvil.config.useIP) instancePortCallST else st""}
          |  }
          |}
          |${(stateFunctionObjectST, "\n")}
          |
          |${if(anvil.config.genVerilog) topModuleST.render else st""}
          """
    }

    val basicBlockST = processBasicBlock(name, o.body.asInstanceOf[AST.IR.Body.Basic].blocks, hwLog)

    return procedureST(basicBlockST._1, basicBlockST._2)
  }

  @pure def processBasicBlock(name: String, bs: ISZ[AST.IR.BasicBlock], hwLog: HwSynthesizer.HwLog): (ST, ST) = {
    for(b <- bs) {
      if(b.label > hwLog.maxNumLabel) {
        hwLog.maxNumLabel = b.label
      }
    }

    val ipPortLogic = HwSynthesizer.IpPortAssign(anvil, ipAlloc, ISZ[ST](), ipModules, InputMap.empty, ISZ[ST](), ISZ[ST]())
    @pure def basicBlockST(grounds: HashSMap[Z, ST], functions: ISZ[ST]): (ST, ST) = {
      def chunk(start: Z, size: Z): ISZ[ST] = {
        var res = ISZ[ST]()
        var i = start
        val end: Z = if (start + size < grounds.size) start + size else grounds.size
        val entries = grounds.entries
        while (i < end) {
          val entry = entries(i)
          res = res :+ entry._2
          i = i + 1
        }
        return res
      }

      if(anvil.config.cpMax <= 0) {
        var chunks = ISZ[ISZ[ST]]()
        var idx: Z = 0

        if (grounds.size >= 999) {
          chunks = chunks :+ chunk(idx, 999)
          idx = idx + 999
          while (idx < grounds.size) {
            chunks = chunks :+ chunk(idx, 1000)
            idx = idx + 1000
          }
        } else {
          chunks = chunks :+ chunk(0, grounds.size)
        }

        var chunkST: ISZ[ST] = ISZ[ST]()
        for (i <- 0 until (chunks.size)) {
          if (i == 0) {
            chunkST = chunkST :+
              st"""
                  |def stateMachine_${i}(): Unit = {
                  |  switch(CP) {
                  |    is(2.U) {
                  |      CP := Mux(r_valid, 3.U, CP)
                  |    }
                  |    ${(chunks(i), "\n")}
                  |  }
                  |}
              """
          } else {
            chunkST = chunkST :+
              st"""
                  |def stateMachine_${i}(): Unit = {
                  |  switch(CP) {
                  |    ${(chunks(i), "\n")}
                  |  }
                  |}
              """
          }
        }

        var chunkFunST: ISZ[ST] = {
          for (i <- 0 until (chunks.size)) yield
            st"""
              |stateMachine_${i}()
            """
        }

        val stateMachineFunST: ST =
          st"""
              |def stateMachineAll(): Unit = {
              |  ${(chunkFunST, "\n")}
              |}
              |stateMachineAll()
          """

        chunkST = chunkST :+ stateMachineFunST

        return (
          st"""${(chunkST, "")}""",
          st"""${(functions, "")}"""
        )
      } else {
        var stateSTs: ISZ[ISZ[ST]] = ISZ[ISZ[ST]]()
        // for state machine 0
        stateSTs = stateSTs :+ ISZ[ST]()
        val initST = stateSTs(0) :+
          st"""
              |is(2.U) {
              |  nextCP(0.U) := Mux(r_valid, 3.U, 2.U)
              |}
              """
        stateSTs = stateSTs(0 ~> initST)

        for(pair <- grounds.entries) {
          val (label, blockST) = pair
          val (cpIdx, stateIdx) = getCpIndex(label)
          if(stateIdx == 0) {
            stateSTs = stateSTs :+ ISZ[ST]()
          }
          val updatedBlock = stateSTs(cpIdx) :+ st"${blockST}"
          stateSTs = stateSTs(cpIdx ~> updatedBlock)
        }

        var fmsSTs: ISZ[ST] = ISZ[ST]()
        for(i <- 0 until stateSTs.size) {
          fmsSTs = fmsSTs :+
            st"""
                |def stateMachine_${i}(): Unit = {
                |  switch(CP(${i}.U)) {
                |    ${(stateSTs(i), "\n")}
                |  }
                |}
                |stateMachine_${i}()
              """
        }

        return (
          st"""${(fmsSTs, "\n")}""",
          st"""${(functions, "")}"""
        )
      }
    }

    @pure def groundST(b: AST.IR.BasicBlock, ground: ST, jump: ST): (ST, ST) = {
      var commentST = ISZ[ST]()

      for(g <- b.grounds) {
        commentST = commentST :+ g.prettyST(anvil.printer)
      }
      commentST = commentST :+ b.jump.prettyST(anvil.printer)

      val jumpST: ST = {
        if(hwLog.isIndexerInCurrentBlock() && !hwLog.isMemCpyInCurrentBlock()) {
          val jST = processJumpIntrinsic(hwLog.stateBlock.get, ipPortLogic, hwLog)
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
                |  Block_${b.label}.block_${b.label}(this)
                |}
                """
          else
            st"""
                |is(${b.label % (anvil.config.cpMax)}.U) {
                |  Block_${b.label}.block_${b.label}(this)
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
        val processedGroundST = processGround(b.grounds, ipPortLogic, hwLog)
        var jump = processJumpIntrinsic(b, ipPortLogic, hwLog)
        if(ipPortLogic.whenCondST.nonEmpty) {
          jump =
            st"""
                |${if(anvil.config.cpMax <= 0) "" else s"nextCP(${getCpIndex(hwLog.currentLabel)._1}.U) := ${getCpIndex(hwLog.currentLabel)._2}.U"}
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

  @pure def processGround(gs: ISZ[AST.IR.Stmt.Ground], ipPortLogic: HwSynthesizer.IpPortAssign, hwLog: HwSynthesizer.HwLog): ST = {
    var groundST = ISZ[ST]()

    for(g <- gs) {
      g match {
        case g: AST.IR.Stmt.Assign => {
          groundST = groundST :+ processStmtAssign(g, ipPortLogic, hwLog)
        }
        case g: AST.IR.Stmt.Intrinsic => {
          groundST = groundST :+ processStmtIntrinsic(g, ipPortLogic, hwLog)
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

  @pure def processJumpIntrinsic(b: AST.IR.BasicBlock, ipPortLogic: HwSynthesizer.IpPortAssign, hwLog: HwSynthesizer.HwLog): ST = {
    var intrinsicST: ISZ[ST] = ISZ[ST]()
    val j = b.jump

    @pure def jumpSplitCpST(label: Z): ST = {
      var sts: ISZ[ST] = ISZ[ST]()
      val curCpIdx = getCpIndex(hwLog.currentLabel)._1
      val (nextCpIdx, nextPosIdx) = getCpIndex(label)
      if(curCpIdx == nextCpIdx) {
        sts = sts :+ st"nextCP(${curCpIdx}.U) := ${nextPosIdx}.U"
      } else {
        sts = sts :+ st"nextCP(${curCpIdx}.U) := ${anvil.config.cpMax}.U"
        sts = sts :+ st"nextCP(${nextCpIdx}.U) := RegNext(${nextPosIdx}.U)"
      }

      return st"${(sts, "\n")}"
    }

    j match {
      case AST.IR.Jump.Intrinsic(intrinsic: Intrinsic.GotoLocal) => {
        val targetAddrST: ST = processExpr(AST.IR.Exp.Temp(intrinsic.loc, anvil.cpType, intrinsic.pos), F, ipPortLogic, hwLog)
        if (intrinsic.isTemp) {
          if(anvil.config.cpMax <= 0) {
            intrinsicST = intrinsicST :+ st"CP := ${targetAddrST}"
          } else {
            var portSTs: ISZ[ST] = ISZ[ST]()
            val instanceName: String = getIpInstanceName(LabelToFsmIP()).get
            portSTs = portSTs :+ st"${instanceName}.io.label := ${targetAddrST}"
            portSTs = portSTs :+ st"${instanceName}.io.start := Mux(${instanceName}.io.valid, false.B, true.B)"
            portSTs = portSTs :+ st"${instanceName}.io.originalCpIndex := ${getCpIndex(hwLog.currentLabel)._1}.U"
            portSTs = portSTs :+
              st"""
                  |nextCP(${getCpIndex(hwLog.currentLabel)._1}.U) := ${getCpIndex(hwLog.currentLabel)._2}.U
                  |when(${instanceName}.io.valid) {
                  |  when(${instanceName}.io.isSameCpIndex) {
                  |    nextCP(${instanceName}.io.cpIndex) := ${instanceName}.io.stateIndex
                  |  } .otherwise {
                  |    nextCP(${getCpIndex(hwLog.currentLabel)._1}.U) := ${anvil.config.cpMax}.U
                  |    nextCP(${instanceName}.io.cpIndex) := RegNext(${instanceName}.io.stateIndex)
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
                |CP := Cat(
                |  ${(returnAddrST, "\n")}
                |)
            """
        }
      }
      case j: AST.IR.Jump.Goto => {
        if(anvil.config.cpMax <= 0) {
          intrinsicST = intrinsicST :+ st"CP := ${j.label}.U"
        } else {
          intrinsicST = intrinsicST :+ jumpSplitCpST(j.label)
        }
      }
      case j: AST.IR.Jump.If => {
        val cond = processExpr(j.cond, F, ipPortLogic, hwLog)
        if(anvil.config.cpMax <= 0) {
          intrinsicST = intrinsicST :+ st"CP := Mux((${cond.render}.asUInt) === 1.U, ${j.thenLabel}.U, ${j.elseLabel}.U)"
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
          case Some(x) => if(anvil.config.cpMax <= 0) st"CP := ${x}.U" else jumpSplitCpST(x)
          case None() => st""
        }

        var isStatementST = ISZ[ST]()
        for(i <- j.cases) {
          isStatementST = isStatementST :+
            st"""
                |is(${processExpr(i.value, F, ipPortLogic, hwLog).render}) {
                |  ${if(anvil.config.cpMax <=0) st"CP := ${i.label}.U" else jumpSplitCpST(i.label)}
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

  @pure def processStmtIntrinsic(i: AST.IR.Stmt.Intrinsic, ipPortLogic: HwSynthesizer.IpPortAssign, hwLog: HwSynthesizer.HwLog): ST = {
    var intrinsicST = st""

    i match {
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.TempLoad) => {
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
          val readAddrST: ST = processExpr(intrinsic.base, F, ipPortLogic, hwLog)
          val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
          val tempST: ST = st"${if (!anvil.config.splitTempSizes) s"${generalRegName}(${intrinsic.temp}.U)" else s"${getGeneralRegName(intrinsic.tipe)}(${intrinsic.temp}.U)"}"
          val byteST: ST = st"(${intrinsic.bytes * 8 - 1}, 0)"
          val signedST: ST = if(intrinsic.isSigned) st".asSInt" else st""
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
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Copy) => {
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val dmaDstAddrST: ST = processExpr(intrinsic.lbase, F, ipPortLogic, hwLog)
          val dmaDstOffsetST: ST = if(intrinsic.loffset < 0) st"(${intrinsic.loffset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.loffset}.U"
          val dmaSrcLenST: ST = processExpr(intrinsic.rhsBytes, F, ipPortLogic, hwLog)
          val dmaSrcAddrST: ST = processExpr(intrinsic.rhs, F, ipPortLogic, hwLog)
          val indexerInstanceName: String = getIpInstanceName(BlockMemoryIP()).get
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}.io.dmaValid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}.io.mode := 0.U"
          intrinsicST =
            st"""
                |${indexerInstanceName}.io.mode := 3.U
                |${indexerInstanceName}.io.dmaSrcAddr := ${dmaSrcAddrST.render}
                |${indexerInstanceName}.io.dmaDstAddr := ${dmaDstAddrST.render}
                |${indexerInstanceName}.io.dmaDstOffset := ${dmaDstOffsetST.render}
                |${indexerInstanceName}.io.dmaSrcLen := ${dmaSrcLenST.render}
                |${indexerInstanceName}.io.dmaDstLen := ${intrinsic.lhsBytes}.U
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
          val jumpST = processJumpIntrinsic(hwLog.stateBlock.get, ipPortLogic, hwLog)
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
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
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

  @pure def processStmtAssign(a: AST.IR.Stmt.Assign, ipPortLogic: HwSynthesizer.IpPortAssign, hwLog: HwSynthesizer.HwLog): ST = {
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
      case a: AST.IR.Stmt.Assign.Temp => {
        val regNo = a.lhs
        val lhsST: ST = if(!anvil.config.splitTempSizes)  st"${generalRegName}(${regNo}.U)" else st"${getGeneralRegName(a.rhs.tipe)}(${regNo}.U)"
        val rhsST = processExpr(a.rhs, F, ipPortLogic, hwLog)
        if(isIntrinsicLoad(a.rhs)) {
          if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
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

  @pure def processExpr(exp: AST.IR.Exp, isForcedSign: B, ipPortLogic: HwSynthesizer.IpPortAssign, hwLog: HwSynthesizer.HwLog): ST = {
    var exprST = st""

    exp match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Register) => {
        exprST = if(intrinsic.isSP) st"SP" else st"DP"
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => {
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ip) {
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

        if(anvil.config.cpMax > 0) {
          ipPortLogic.sts = ipPortLogic.sts :+ st"nextCP(${getCpIndex(hwLog.currentLabel)._1}.U) := ${getCpIndex(hwLog.currentLabel)._2}.U"
        }

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
            val allocIndex: Z = getIpAllocIndex(exp)
            var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
            if(isSIntOperation) {
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
          }
          case AST.IR.Exp.Binary.Op.Div => {
            val allocIndex: Z = getIpAllocIndex(exp)
            var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
            if(isSIntOperation) {
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
          }
          case AST.IR.Exp.Binary.Op.Rem => {
            val allocIndex: Z = getIpAllocIndex(exp)
            var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
            if(isSIntOperation) {
              hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "SInt") + "b" ~> (st"${rightST.render}", "SInt")
            } else {
              hashSMap = hashSMap + "a" ~> (st"${leftST.render}", "UInt") + "b" ~> (st"${rightST.render}", "UInt")
            }
            val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Rem, isSIntOperation)).get
            hashSMap = hashSMap + "start" ~> (st"Mux(${indexerInstanceName}_${allocIndex}.io.valid, false.B, true.B)", "Bool")
            insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Rem, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap, allocIndex), ipPortLogic.inputMap)
            ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
            exprST = st"${indexerInstanceName}_${allocIndex}.io.remainder"
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

object HwSynthesizer {
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
      if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Ip){
        binExp(o.lhsOffset)
      }
      return MAnvilIRTransformer.PreResultIntrinsicCopy
    }

    override def preIntrinsicTempLoad(o: Intrinsic.TempLoad): MAnvilIRTransformer.PreResult[Intrinsic.TempLoad] = {
      if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Ip) {
        binExp(o.rhsOffset)
      }
      return MAnvilIRTransformer.PreResultIntrinsicTempLoad
    }

    override def preIntrinsicLoad(o: Intrinsic.Load): MAnvilIRTransformer.PreResult[Intrinsic.Load] = {
      if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Ip) {
        binExp(o.rhsOffset)
      }
      return MAnvilIRTransformer.PreResultIntrinsicLoad
    }

    override def preIntrinsicStore(o: Intrinsic.Store): MAnvilIRTransformer.PreResult[Intrinsic.Store] = {
      if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Ip) {
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