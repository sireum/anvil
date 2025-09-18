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
import org.sireum.anvil._
import org.sireum.anvil.Anvil.VarInfo
import org.sireum.anvil.Util.{AnvilIRPrinter, constructLocalId, indexing, isTempGlobal, spType}
import org.sireum.lang.ast.{IR, Typed}
import org.sireum.lang.ast.IR.{Exp, Jump}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Resolver.{QName, addBuiltIns, typeParamMap}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Position

@sig trait ArbIpType {}
@datatype class ArbBinaryIP(t: AST.IR.Exp.Binary.Op.Type, signed: B) extends ArbIpType
@datatype class ArbIntrinsicIP(t: AST.IR.Exp.Intrinsic.Type) extends ArbIpType
@datatype class ArbBlockMemoryIP() extends ArbIpType

@datatype trait ArbIpModule {
  @strictpure def arbIpId: Z
  @strictpure def signed: B
  @strictpure def moduleST: ST
  @strictpure def width: Z
  // 1st element of [String, (Z, String)] -> port name
  // 1st element of (B, String) -> whether the current signal is control signal
  // 2nd element of (B, String) -> the type of the current port
  @strictpure def portList: HashSMap[String, (B, String)]
  @strictpure def expression: ArbIpType
  @strictpure def moduleName: String
  @strictpure def instanceName: String
}

object ArbIpModule {
  @datatype class StateValue(val state: Z, val value: String) {}
  @datatype class Input(val stateValue: StateValue, val portValueType: String) {}
}

@record @unclonable class ArbInputMap(var ipMap: HashSMap[ArbIpType, HashSMap[String, anvil.ArbIpModule.Input]]) {}

object ArbInputMap {
  @strictpure def empty: ArbInputMap = ArbInputMap(HashSMap ++ ISZ[(ArbIpType, HashSMap[String, ArbIpModule.Input])](
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Add, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Add, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Sub, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Sub, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.And, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.And, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Or, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Or, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Xor, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Xor, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Eq, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Eq, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Ne, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Ne, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Gt, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Gt, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Ge, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Ge, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Lt, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Lt, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Le, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Le, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Shr, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Shr, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Shl, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Shl, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Ushr, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Ushr, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Mul, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Mul, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Div, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Div, F) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Rem, T) ~> HashSMap.empty,
    ArbBinaryIP(AST.IR.Exp.Binary.Op.Rem, F) ~> HashSMap.empty,
    ArbIntrinsicIP(HwSynthesizer.defaultIndexing) ~> HashSMap.empty,
    ArbBlockMemoryIP() ~> HashSMap.empty
  ))
}

@datatype class ArbAdder(val signedPort: B,
                         val moduleDeclarationName: String,
                         val moduleInstanceName: String,
                         val widthOfPort: Z,
                         val exp: ArbIpType,
                         val nonXilinxIP: B,
                         val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
          |    val r_start      = RegInit(false.B)
          |    val r_start_next = RegInit(false.B)
          |    val r_busy       = RegInit(true.B)
          |
          |    r_start      := io.start
          |    r_start_next := r_start
          |    when(r_start & ~r_start_next) {
          |        r_busy := false.B
          |    } .elsewhen(io.valid) {
          |        r_busy := true.B
          |    }
          |
          |    io.valid := Mux(state === 2.U, true.B, false.B)
          |    io.out := Mux(state === 2.U, result, 0.${if(signedPort) "S" else "U"})
          |    switch(state) {
          |        is(0.U) {
          |            state := Mux(r_start & ~r_busy, 1.U, 0.U)
          |            regA := Mux(r_start, io.a, regA)
          |            regB := Mux(r_start, io.b, regB)
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
          |  adder.io.A := RegNext(io.a)
          |  adder.io.B := RegNext(io.b)
          |  adder.io.ce := RegNext(io.start)
          |  io.valid := RegNext(adder.io.valid)
          |  io.out := RegNext(adder.io.S)
          |}
        """
  }
}

@datatype class ArbSubtractor(val signedPort: B,
                              val moduleDeclarationName: String,
                              val moduleInstanceName: String,
                              val widthOfPort: Z,
                              val exp: ArbIpType,
                              val nonXilinxIP: B,
                              val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
          |    val r_start      = RegInit(false.B)
          |    val r_start_next = RegInit(false.B)
          |    val r_busy       = RegInit(true.B)
          |
          |    r_start      := io.start
          |    r_start_next := r_start
          |    when(r_start & ~r_start_next) {
          |        r_busy := false.B
          |    } .elsewhen(io.valid) {
          |        r_busy := true.B
          |    }
          |
          |    io.valid := Mux(state === 2.U, true.B, false.B)
          |    io.out := Mux(state === 2.U, result, 0.${if (signedPort) "S" else "U"})
          |    switch(state) {
          |        is(0.U) {
          |            state := Mux(r_start & ~r_busy, 1.U, 0.U)
          |            regA := Mux(r_start, io.a, regA)
          |            regB := Mux(r_start, io.b, regB)
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
          |  subtractor.io.A   := RegNext(io.a)
          |  subtractor.io.B   := RegNext(io.b)
          |  subtractor.io.ce  := RegNext(io.start)
          |  io.valid := RegNext(subtractor.io.valid)
          |  io.out   := RegNext(subtractor.io.S)
          |}
        """
  }
}

@datatype class ArbIndexer(val signedPort: B,
                           val moduleDeclarationName: String,
                           val moduleInstanceName: String,
                           val widthOfPort: Z,
                           val exp: ArbIpType,
                           val nonXilinxIP: B,
                           val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "baseOffset" ~> (F, "UInt".string) +
      "dataOffset" ~> (F, "UInt".string) +
      "index" ~> (F, "UInt".string) +
      "elementSize" ~> (F, "UInt".string) +
      "mask" ~> (F, "UInt".string) +
      "ready" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
          |    val r_start      = RegInit(false.B)
          |    val r_start_next = RegInit(false.B)
          |    val r_busy       = RegInit(true.B)
          |
          |    r_start      := io.ready
          |    r_start_next := r_start
          |    when(r_start & ~r_start_next) {
          |        r_busy := false.B
          |    } .elsewhen(io.valid) {
          |        r_busy := true.B
          |    }
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
          |    io.valid := Mux(stateReg === 3.U & ~r_busy, true.B, false.B)
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
          |    val sIdle :: sAdd1 :: sMult :: sAdd2 :: sEnd :: Nil = Enum(5)
          |    val stateReg        = RegInit(sIdle)
          |    val regBaseAddr     = Reg(UInt(width.W))
          |    val regIndex        = RegNext(io.index)
          |    val regElementSize  = RegNext(io.elementSize)
          |    val regMult         = Reg(UInt(width.W))
          |    val regMask         = RegNext(io.mask)
          |    val result          = RegInit(0.U(width.W))
          |    val regBaseOffset   = RegNext(io.baseOffset)
          |    val regDataOffset   = RegNext(io.dataOffset)
          |
          |    val adder           = Module(new IndexAdder(width))
          |    val multiplier      = Module(new IndexMultiplier(width))
          |
          |    val r_start      = RegInit(false.B)
          |    val r_start_next = RegInit(false.B)
          |    val r_busy       = RegInit(true.B)
          |
          |    r_start      := io.ready
          |    r_start_next := r_start
          |    when(r_start & ~r_start_next) {
          |        r_busy := false.B
          |    } .elsewhen(io.valid) {
          |        r_busy := true.B
          |    }
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
          |            stateReg       := Mux(r_start & ~r_busy, sAdd1, sIdle)
          |        }
          |        is(sAdd1) {
          |            adder.io.a     := regBaseOffset
          |            adder.io.b     := regDataOffset
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
          |    io.out   := Mux(stateReg === sEnd & ~r_busy, result, 0.U)
          |    io.valid := Mux(stateReg === sEnd & ~r_busy, true.B, false.B)
          |}
        """
  }
}

@datatype class ArbAnd(val signedPort: B,
                       val moduleDeclarationName: String,
                       val moduleInstanceName: String,
                       val widthOfPort: Z,
                       val exp: ArbIpType,
                       val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a & io.b)
        |}
      """
  }
}

@datatype class ArbOr(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: ArbIpType,
                      val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a | io.b)
        |}
      """
  }
}

@datatype class ArbXor(val signedPort: B,
                       val moduleDeclarationName: String,
                       val moduleInstanceName: String,
                       val widthOfPort: Z,
                       val exp: ArbIpType,
                       val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a ^ io.b)
        |}
      """
  }
}

@datatype class ArbEq(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: ArbIpType,
                      val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a === io.b)
        |}
      """
  }
}

@datatype class ArbNe(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: ArbIpType,
                      val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a =/= io.b)
        |}
      """
  }
}

@datatype class ArbGe(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: ArbIpType,
                      val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a >= io.b)
        |}
      """
  }
}

@datatype class ArbGt(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: ArbIpType,
                      val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a > io.b)
        |}
      """
  }
}

@datatype class ArbLe(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: ArbIpType,
                      val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a <= io.b)
        |}
      """
  }
}

@datatype class ArbLt(val signedPort: B,
                      val moduleDeclarationName: String,
                      val moduleInstanceName: String,
                      val widthOfPort: Z,
                      val exp: ArbIpType,
                      val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val r_start      = RegInit(false.B)
        |    val r_start_next = RegInit(false.B)
        |    val r_busy       = RegInit(true.B)
        |
        |    r_start      := io.start
        |    r_start_next := r_start
        |    when(r_start & ~r_start_next) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    io.valid := r_start & ~r_busy
        |    io.out := RegNext(io.a < io.b)
        |}
      """
  }
}

@datatype class ArbShr(val signedPort: B,
                       val moduleDeclarationName: String,
                       val moduleInstanceName: String,
                       val widthOfPort: Z,
                       val exp: ArbIpType,
                       val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, "UInt".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val big  = RegNext(io.b >= width.U)
        |    val sh   = RegNext(io.b(5, 0))
        |    val aU   = RegNext(io.a)
        |    ${if(signedPort) "val sign = RegNext(io.a(width-1) === 1.U)" else ""}
        |    ${if(signedPort) "val top  = RegNext(Mux(sign, (-1).S(64.W), 0.S(64.W)))" else ""}
        |
        |    val r_busy       = RegInit(true.B)
        |
        |    val v1 = RegNext(io.start, init=false.B)
        |    val v2 = RegNext(v1,       init=false.B)
        |    val v3 = RegNext(v2,       init=false.B)
        |    val v4 = RegNext(v3,       init=false.B)
        |    val v5 = RegNext(v4,       init=false.B)
        |    val v6 = RegNext(v5,       init=false.B)
        |    val v7 = RegNext(v6,       init=false.B)
        |    val v8 = RegNext(v7,       init=false.B)
        |    val v9 = RegNext(v8,       init=false.B)
        |
        |    when(v8 & ~v9) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    val s1 = RegNext(Mux(sh(0), aU >> 1, aU))
        |    val s2 = RegNext(Mux(sh(1), s1 >> 2, s1))
        |    val s3 = RegNext(Mux(sh(2), s2 >> 4, s2))
        |    val s4 = RegNext(Mux(sh(3), s3 >> 8, s3))
        |    val s5 = RegNext(Mux(sh(4), s4 >> 16, s4))
        |    val s6 = RegNext(Mux(sh(5), s5 >> 32, s5))
        |    val s7 = RegNext(Mux(big, ${if(signedPort) "top" else "0.U"}, s6))
        |
        |    io.valid := v1 & ~r_busy
        |    io.out := s7
        |}
      """
  }
}

@datatype class ArbShl(val signedPort: B,
                       val moduleDeclarationName: String,
                       val moduleInstanceName: String,
                       val widthOfPort: Z,
                       val exp: ArbIpType,
                       val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, "UInt".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val big = RegNext(io.b >= width.U)
        |    val sh  = RegNext(io.b(5, 0))
        |    val aU  = RegNext(io.a.asUInt)
        |
        |    val r_busy       = RegInit(true.B)
        |
        |    val v1 = RegNext(io.start, init=false.B)
        |    val v2 = RegNext(v1,       init=false.B)
        |    val v3 = RegNext(v2,       init=false.B)
        |    val v4 = RegNext(v3,       init=false.B)
        |    val v5 = RegNext(v4,       init=false.B)
        |    val v6 = RegNext(v5,       init=false.B)
        |    val v7 = RegNext(v6,       init=false.B)
        |    val v8 = RegNext(v7,       init=false.B)
        |    val v9 = RegNext(v8,       init=false.B)
        |
        |    when(v8 & ~v9) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    val s1 = RegNext(Mux(sh(0), aU << 1, aU))
        |    val s2 = RegNext(Mux(sh(1), s1 << 2, s1))
        |    val s3 = RegNext(Mux(sh(2), s2 << 4, s2))
        |    val s4 = RegNext(Mux(sh(3), s3 << 8, s3))
        |    val s5 = RegNext(Mux(sh(4), s4 << 16, s4))
        |    val s6 = RegNext(Mux(sh(5), s5 << 32, s5))
        |    val s7 = RegNext(Mux(big, 0.U, s6))
        |
        |    io.valid := v1 & ~r_busy
        |    io.out := s7${if(signedPort) ".asSInt" else ""}
        |}
      """
  }
}

@datatype class ArbUshr(val signedPort: B,
                        val moduleDeclarationName: String,
                        val moduleInstanceName: String,
                        val widthOfPort: Z,
                        val exp: ArbIpType,
                        val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, "UInt".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
        |    val big  = RegNext(io.b >= width.U)
        |    val sh   = RegNext(io.b(5, 0))
        |    val aU   = RegNext(io.a.asUInt)
        |
        |    val r_busy       = RegInit(true.B)
        |
        |    val v1 = RegNext(io.start, init=false.B)
        |    val v2 = RegNext(v1,       init=false.B)
        |    val v3 = RegNext(v2,       init=false.B)
        |    val v4 = RegNext(v3,       init=false.B)
        |    val v5 = RegNext(v4,       init=false.B)
        |    val v6 = RegNext(v5,       init=false.B)
        |    val v7 = RegNext(v6,       init=false.B)
        |    val v8 = RegNext(v7,       init=false.B)
        |    val v9 = RegNext(v8,       init=false.B)
        |
        |    when(v8 & ~v9) {
        |        r_busy := false.B
        |    } .elsewhen(io.valid) {
        |        r_busy := true.B
        |    }
        |
        |    val s1 = RegNext(Mux(sh(0), aU >> 1, aU))
        |    val s2 = RegNext(Mux(sh(1), s1 >> 2, s1))
        |    val s3 = RegNext(Mux(sh(2), s2 >> 4, s2))
        |    val s4 = RegNext(Mux(sh(3), s3 >> 8, s3))
        |    val s5 = RegNext(Mux(sh(4), s4 >> 16, s4))
        |    val s6 = RegNext(Mux(sh(5), s5 >> 32, s5))
        |    val s7 = RegNext(Mux(big, 0.U, s6))
        |
        |    io.valid := v1 & ~r_busy
        |    io.out := s7${if(signedPort) ".asSInt" else ""}
        |}
      """
  }
}

@datatype class ArbMultiplier(val signedPort: B,
                              val moduleDeclarationName: String,
                              val moduleInstanceName: String,
                              val widthOfPort: Z,
                              val exp: ArbIpType,
                              val nonXilinxIP: B,
                              val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
          |    val r_start      = RegInit(false.B)
          |    val r_start_next = RegInit(false.B)
          |    val r_busy       = RegInit(true.B)
          |
          |    r_start      := io.start
          |    r_start_next := r_start
          |    when(r_start & ~r_start_next) {
          |        r_busy := false.B
          |    } .elsewhen(io.valid) {
          |        r_busy := true.B
          |    }
          |
          |    io.out := io.a * io.b
          |    io.valid := r_start & ~r_busy
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

@datatype class ArbDivision(val signedPort: B,
                            val moduleDeclarationName: String,
                            val moduleInstanceName: String,
                            val widthOfPort: Z,
                            val exp: ArbIpType,
                            val nonXilinxIP: B,
                            val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
          |  val r_start      = RegInit(false.B)
          |  val r_start_next = RegInit(false.B)
          |  val r_busy       = RegInit(true.B)
          |
          |  r_start      := io.start
          |  r_start_next := r_start
          |  when(r_start & ~r_start_next) {
          |      r_busy := false.B
          |  } .elsewhen(io.valid) {
          |      r_busy := true.B
          |  }
          |
          |  io.quotient := Mux(a_neg ^ b_neg, -quotient, quotient)${if(signedPort) ".asSInt" else ""}
          |  io.remainder := Mux(a_neg, -remainder, remainder)${if(signedPort) ".asSInt" else ""}
          |  io.valid := (count === 0.U) & ~r_busy
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

@datatype class ArbRemainder(val signedPort: B,
                             val moduleDeclarationName: String,
                             val moduleInstanceName: String,
                             val widthOfPort: Z,
                             val exp: ArbIpType,
                             val nonXilinxIP: B,
                             val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  val portType: String = if(signedPort) "SInt" else "UInt"
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    HashSMap.empty[String, (B, String)] +
      "a" ~> (F, s"${portType}".string) +
      "b" ~> (F, s"${portType}".string) +
      "start" ~> (T, "Bool".string)
  }
  @strictpure override def expression: ArbIpType = exp
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
          |  val r_start      = RegInit(false.B)
          |  val r_start_next = RegInit(false.B)
          |  val r_busy       = RegInit(true.B)
          |
          |  r_start      := io.start
          |  r_start_next := r_start
          |  when(r_start & ~r_start_next) {
          |      r_busy := false.B
          |  } .elsewhen(io.valid) {
          |      r_busy := true.B
          |  }
          |
          |  io.quotient := Mux(a_neg ^ b_neg, -quotient, quotient)${if(signedPort) ".asSInt" else ""}
          |  io.remainder := Mux(a_neg, -remainder, remainder)${if(signedPort) ".asSInt" else ""}
          |  io.valid := (count === 0.U) & ~r_busy
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

@datatype class ArbBlockMemory(val signedPort: B,
                               val moduleDeclarationName: String,
                               val moduleInstanceName: String,
                               val widthOfBRAM: Z,
                               val depthOfBRAM: Z,
                               val exp: ArbIpType,
                               val memoryType: Anvil.Config.MemoryAccess.Type,
                               val genVerilog: B,
                               val erase: B,
                               val aligned: B,
                               val arbID: Z) extends ArbIpModule {
  @strictpure override def arbIpId: Z = arbID
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfBRAM
  @strictpure def depth: Z = depthOfBRAM
  @strictpure override def portList: HashSMap[String, (B, String)] = {
    memoryType match {
      case Anvil.Config.MemoryAccess.BramNative =>
        HashSMap.empty[String, (B, String)] +
          "mode" ~> (T, "UInt".string) +
          "readAddr" ~> (F, "UInt".string) +
          "readOffset" ~> (F, "UInt".string) +
          "readLen" ~> (F, "UInt".string) +
          "writeAddr" ~> (F, "UInt".string) +
          "writeOffset" ~> (F, "UInt".string) +
          "writeLen" ~> (F, "UInt".string) +
          "writeData" ~> (F, "UInt".string) +
          "dmaSrcAddr" ~> (F, "UInt".string) +
          "dmaDstAddr" ~> (F, "UInt".string) +
          "dmaDstOffset" ~> (F, "UInt".string) +
          "dmaSrcLen" ~> (F, "UInt".string)+
          "dmaDstLen" ~> (F, "UInt".string)
      case Anvil.Config.MemoryAccess.Default =>
        halt("not impl default in ArbBlockMemory")
      case _ =>
        if(!aligned)
          HashSMap.empty[String, (B, String)] +
            "mode" ~> (T, "UInt".string) +
            "readAddr" ~> (F, "UInt".string) +
            "readOffset" ~> (F, "UInt".string) +
            "readLen" ~> (F, "UInt".string) +
            "writeAddr" ~> (F, "UInt".string) +
            "writeOffset" ~> (F, "UInt".string) +
            "writeLen" ~> (F, "UInt".string) +
            "writeData" ~> (F, "UInt".string) +
            "dmaSrcAddr" ~> (F, "UInt".string) +
            "dmaDstAddr" ~> (F, "UInt".string) +
            "dmaDstOffset" ~> (F, "UInt".string) +
            "dmaSrcLen" ~> (F, "UInt".string)+
            "dmaDstLen" ~> (F, "UInt".string)
        else
          HashSMap.empty[String, (B, String)] +
            "mode" ~> (T, "UInt".string) +
            "readAddr" ~> (F, "UInt".string) +
            "writeAddr" ~> (F, "UInt".string) +
            "writeData" ~> (F, "UInt".string) +
            "dmaSrcAddr" ~> (F, "UInt".string) +
            "dmaDstAddr" ~> (F, "UInt".string) +
            "dmaSrcLen" ~> (F, "UInt".string) +
            "dmaDstLen" ~> (F, "UInt".string)
    }
  }
  @strictpure override def expression: ArbIpType = exp
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
  @pure override def moduleST: ST = {
    val bramInsST: ST =
      if(!genVerilog) st"val bram = Module(new BRAMIP(${depthOfBRAM}, 8))"
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

    val bramModuleST: ST =
      st"""
          |${if(!genVerilog) bramIpST else st""}
          |class ${moduleName}(val width: Int = ${widthOfBRAM}, val depth: Int = ${depthOfBRAM}) extends Module {
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

    val ddrModuleST: ST =
      st"""
          |class ${moduleName}(val C_M_AXI_DATA_WIDTH: Int,
          |                    val C_M_AXI_ADDR_WIDTH: Int,
          |                    val MEMORY_DEPTH: Int,
          |                    val C_M_TARGET_SLAVE_BASE_ADDR: BigInt = 0x0) extends Module {
          |
          |  val io = IO(new Bundle{
          |    val mode = Input(UInt(2.W)) // 00 -> disable, 01 -> read, 10 -> write, 11 -> DMA
          |
          |    // Byte level read/write port
          |    val readAddr    = Input(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val readOffset  = Input(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val readLen     = Input(UInt(log2Up(C_M_AXI_DATA_WIDTH / 8 + 1).W))
          |    val readData    = Output(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val readValid   = Output(Bool())
          |
          |    val writeAddr   = Input(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val writeOffset = Input(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val writeLen    = Input(UInt(log2Up(C_M_AXI_DATA_WIDTH / 8 + 1).W))
          |    val writeData   = Input(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val writeValid  = Output(Bool())
          |
          |    // DMA
          |    val dmaSrcAddr   = Input(UInt(C_M_AXI_ADDR_WIDTH.W))  // byte address
          |    val dmaDstAddr   = Input(UInt(C_M_AXI_ADDR_WIDTH.W))  // byte address
          |    val dmaDstOffset = Input(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val dmaSrcLen    = Input(UInt(log2Up(MEMORY_DEPTH).W)) // byte count
          |    val dmaDstLen    = Input(UInt(log2Up(MEMORY_DEPTH).W)) // byte count
          |    val dmaValid     = Output(Bool())
          |
          |    // master write address channel
          |    val M_AXI_AWID    = Output(UInt(1.W))
          |    val M_AXI_AWADDR  = Output(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val M_AXI_AWLEN   = Output(UInt(8.W))
          |    val M_AXI_AWSIZE  = Output(UInt(3.W))
          |    val M_AXI_AWBURST = Output(UInt(2.W))
          |    val M_AXI_AWLOCK  = Output(Bool())
          |    val M_AXI_AWCACHE = Output(UInt(4.W))
          |    val M_AXI_AWPROT  = Output(UInt(3.W))
          |    val M_AXI_AWQOS   = Output(UInt(4.W))
          |    val M_AXI_AWUSER  = Output(UInt(1.W))
          |    val M_AXI_AWVALID = Output(Bool())
          |    val M_AXI_AWREADY = Input(Bool())
          |
          |    // master write data channel
          |    val M_AXI_WDATA  = Output(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val M_AXI_WSTRB  = Output(UInt((C_M_AXI_DATA_WIDTH/8).W))
          |    val M_AXI_WLAST  = Output(Bool())
          |    val M_AXI_WUSER  = Output(UInt(1.W))
          |    val M_AXI_WVALID = Output(Bool())
          |    val M_AXI_WREADY = Input(Bool())
          |
          |    // master write response channel
          |    val M_AXI_BID    = Input(UInt(1.W))
          |    val M_AXI_BRESP  = Input(UInt(2.W))
          |    val M_AXI_BUSER  = Input(UInt(1.W))
          |    val M_AXI_BVALID = Input(Bool())
          |    val M_AXI_BREADY = Output(Bool())
          |
          |    // master read address channel
          |    val M_AXI_ARID    = Output(UInt(1.W))
          |    val M_AXI_ARADDR  = Output(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val M_AXI_ARLEN   = Output(UInt(8.W))
          |    val M_AXI_ARSIZE  = Output(UInt(3.W))
          |    val M_AXI_ARBURST = Output(UInt(2.W))
          |    val M_AXI_ARLOCK  = Output(Bool())
          |    val M_AXI_ARCACHE = Output(UInt(4.W))
          |    val M_AXI_ARPROT  = Output(UInt(3.W))
          |    val M_AXI_ARQOS   = Output(UInt(4.W))
          |    val M_AXI_ARUSER  = Output(UInt(1.W))
          |    val M_AXI_ARVALID = Output(Bool())
          |    val M_AXI_ARREADY = Input(Bool())
          |
          |    // master read data channel
          |    val M_AXI_RID    = Input(UInt(1.W))
          |    val M_AXI_RDATA  = Input(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val M_AXI_RRESP  = Input(UInt(2.W))
          |    val M_AXI_RLAST  = Input(Bool())
          |    val M_AXI_RUSER  = Input(UInt(1.W))
          |    val M_AXI_RVALID = Input(Bool())
          |    val M_AXI_RREADY = Output(Bool())
          |  })
          |
          |  // registers for diff channels
          |  // write address channel
          |  val r_m_axi_awvalid = RegInit(false.B)
          |  val r_m_axi_awaddr  = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |  val r_m_axi_awlen   = RegInit(0.U(8.W))
          |
          |  // write data channel
          |  val r_m_axi_wvalid  = RegInit(false.B)
          |  val r_m_axi_wdata   = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_m_axi_wstrb   = RegInit(0.U((C_M_AXI_DATA_WIDTH/8).W))
          |  val r_m_axi_wlast   = RegInit(false.B)
          |  val r_w_valid       = RegInit(false.B)
          |
          |  // write response channel
          |  val r_m_axi_bready  = RegInit(false.B)
          |  val r_b_valid       = RegInit(false.B)
          |
          |  // read address channel
          |  val r_m_axi_arvalid = RegInit(false.B)
          |  val r_m_axi_araddr  = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |  val r_m_axi_arlen   = RegInit(0.U(8.W))
          |
          |  // read data channel
          |  val r_m_axi_rready  = RegInit(false.B)
          |  val r_r_valid       = RegInit(false.B)
          |
          |  val r_read_req      = RegNext(io.mode === 1.U, init = false.B)
          |  val r_write_req     = RegNext(io.mode === 2.U, init = false.B)
          |  val r_dma_req       = RegNext(io.mode === 3.U, init = false.B)
          |
          |  // read logic
          |  val r_read_buffer   = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_buffer_shift0 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_buffer_shift1 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_buffer_shift2 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_buffer_shift3 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_buffer_shift4 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_buffer_shift5 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_buffer_shift6 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_buffer_shift7 = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_final_buffer  = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_read_addr     = RegNext(io.readAddr + io.readOffset, init = 0.U)
          |  val r_read_offset   = RegNext(r_read_addr(2,0), init = 0.U)
          |  val r_read_req_next = RegNext(r_read_req, init = false.B)
          |
          |  r_buffer_shift0 := r_read_buffer
          |  r_buffer_shift1 := r_read_buffer >> 8
          |  r_buffer_shift2 := r_read_buffer >> 16
          |  r_buffer_shift3 := r_read_buffer >> 24
          |  r_buffer_shift4 := r_read_buffer >> 32
          |  r_buffer_shift5 := r_read_buffer >> 40
          |  r_buffer_shift6 := r_read_buffer >> 48
          |  r_buffer_shift7 := r_read_buffer >> 56
          |  r_final_buffer  := MuxLookup(r_read_offset, 0.U,
          |                              Seq(
          |                                  0.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift0),
          |                                  1.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift1),
          |                                  2.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift2),
          |                                  3.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift3),
          |                                  4.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift4),
          |                                  5.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift5),
          |                                  6.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift6),
          |                                  7.U -> Cat(0.U(C_M_AXI_DATA_WIDTH.W), r_buffer_shift7)
          |                              ))
          |
          |  io.readValid        := RegNext(RegNext(r_read_req & r_r_valid))
          |  io.readData         := r_final_buffer
          |
          |  r_m_axi_arlen     := Mux(r_dma_req, 0.U, 1.U)
          |
          |  when(r_read_req & ~r_read_req_next) {
          |    r_m_axi_arvalid := true.B
          |    r_m_axi_araddr  := r_read_addr + C_M_TARGET_SLAVE_BASE_ADDR.U
          |  }
          |
          |  when(io.M_AXI_ARVALID & io.M_AXI_ARREADY) {
          |    r_m_axi_arvalid := false.B
          |  }
          |
          |  when(io.M_AXI_RVALID & io.M_AXI_RREADY) {
          |    r_read_buffer   := Cat(io.M_AXI_RDATA, r_read_buffer(2 * C_M_AXI_DATA_WIDTH - 1, C_M_AXI_DATA_WIDTH))
          |  }
          |
          |  when(io.M_AXI_RVALID & io.M_AXI_RREADY & io.M_AXI_RLAST) {
          |    r_r_valid       := true.B
          |  }
          |
          |  when(r_r_valid) {
          |    r_r_valid       := false.B
          |  }
          |
          |  // write logic
          |  io.writeValid           := RegNext(r_write_req & r_b_valid, init = false.B)
          |  val r_write_buffer      = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_padding     = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_masking     = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_reversing   = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_data        = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_data_shift  = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_data_1      = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_data_2      = RegInit(0.U((2 * C_M_AXI_DATA_WIDTH).W))
          |  val r_write_addr        = RegNext(io.writeAddr + io.writeOffset, init = 0.U)
          |  val r_write_req_next    = RegNext(r_write_req, init = false.B)
          |  val r_write_running     = RegInit(false.B)
          |  val r_write_offset      = RegInit(0.U(3.W))
          |  val r_aw_enable         = RegInit(false.B)
          |  val r_first_write_valid = RegInit(false.B)
          |  val w_m_axi_wlast       = io.M_AXI_WVALID & io.M_AXI_WREADY
          |
          |  r_m_axi_awlen     := Mux(r_dma_req, 0.U, 1.U)
          |
          |  r_write_offset    := r_write_addr(2, 0)
          |  r_write_padding   := MuxLookup(io.writeLen, 1.U,
          |                                  Seq(
          |                                      1.U -> "hFF".U,
          |                                      2.U -> "hFFFF".U,
          |                                      3.U -> "hFFFFFF".U,
          |                                      4.U -> "hFFFFFFFF".U,
          |                                      5.U -> "hFFFFFFFFFF".U,
          |                                      6.U -> "hFFFFFFFFFFFF".U,
          |                                      7.U -> "hFFFFFFFFFFFFFF".U,
          |                                      8.U -> "hFFFFFFFFFFFFFFFF".U
          |                                  ))
          |  r_write_masking   := MuxLookup(r_write_offset, 0.U,
          |                                  Seq(
          |                                      0.U -> r_write_padding,
          |                                      1.U -> (r_write_padding << 8),
          |                                      2.U -> (r_write_padding << 16),
          |                                      3.U -> (r_write_padding << 24),
          |                                      4.U -> (r_write_padding << 32),
          |                                      5.U -> (r_write_padding << 40),
          |                                      6.U -> (r_write_padding << 48),
          |                                      7.U -> (r_write_padding << 56)
          |                                  ))
          |  r_write_reversing := ~r_write_masking
          |
          |  r_write_data      := Cat(0.U(C_M_AXI_DATA_WIDTH.W), io.writeData)
          |  r_write_data_shift:= MuxLookup(r_write_offset, 0.U,
          |                                  Seq(
          |                                      0.U -> r_write_data,
          |                                      1.U -> (r_write_data << 8),
          |                                      2.U -> (r_write_data << 16),
          |                                      3.U -> (r_write_data << 24),
          |                                      4.U -> (r_write_data << 32),
          |                                      5.U -> (r_write_data << 40),
          |                                      6.U -> (r_write_data << 48),
          |                                      7.U -> (r_write_data << 56)
          |                                  ))
          |
          |  when(r_write_req & ~r_write_req_next) {
          |    r_m_axi_arvalid := true.B
          |    r_m_axi_araddr  := r_write_addr + C_M_TARGET_SLAVE_BASE_ADDR.U
          |  }
          |
          |  when(io.M_AXI_RVALID & io.M_AXI_RREADY) {
          |    r_write_buffer  := Cat(io.M_AXI_RDATA, r_write_buffer(2 * C_M_AXI_DATA_WIDTH - 1, C_M_AXI_DATA_WIDTH))
          |  }
          |
          |  when(r_r_valid) {
          |    r_write_data_1  := r_write_buffer & r_write_reversing
          |  }
          |
          |  when(r_write_req & RegNext(r_r_valid)) {
          |    r_write_running := true.B
          |    r_write_data_2  := r_write_data_1 | r_write_data_shift
          |  }
          |
          |  when(r_write_running & ~r_aw_enable) {
          |    r_aw_enable     := true.B
          |    r_m_axi_awvalid := true.B
          |    r_m_axi_awaddr  := r_write_addr + C_M_TARGET_SLAVE_BASE_ADDR.U
          |  }
          |
          |  when(r_write_running) {
          |    r_first_write_valid := true.B
          |    r_m_axi_wvalid  := true.B
          |    r_m_axi_wdata   := Mux(r_first_write_valid, r_write_data_2(2 * C_M_AXI_DATA_WIDTH - 1, C_M_AXI_DATA_WIDTH), r_write_data_2(C_M_AXI_DATA_WIDTH - 1, 0))
          |    r_m_axi_wstrb   := "hFF".U
          |  }
          |
          |  when(io.M_AXI_AWVALID & io.M_AXI_AWREADY) {
          |    r_m_axi_awvalid := false.B
          |  }
          |
          |  when(io.M_AXI_WVALID & io.M_AXI_WREADY) {
          |    r_m_axi_wlast   := true.B
          |  }
          |
          |  when(io.M_AXI_WVALID & io.M_AXI_WREADY & io.M_AXI_WLAST) {
          |    r_aw_enable     := false.B
          |    r_write_running := false.B
          |    r_w_valid       := true.B
          |    r_m_axi_wvalid  := false.B
          |  }
          |
          |  when(r_w_valid & io.M_AXI_BVALID & io.M_AXI_BREADY) {
          |    r_w_valid       := false.B
          |    r_b_valid       := true.B
          |    r_m_axi_bready  := false.B
          |    r_m_axi_wlast   := false.B
          |    r_first_write_valid := false.B
          |  } .otherwise {
          |    r_m_axi_bready  := true.B
          |  }
          |
          |  when(r_b_valid) {
          |    r_b_valid       := false.B
          |  }
          |
          |  // dma logic
          |  val r_dma_req_next     = RegNext(r_dma_req)
          |  val r_dmaSrc_addr      = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |  val r_dmaSrc_len       = RegInit(0.U(log2Up(MEMORY_DEPTH).W))
          |  val r_dmaDst_addr      = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |  val r_dmaDst_len       = RegInit(0.U(log2Up(MEMORY_DEPTH).W))
          |  val r_dma_read_data    = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_dma_status       = RegInit(0.U(2.W)) // 0.U - Idle, 1.U - read, 2.U - write
          |  val r_dmaSrc_finish    = RegNext(r_dmaSrc_len === 0.U, init = false.B)
          |  val r_dmaDst_finish    = RegNext(r_dmaDst_len === 0.U, init = false.B)
          |  val r_dmaErase_enable  = RegInit(false.B)
          |  val r_dmaRead_running  = RegInit(false.B)
          |  val r_dmaWrite_running = RegInit(false.B)
          |
          |  io.dmaValid := RegNext(r_dma_req & (r_dma_status === 3.U), init = false.B)
          |
          |  when(r_dma_req & ~r_dma_req_next) {
          |    r_dmaSrc_addr      := io.dmaSrcAddr
          |    r_dmaDst_addr      := io.dmaDstAddr + io.dmaDstOffset
          |    r_dmaSrc_len       := io.dmaSrcLen
          |    r_dmaDst_len       := io.dmaDstLen
          |    // r_dmaSrc_finish    := false.B
          |    // r_dmaDst_finish    := false.B
          |
          |    r_dmaRead_running  := false.B
          |    r_dmaWrite_running := false.B
          |
          |    r_dmaErase_enable  := io.dmaSrcLen === 0.U
          |
          |    r_dma_status       := Mux(io.dmaSrcLen === 0.U, 2.U, 1.U)
          |  } .elsewhen(r_dma_req & r_r_valid) {
          |    r_dma_status       := 2.U
          |    r_dmaSrc_len       := Mux(r_dmaSrc_len =/= 0.U, r_dmaSrc_len - 8.U, r_dmaSrc_len)
          |  } .elsewhen(r_dma_req & r_b_valid) {
          |    r_dma_status       := Mux(!r_dmaSrc_finish, 1.U, Mux(r_dmaDst_finish, 3.U, 2.U))
          |
          |    r_dmaRead_running  := false.B
          |    r_dmaWrite_running := false.B
          |
          |    r_dmaSrc_addr      := r_dmaSrc_addr + 8.U
          |    r_dmaDst_addr      := r_dmaDst_addr + 8.U
          |  }
          |
          |  when(r_dma_req & io.M_AXI_AWVALID & io.M_AXI_AWREADY) {
          |    r_dmaDst_len       := Mux(r_dmaDst_len =/= 0.U, r_dmaDst_len - 8.U, r_dmaDst_len)
          |  }
          |
          |  when(r_dma_status === 3.U) {
          |    r_dma_status       := 0.U
          |    r_dmaErase_enable  := false.B
          |  }
          |
          |  when(r_dma_status === 1.U & ~r_dmaRead_running) {
          |    r_dmaRead_running  := true.B
          |
          |    r_m_axi_arvalid    := true.B
          |    r_m_axi_araddr     := r_dmaSrc_addr + C_M_TARGET_SLAVE_BASE_ADDR.U
          |  }
          |
          |  when(io.M_AXI_RVALID & io.M_AXI_RREADY & io.M_AXI_RLAST) {
          |    r_dma_read_data    := io.M_AXI_RDATA
          |  }
          |
          |  when(r_dma_status === 2.U & ~r_dmaWrite_running) {
          |    r_dmaWrite_running := true.B
          |
          |    r_m_axi_awvalid    := true.B
          |    r_m_axi_awaddr     := r_dmaDst_addr + C_M_TARGET_SLAVE_BASE_ADDR.U
          |    r_m_axi_wvalid     := true.B
          |    r_m_axi_wdata      := Mux((r_dmaSrc_finish & !r_dmaDst_finish) | r_dmaErase_enable, 0.U, r_dma_read_data)
          |    r_m_axi_wstrb      := "hFF".U
          |  }
          |
          |  // AXI4 Full port connection
          |  io.M_AXI_AWID    := 0.U
          |  io.M_AXI_AWLEN   := r_m_axi_awlen
          |  io.M_AXI_AWSIZE  := log2Up(C_M_AXI_DATA_WIDTH / 8 - 1).U
          |  io.M_AXI_AWBURST := 1.U
          |  io.M_AXI_AWLOCK  := false.B
          |  io.M_AXI_AWCACHE := 2.U
          |  io.M_AXI_AWPROT  := 0.U
          |  io.M_AXI_AWQOS   := 0.U
          |  io.M_AXI_AWUSER  := 0.U
          |  io.M_AXI_AWADDR  := Cat(r_m_axi_awaddr(C_M_AXI_ADDR_WIDTH - 1, 3), 0.U(3.W))
          |  io.M_AXI_AWVALID := r_m_axi_awvalid
          |
          |  io.M_AXI_WSTRB   := r_m_axi_wstrb
          |  io.M_AXI_WUSER   := 0.U
          |  io.M_AXI_WDATA   := r_m_axi_wdata
          |  io.M_AXI_WLAST   := Mux(r_write_req, r_m_axi_wlast, w_m_axi_wlast)
          |  io.M_AXI_WVALID  := r_m_axi_wvalid
          |
          |  io.M_AXI_BREADY  := true.B
          |
          |  io.M_AXI_ARID    := 0.U
          |  io.M_AXI_ARLEN   := r_m_axi_arlen
          |  io.M_AXI_ARSIZE  := log2Up(C_M_AXI_DATA_WIDTH / 8 - 1).U
          |  io.M_AXI_ARBURST := 1.U
          |  io.M_AXI_ARLOCK  := false.B
          |  io.M_AXI_ARCACHE := 2.U
          |  io.M_AXI_ARPROT  := 0.U
          |  io.M_AXI_ARQOS   := 0.U
          |  io.M_AXI_ARUSER  := 0.U
          |  io.M_AXI_ARADDR  := Cat(r_m_axi_araddr(C_M_AXI_ADDR_WIDTH - 1, 3), 0.U(3.W))
          |  io.M_AXI_ARVALID := r_m_axi_arvalid
          |
          |  io.M_AXI_RREADY  := true.B
          |}
        """

    val alignDdrModuleST: ST =
      st"""
          |class ${moduleName}(val C_M_AXI_DATA_WIDTH: Int,
          |                    val C_M_AXI_ADDR_WIDTH: Int,
          |                    val MEMORY_DEPTH: Int,
          |                    val C_M_TARGET_SLAVE_BASE_ADDR: BigInt = 0x0) extends Module {
          |
          |  val io = IO(new Bundle{
          |    val mode = Input(UInt(2.W)) // 00 -> disable, 01 -> read, 10 -> write, 11 -> DMA
          |
          |    // Byte level read/write port
          |    val readAddr    = Input(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val readData    = Output(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val readValid   = Output(Bool())
          |
          |    val writeAddr   = Input(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val writeData   = Input(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val writeValid  = Output(Bool())
          |
          |    // DMA
          |    val dmaSrcAddr   = Input(UInt(C_M_AXI_ADDR_WIDTH.W))  // byte address
          |    val dmaDstAddr   = Input(UInt(C_M_AXI_ADDR_WIDTH.W))  // byte address
          |    val dmaSrcLen    = Input(UInt(log2Up(MEMORY_DEPTH).W)) // byte count
          |    val dmaDstLen    = Input(UInt(log2Up(MEMORY_DEPTH).W)) // byte count
          |    val dmaValid     = Output(Bool())
          |
          |    // master write address channel
          |    val M_AXI_AWID    = Output(UInt(1.W))
          |    val M_AXI_AWADDR  = Output(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val M_AXI_AWLEN   = Output(UInt(8.W))
          |    val M_AXI_AWSIZE  = Output(UInt(3.W))
          |    val M_AXI_AWBURST = Output(UInt(2.W))
          |    val M_AXI_AWLOCK  = Output(Bool())
          |    val M_AXI_AWCACHE = Output(UInt(4.W))
          |    val M_AXI_AWPROT  = Output(UInt(3.W))
          |    val M_AXI_AWQOS   = Output(UInt(4.W))
          |    val M_AXI_AWUSER  = Output(UInt(1.W))
          |    val M_AXI_AWVALID = Output(Bool())
          |    val M_AXI_AWREADY = Input(Bool())
          |
          |    // master write data channel
          |    val M_AXI_WDATA  = Output(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val M_AXI_WSTRB  = Output(UInt((C_M_AXI_DATA_WIDTH/8).W))
          |    val M_AXI_WLAST  = Output(Bool())
          |    val M_AXI_WUSER  = Output(UInt(1.W))
          |    val M_AXI_WVALID = Output(Bool())
          |    val M_AXI_WREADY = Input(Bool())
          |
          |    // master write response channel
          |    val M_AXI_BID    = Input(UInt(1.W))
          |    val M_AXI_BRESP  = Input(UInt(2.W))
          |    val M_AXI_BUSER  = Input(UInt(1.W))
          |    val M_AXI_BVALID = Input(Bool())
          |    val M_AXI_BREADY = Output(Bool())
          |
          |    // master read address channel
          |    val M_AXI_ARID    = Output(UInt(1.W))
          |    val M_AXI_ARADDR  = Output(UInt(C_M_AXI_ADDR_WIDTH.W))
          |    val M_AXI_ARLEN   = Output(UInt(8.W))
          |    val M_AXI_ARSIZE  = Output(UInt(3.W))
          |    val M_AXI_ARBURST = Output(UInt(2.W))
          |    val M_AXI_ARLOCK  = Output(Bool())
          |    val M_AXI_ARCACHE = Output(UInt(4.W))
          |    val M_AXI_ARPROT  = Output(UInt(3.W))
          |    val M_AXI_ARQOS   = Output(UInt(4.W))
          |    val M_AXI_ARUSER  = Output(UInt(1.W))
          |    val M_AXI_ARVALID = Output(Bool())
          |    val M_AXI_ARREADY = Input(Bool())
          |
          |    // master read data channel
          |    val M_AXI_RID    = Input(UInt(1.W))
          |    val M_AXI_RDATA  = Input(UInt(C_M_AXI_DATA_WIDTH.W))
          |    val M_AXI_RRESP  = Input(UInt(2.W))
          |    val M_AXI_RLAST  = Input(Bool())
          |    val M_AXI_RUSER  = Input(UInt(1.W))
          |    val M_AXI_RVALID = Input(Bool())
          |    val M_AXI_RREADY = Output(Bool())
          |  })
          |
          |  // registers for diff channels
          |  // write address channel
          |  val r_m_axi_awvalid = RegInit(false.B)
          |  val r_m_axi_awaddr  = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |
          |  // write data channel
          |  val r_m_axi_wvalid  = RegInit(false.B)
          |  val r_m_axi_wdata   = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_m_axi_wstrb   = RegInit(0.U((C_M_AXI_DATA_WIDTH/8).W))
          |  val r_m_axi_wlast   = RegInit(false.B)
          |  val r_w_valid       = RegInit(false.B)
          |
          |  // write response channel
          |  val r_b_valid       = RegInit(false.B)
          |
          |  // read address channel
          |  val r_m_axi_arvalid = RegInit(false.B)
          |  val r_m_axi_araddr  = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |
          |  // read data channel
          |  val r_m_axi_rready  = RegInit(false.B)
          |  val r_r_valid       = RegInit(false.B)
          |
          |  val r_read_req      = RegNext(io.mode === 1.U, init = false.B)
          |  val r_write_req     = RegNext(io.mode === 2.U, init = false.B)
          |  val r_dma_req       = RegNext(io.mode === 3.U, init = false.B)
          |
          |  // read logic
          |  val r_read_req_next = RegNext(r_read_req, init = false.B)
          |  val r_read_addr     = RegNext(io.readAddr + C_M_TARGET_SLAVE_BASE_ADDR.U, init = 0.U)
          |
          |  io.readValid        := r_read_req & r_r_valid
          |  io.readData         := RegNext(io.M_AXI_RDATA)
          |
          |  when(r_read_req & ~r_read_req_next) {
          |    r_m_axi_arvalid   := true.B
          |    r_m_axi_araddr    := r_read_addr
          |  }
          |
          |  when(io.M_AXI_ARVALID & io.M_AXI_ARREADY) {
          |    r_m_axi_arvalid   := false.B
          |  }
          |
          |  when(io.M_AXI_RVALID & io.M_AXI_RREADY & io.M_AXI_RLAST) {
          |    r_r_valid         := true.B
          |  }
          |
          |  when(r_r_valid) {
          |    r_r_valid         := false.B
          |  }
          |
          |  // write logic
          |  io.writeValid        := r_write_req & r_b_valid
          |  val r_write_addr     = RegNext(io.writeAddr + C_M_TARGET_SLAVE_BASE_ADDR.U, init = 0.U)
          |  val r_write_req_next = RegNext(r_write_req, init = false.B)
          |  val r_write_data     = RegNext(io.writeData, init = 0.U)
          |
          |  when(r_write_req & ~r_write_req_next) {
          |    r_m_axi_awvalid := true.B
          |    r_m_axi_awaddr  := r_write_addr
          |    r_m_axi_wvalid  := true.B
          |    r_m_axi_wdata   := r_write_data
          |    r_m_axi_wstrb   := "hFF".U
          |    r_m_axi_wlast   := true.B
          |  }
          |
          |  when(io.M_AXI_AWVALID & io.M_AXI_AWREADY) {
          |    r_m_axi_awvalid := false.B
          |  }
          |
          |  when(io.M_AXI_WVALID & io.M_AXI_WREADY & io.M_AXI_WLAST) {
          |    r_w_valid       := true.B
          |    r_m_axi_wvalid  := false.B
          |  }
          |
          |  when(r_w_valid & io.M_AXI_BVALID & io.M_AXI_BREADY) {
          |    r_w_valid       := false.B
          |    r_b_valid       := true.B
          |    r_m_axi_wlast   := false.B
          |  }
          |
          |  when(r_b_valid) {
          |    r_b_valid       := false.B
          |  }
          |
          |  // dma logic
          |  val r_dma_req_next     = RegNext(r_dma_req, init = false.B)
          |  val r_dmaSrc_addr      = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |  val r_dmaSrc_len       = RegInit(0.U(log2Up(MEMORY_DEPTH).W))
          |  val r_dmaDst_addr      = RegInit(0.U(C_M_AXI_ADDR_WIDTH.W))
          |  val r_dmaDst_len       = RegInit(0.U(log2Up(MEMORY_DEPTH).W))
          |
          |  val r_dma_read_data    = RegInit(0.U(C_M_AXI_DATA_WIDTH.W))
          |  val r_dma_status       = RegInit(0.U(2.W)) // 0.U - Idle, 1.U - read, 2.U - write
          |  val r_dmaSrc_finish    = RegNext(r_dmaSrc_len === 0.U, init = false.B)
          |  val r_dmaDst_finish    = RegNext(r_dmaDst_len === 0.U, init = false.B)
          |  val r_dmaErase_enable  = RegInit(false.B)
          |  val r_dmaRead_running  = RegInit(false.B)
          |  val r_dmaWrite_running = RegInit(false.B)
          |
          |  io.dmaValid := RegNext(r_dma_req & (r_dma_status === 3.U))
          |
          |  when(r_dma_req & ~r_dma_req_next) {
          |    r_dmaSrc_addr      := io.dmaSrcAddr
          |    r_dmaDst_addr      := io.dmaDstAddr
          |    r_dmaSrc_len       := io.dmaSrcLen
          |    r_dmaDst_len       := io.dmaDstLen
          |
          |    r_dmaRead_running  := false.B
          |    r_dmaWrite_running := false.B
          |
          |    r_dmaErase_enable  := io.dmaSrcLen === 0.U
          |
          |    r_dma_status       := Mux(io.dmaSrcLen === 0.U, 2.U, 1.U)
          |  } .elsewhen(r_dma_req & r_r_valid) {
          |    r_dma_status       := 2.U
          |    r_dmaSrc_len       := Mux(r_dmaSrc_len =/= 0.U, r_dmaSrc_len - 8.U, r_dmaSrc_len)
          |  } .elsewhen(r_dma_req & r_b_valid) {
          |    r_dma_status       := Mux(!r_dmaSrc_finish, 1.U, Mux(r_dmaDst_finish, 3.U, 2.U))
          |
          |    r_dmaRead_running  := false.B
          |    r_dmaWrite_running := false.B
          |
          |    r_dmaSrc_addr      := r_dmaSrc_addr + 8.U
          |    r_dmaDst_addr      := r_dmaDst_addr + 8.U
          |  }
          |
          |  when(r_dma_req & io.M_AXI_AWVALID & io.M_AXI_AWREADY) {
          |    r_dmaDst_len       := Mux(r_dmaDst_len =/= 0.U, r_dmaDst_len - 8.U, r_dmaDst_len)
          |  }
          |
          |  when(r_dma_status === 3.U) {
          |    r_dma_status       := 0.U
          |    r_dmaErase_enable  := false.B
          |  }
          |
          |  when(r_dma_status === 1.U & ~r_dmaRead_running) {
          |    r_dmaRead_running  := true.B
          |
          |    r_m_axi_arvalid    := true.B
          |    r_m_axi_araddr     := r_dmaSrc_addr
          |  }
          |
          |  when(io.M_AXI_RVALID & io.M_AXI_RREADY & io.M_AXI_RLAST) {
          |    r_dma_read_data    := io.M_AXI_RDATA
          |  }
          |
          |  when(r_dma_status === 2.U & ~r_dmaWrite_running) {
          |    r_dmaWrite_running := true.B
          |
          |    r_m_axi_awvalid    := true.B
          |    r_m_axi_awaddr     := r_dmaDst_addr
          |    r_m_axi_wvalid     := true.B
          |    r_m_axi_wdata      := Mux(r_dmaSrc_finish | r_dmaErase_enable, 0.U, r_dma_read_data)
          |    r_m_axi_wstrb      := "hFF".U
          |    r_m_axi_wlast      := true.B
          |  }
          |
          |  // AXI4 Full port connection
          |  io.M_AXI_AWID    := 0.U
          |  io.M_AXI_AWLEN   := 0.U
          |  io.M_AXI_AWSIZE  := log2Up(C_M_AXI_DATA_WIDTH / 8 - 1).U
          |  io.M_AXI_AWBURST := 1.U
          |  io.M_AXI_AWLOCK  := false.B
          |  io.M_AXI_AWCACHE := 2.U
          |  io.M_AXI_AWPROT  := 0.U
          |  io.M_AXI_AWQOS   := 0.U
          |  io.M_AXI_AWUSER  := 0.U
          |  io.M_AXI_AWADDR  := r_m_axi_awaddr
          |  io.M_AXI_AWVALID := r_m_axi_awvalid
          |
          |  io.M_AXI_WSTRB   := r_m_axi_wstrb
          |  io.M_AXI_WUSER   := 0.U
          |  io.M_AXI_WDATA   := r_m_axi_wdata
          |  io.M_AXI_WLAST   := r_m_axi_wlast
          |  io.M_AXI_WVALID  := r_m_axi_wvalid
          |
          |  io.M_AXI_BREADY  := true.B
          |
          |  io.M_AXI_ARID    := 0.U
          |  io.M_AXI_ARLEN   := 0.U
          |  io.M_AXI_ARSIZE  := log2Up(C_M_AXI_DATA_WIDTH / 8 - 1).U
          |  io.M_AXI_ARBURST := 1.U
          |  io.M_AXI_ARLOCK  := false.B
          |  io.M_AXI_ARCACHE := 2.U
          |  io.M_AXI_ARPROT  := 0.U
          |  io.M_AXI_ARQOS   := 0.U
          |  io.M_AXI_ARUSER  := 0.U
          |  io.M_AXI_ARADDR  := r_m_axi_araddr
          |  io.M_AXI_ARVALID := r_m_axi_arvalid
          |
          |  io.M_AXI_RREADY  := true.B
          |}
        """

    if (memoryType == Anvil.Config.MemoryAccess.BramNative) {
      return bramModuleST
    } else if(memoryType == Anvil.Config.MemoryAccess.BramAxi4 || memoryType == Anvil.Config.MemoryAccess.Ddr) {
      return if(aligned) alignDdrModuleST else ddrModuleST
    } else {
      return st""
    }
  }
}

import HwSynthesizer2._
@record class HwSynthesizer2(val anvil: Anvil) {
  val sharedMemName: String = "arrayRegFiles"
  val generalRegName: String = "generalRegFiles"

  val hwLog: HwSynthesizer2.HwLog = HwSynthesizer2.HwLog(0, MNone(), F, F, 0, 0)

  val noXilinxIp: B = anvil.config.noXilinxIp
  var ipArbiterUsage: HashSSet[ArbIpType] = HashSSet.empty[ArbIpType]
  var ipModules: ISZ[ArbIpModule] = ISZ[ArbIpModule](
    ArbAdder(F, "AdderUnsigned64", "arbAdderUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Add, F), noXilinxIp, 0),
    ArbAdder(T, "AdderSigned64", "arbAdderSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Add, T), noXilinxIp, 1),
    ArbSubtractor(F, "SubtractorUnsigned64", "arbSubtractorUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Sub, F), noXilinxIp, 2),
    ArbSubtractor(T, "SubtractorSigned64", "arbSubtractorSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Sub, T), noXilinxIp, 3),
    ArbIndexer(F, "Indexer", "arbIndexer", anvil.typeBitSize(spType), ArbIntrinsicIP(defaultIndexing), noXilinxIp, 4),
    ArbAnd(F, "AndUnsigned64", "arbAndUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.And, F), 5),
    ArbAnd(T, "AndSigned64", "arbAndSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.And, T), 6),
    ArbOr(F, "OrUnsigned64", "arbOrUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Or, F), 7),
    ArbOr(T, "OrSigned64", "arbOrSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Or, T), 8),
    ArbXor(F, "XorUnsigned64", "arbXorUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Xor, F), 9),
    ArbXor(T, "XorSigned64", "arbXorSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Xor, T), 10),
    ArbEq(F, "EqUnsigned64", "arbEqUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Eq, F), 11),
    ArbEq(T, "EqSigned64", "arbEqSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Eq, T), 12),
    ArbNe(F, "NeUnsigned64", "arbNeUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Ne, F), 13),
    ArbNe(T, "NeSigned64", "arbNeSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Ne, T), 14),
    ArbGt(F, "GtUnsigned64", "arbGtUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Gt, F), 15),
    ArbGt(T, "GtSigned64", "arbGtSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Gt, T), 16),
    ArbGe(F, "GeUnsigned64", "arbGeUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Ge, F), 17),
    ArbGe(T, "GeSigned64", "arbGeSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Ge, T), 18),
    ArbLt(F, "LtUnsigned64", "arbLtUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Lt, F), 19),
    ArbLt(T, "LtSigned64", "arbLtSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Lt, T), 20),
    ArbLe(F, "LeUnsigned64", "arbLeUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Le, F), 21),
    ArbLe(T, "LeSigned64", "arbLeSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Le, T), 22),
    ArbShr(F, "ShrUnsigned64", "arbShrUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Shr, F), 23),
    ArbShr(T, "ShrSigned64", "arbShrSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Shr, T), 24),
    ArbShl(F, "ShlUnsigned64", "arbShlUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Shl, F), 25),
    ArbShl(T, "ShlSigned64", "arbShlSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Shl, T), 26),
    ArbUshr(F, "UshrUnsigned64", "arbUshrUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Ushr, F), 27),
    ArbUshr(T, "UshrSigned64", "arbUshrSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Ushr, T), 28),
    ArbMultiplier(F, "MultiplierUnsigned64", "abrMultiplierUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Mul, F), noXilinxIp, 29),
    ArbMultiplier(T, "MultiplierSigned64", "arbMultiplierSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Mul, T), noXilinxIp, 30),
    ArbDivision(F, "DivisionUnsigned64", "arbDivisionUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Div, F), noXilinxIp, 31),
    ArbDivision(T, "DivisionSigned64", "arbDivisionSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Div, T), noXilinxIp, 32),
    ArbRemainder(F, "RemainerUnsigned64", "arbRemainerUnsigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Rem, F), noXilinxIp, 33),
    ArbRemainder(T, "RemainerSigned64", "arbRemainerSigned64", 64, ArbBinaryIP(AST.IR.Exp.Binary.Op.Rem, T), noXilinxIp, 34),
    ArbBlockMemory(T, "BlockMemory", s"arbBlockMemory", 8, anvil.config.memory, ArbBlockMemoryIP(), anvil.config.memoryAccess, anvil.config.genVerilog, anvil.config.erase, anvil.config.alignAxi4, 35)
  )

  @pure def findChiselModule(ip: ArbIpType): Option[ArbIpModule] = {
    for(i <- 0 until ipModules.size) {
      if(ipModules(i).expression == ip) {
        return Some(ipModules(i))
      }
    }
    return None()
  }

  @strictpure def blockMemoryParaTypeStr(ip: ArbIpType): String = {
    ip match {
      case ArbBlockMemoryIP() =>
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) ", depth: Int" else ", addrWidth: Int, depth: Int"
      case _ => ""
    }
  }

  @strictpure def blockMemoryParaStr(ip: ArbIpType): String = {
    ip match {
      case ArbBlockMemoryIP() =>
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) ", depth" else ", addrWidth, depth"
      case _ => ""
    }
  }

  @strictpure def blockMemoryParaAssignmentStr(ip: ArbIpType): String = {
    ip match {
      case ArbBlockMemoryIP() =>
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) ", depth = depth" else ", addrWidth = addrWidth, depth = depth"
      case _ => ""
    }
  }

  @pure def getIpArbiterTemplate(ip: ArbIpType): ST = {
    val mod = findChiselModule(ip).get
    val outputNameStr: String = ip match {
      case ArbBinaryIP(_, _) => "out"
      case ArbIntrinsicIP(_) => "out"
      case ArbBlockMemoryIP() => "data"
    }

    val outputTypeStr: String = ip match {
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Eq, _) => "Bool()"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Ne, _) => "Bool()"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Gt, _) => "Bool()"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Ge, _) => "Bool()"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Lt, _) => "Bool()"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Le, _) => "Bool()"
      case ArbBinaryIP(_, _) => if (mod.signed) "SInt(dataWidth.W)" else "UInt(dataWidth.W)"
      case ArbIntrinsicIP(_) => "UInt(dataWidth.W)"
      case ArbBlockMemoryIP() => "UInt(dataWidth.W)"
    }

    val outputDefaultStr: String = ip match {
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Eq, _) => "false.B"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Ne, _) => "false.B"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Gt, _) => "false.B"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Ge, _) => "false.B"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Lt, _) => "false.B"
      case ArbBinaryIP(AST.IR.Exp.Binary.Op.Le, _) => "false.B"
      case ArbBinaryIP(_, _) => if (mod.signed) "0.S" else "0.U"
      case ArbIntrinsicIP(_) => "0.U"
      case ArbBlockMemoryIP() => "0.U"
    }


    @pure def requestBundleST: ST = {
      var portST: ISZ[ST] = ISZ[ST]()

      for(i <- mod.portList.entries) {
        // check whether the current signal is a control signal
        // we do not instantiate control signal in Request bundle
        if(!i._2._1) {
          portST = portST :+ st"val ${i._1} = ${i._2._2}(dataWidth.W)"
        }
      }

      val blockMemoryPortST: ST = anvil.config.memoryAccess match {
          case Anvil.Config.MemoryAccess.BramNative =>
            st"""
                |val mode         = UInt(2.W)
                |val readAddr     = UInt(log2Up(depth).W)
                |val readOffset   = UInt(log2Up(depth).W)
                |val readLen      = UInt(4.W)
                |val writeAddr    = UInt(log2Up(depth).W)
                |val writeOffset  = UInt(log2Up(depth).W)
                |val writeLen     = UInt(4.W)
                |val writeData    = UInt(dataWidth.W)
                |val dmaSrcAddr   = UInt(log2Up(depth).W)
                |val dmaDstAddr   = UInt(log2Up(depth).W)
                |val dmaDstOffset = UInt(log2Up(depth).W)
                |val dmaSrcLen    = UInt(log2Up(depth).W)
                |val dmaDstLen    = UInt(log2Up(depth).W)
              """
          case _ =>
            if(anvil.config.alignAxi4)
              st"""
                  |val mode       = UInt(2.W)
                  |val readAddr   = UInt(addrWidth.W)
                  |val writeAddr  = UInt(addrWidth.W)
                  |val writeData  = UInt(dataWidth.W)
                  |val dmaSrcAddr = UInt(addrWidth.W)
                  |val dmaDstAddr = UInt(addrWidth.W)
                  |val dmaSrcLen  = UInt(log2Up(depth).W)
                  |val dmaDstLen  = UInt(log2Up(depth).W)
                """
            else
              st"""
                  |val mode         = UInt(2.W)
                  |val readAddr     = UInt(addrWidth.W)
                  |val readOffset   = UInt(addrWidth.W)
                  |val readLen      = UInt(4.W)
                  |val writeAddr    = UInt(addrWidth.W)
                  |val writeOffset  = UInt(addrWidth.W)
                  |val writeLen     = UInt(4.W)
                  |val writeData    = UInt(dataWidth.W)
                  |val dmaSrcAddr   = UInt(addrWidth.W)
                  |val dmaDstAddr   = UInt(addrWidth.W)
                  |val dmaDstOffset = UInt(addrWidth.W)
                  |val dmaSrcLen    = UInt(log2Up(depth).W)
                  |val dmaDstLen    = UInt(log2Up(depth).W)
                """
      }

      val finalPortST: ST = if(ip == ArbBlockMemoryIP()) blockMemoryPortST else st"${(portST, "\n")}"

      return st"""
                 |class ${mod.moduleName}RequestBundle(dataWidth: Int${blockMemoryParaTypeStr(ip)}) extends Bundle {
                 |  ${finalPortST}
                 |}
               """
    }

    @pure def responseBundleST: ST = {
      var portST: ISZ[ST] = ISZ[ST]()
      portST = portST :+ st"val ${outputNameStr} = ${outputTypeStr}"

      return st"""
                 |class ${mod.moduleName}ResponseBundle(dataWidth: Int) extends Bundle {
                 |  ${(portST, "")}
                 |}
               """
    }

    @strictpure def IpIOST: ST = {
      st"""
          |class ${mod.moduleName}IO(dataWidth: Int${blockMemoryParaTypeStr(ip)}) extends Bundle {
          |  val req = Valid(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)}))
          |  val resp = Flipped(Valid(new ${mod.moduleName}ResponseBundle(dataWidth)))
          |}
        """
    }

    @strictpure def IpArbiterIOST: ST = {
      st"""
          |class ${mod.moduleName}ArbiterIO(numIPs: Int, dataWidth: Int${blockMemoryParaTypeStr(ip)}) extends Bundle {
          |  val ipReqs  = Flipped(Vec(numIPs, Valid(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)}))))
          |  val ipResps = Vec(numIPs, Valid(new ${mod.moduleName}ResponseBundle(dataWidth)))
          |  val ip      = new ${mod.moduleName}IO(dataWidth${blockMemoryParaStr(ip)})
          |}
        """
    }

    @strictpure def arbiterModuleST: ST = {
      st"""
          |class ${mod.moduleName}ArbiterModule(numIPs: Int, dataWidth: Int${blockMemoryParaTypeStr(ip)}) extends Module {
          |  val io = IO(new ${mod.moduleName}ArbiterIO(numIPs, dataWidth${blockMemoryParaStr(ip)}))
          |
          |  // ------------------ Stage 0: Input Cache ------------------
          |  val r_ipReq_valid = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
          |  val r_ipReq_valid_next = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
          |  val r_ipReq_enable = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
          |  val r_ipReq_bits = RegInit(VecInit(Seq.fill(numIPs)(0.U.asTypeOf(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)})))))
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
          |  val r_reqBits  = RegInit(0.U.asTypeOf(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)})))
          |  val r_chosen   = RegInit(0.U(log2Up(numIPs).W))
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
          |  val r_mem_resp_valid = RegNext(io.ip.resp.valid, init = false.B)
          |  val r_mem_resp_bits  = RegNext(io.ip.resp.bits)
          |  val r_mem_resp_id    = RegNext(r_chosen, init = 0.U)
          |
          |  val r_ipResp_valid = RegInit(VecInit(Seq.fill(numIPs)(false.B)))
          |  val r_ipResp_bits  = RegInit(VecInit(Seq.fill(numIPs)(0.U.asTypeOf(new ${mod.moduleName}ResponseBundle(dataWidth)))))
          |
          |  for (i <- 0 until numIPs) {
          |    r_ipResp_valid(i)    := false.B
          |    r_ipResp_bits(i).${outputNameStr} := ${outputDefaultStr}
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

    @pure def interfaceLogicST: ST = {
      var sts: ISZ[ST] = ISZ[ST]()
      val h: HashSMap[String, (B, String)] = mod.portList
      for(entry <- h.entries) {
        // it is control signal
        if(entry._2._1) {
          if(ip == ArbBlockMemoryIP()) {
            sts = sts :+ st"mod.io.${entry._1} := r_mode"
          } else {
            sts = sts :+ st"mod.io.${entry._1} := r_mod_start"
          }
        } else {
          sts = sts :+ st"mod.io.${entry._1} := r_req.${entry._1}"
        }
      }
      sts = sts :+ st"io.resp.bits.${outputNameStr} := r_resp_data"

      return st"${(sts, "\n")}"
    }

    @strictpure def testFunctionST: ST = {
      st"""
          |class ${mod.moduleName}FunctionModule(dataWidth: Int${blockMemoryParaTypeStr(ip)}) extends Module{
          |  val io = IO(new Bundle{
          |    val arb_req  = Valid(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)}))
          |    val arb_resp = Flipped(Valid(new ${mod.moduleName}ResponseBundle(dataWidth)))
          |  })
          |
          |  val r_arb_req          = RegInit(0.U.asTypeOf(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)})))
          |  val r_arb_req_valid    = RegInit(false.B)
          |  val r_arb_resp         = RegInit(0.U.asTypeOf(new ${mod.moduleName}ResponseBundle(dataWidth)))
          |  val r_arb_resp_valid   = RegInit(false.B)
          |  r_arb_resp       := io.arb_resp.bits
          |  r_arb_resp_valid := io.arb_resp.valid
          |  io.arb_req.bits  := r_arb_req
          |  io.arb_req.valid := r_arb_req_valid
          |
          |  val ${mod.moduleName}CP            = RegInit(0.U(4.W))
          |  val r_res            = Reg(${outputTypeStr})
          |
          |  switch(${mod.moduleName}CP) {
          |    is(0.U) {
          |      r_arb_req_valid := true.B
          |      //r_arb_req.a     := 1.S
          |      //r_arb_req.b     := (-2).S
          |      when(r_arb_resp_valid) {
          |          //r_res                := r_arb_resp.out
          |          r_arb_req_valid := false.B
          |          ${mod.moduleName}CP := 1.U
          |      }
          |    }
          |    is(1.U) {
          |      printf("result:%d\n", r_res)
          |    }
          |  }
          |}
        """
    }

    @strictpure def modWrapperST: ST = {
      val respDataStr: String = ip match {
        case ArbBlockMemoryIP() => "readData"
        case ArbBinaryIP(AST.IR.Exp.Binary.Op.Div, _) => "quotient"
        case ArbBinaryIP(AST.IR.Exp.Binary.Op.Rem, _) => "remainder"
        case _ => "out"
      }

      val reqValidST: ST =
        if(ip == ArbBlockMemoryIP())
          st"""
              |val r_mode = RegInit(0.U(2.W))
              |when(memory_valid) {
              |  r_mode := 0.U
              |} .elsewhen(r_req_valid) {
              |  r_mode := r_req.mode
              |}
            """
        else
          st"""
              |val r_mod_start = RegInit(false.B)
              |when(r_req_valid) {
              |    r_mod_start := true.B
              |} .elsewhen(r_resp_valid) {
              |    r_mod_start := false.B
              |}
            """

      val blockMemoryAxi4PortST: ST =
        st"""
            |// master write address channel
            |val M_AXI_AWID    = Output(UInt(1.W))
            |val M_AXI_AWADDR  = Output(UInt(addrWidth.W))
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
            |val M_AXI_WDATA  = Output(UInt(dataWidth.W))
            |val M_AXI_WSTRB  = Output(UInt((dataWidth/8).W))
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
            |val M_AXI_ARADDR  = Output(UInt(addrWidth.W))
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
            |val M_AXI_RDATA  = Input(UInt(dataWidth.W))
            |val M_AXI_RRESP  = Input(UInt(2.W))
            |val M_AXI_RLAST  = Input(Bool())
            |val M_AXI_RUSER  = Input(UInt(1.W))
            |val M_AXI_RVALID = Input(Bool())
            |val M_AXI_RREADY = Output(Bool())
          """

      val blockMemoryAxi4PortAssignST: ST = {
        st"""
            |io.M_AXI_AWID        := mod.io.M_AXI_AWID
            |io.M_AXI_AWADDR      := mod.io.M_AXI_AWADDR
            |io.M_AXI_AWLEN       := mod.io.M_AXI_AWLEN
            |io.M_AXI_AWSIZE      := mod.io.M_AXI_AWSIZE
            |io.M_AXI_AWBURST     := mod.io.M_AXI_AWBURST
            |io.M_AXI_AWLOCK      := mod.io.M_AXI_AWLOCK
            |io.M_AXI_AWCACHE     := mod.io.M_AXI_AWCACHE
            |io.M_AXI_AWPROT      := mod.io.M_AXI_AWPROT
            |io.M_AXI_AWQOS       := mod.io.M_AXI_AWQOS
            |io.M_AXI_AWUSER      := mod.io.M_AXI_AWUSER
            |io.M_AXI_AWVALID     := mod.io.M_AXI_AWVALID
            |mod.io.M_AXI_AWREADY := io.M_AXI_AWREADY
            |
            |io.M_AXI_WDATA      := mod.io.M_AXI_WDATA
            |io.M_AXI_WSTRB      := mod.io.M_AXI_WSTRB
            |io.M_AXI_WLAST      := mod.io.M_AXI_WLAST
            |io.M_AXI_WUSER      := mod.io.M_AXI_WUSER
            |io.M_AXI_WVALID     := mod.io.M_AXI_WVALID
            |mod.io.M_AXI_WREADY := io.M_AXI_WREADY
            |
            |mod.io.M_AXI_BID    := io.M_AXI_BID
            |mod.io.M_AXI_BRESP  := io.M_AXI_BRESP
            |mod.io.M_AXI_BUSER  := io.M_AXI_BUSER
            |mod.io.M_AXI_BVALID := io.M_AXI_BVALID
            |io.M_AXI_BREADY     := mod.io.M_AXI_BREADY
            |
            |io.M_AXI_ARID        := mod.io.M_AXI_ARID
            |io.M_AXI_ARADDR      := mod.io.M_AXI_ARADDR
            |io.M_AXI_ARLEN       := mod.io.M_AXI_ARLEN
            |io.M_AXI_ARSIZE      := mod.io.M_AXI_ARSIZE
            |io.M_AXI_ARBURST     := mod.io.M_AXI_ARBURST
            |io.M_AXI_ARLOCK      := mod.io.M_AXI_ARLOCK
            |io.M_AXI_ARCACHE     := mod.io.M_AXI_ARCACHE
            |io.M_AXI_ARPROT      := mod.io.M_AXI_ARPROT
            |io.M_AXI_ARQOS       := mod.io.M_AXI_ARQOS
            |io.M_AXI_ARUSER      := mod.io.M_AXI_ARUSER
            |io.M_AXI_ARVALID     := mod.io.M_AXI_ARVALID
            |mod.io.M_AXI_ARREADY := io.M_AXI_ARREADY
            |
            |mod.io.M_AXI_RID    := io.M_AXI_RID
            |mod.io.M_AXI_RDATA  := io.M_AXI_RDATA
            |mod.io.M_AXI_RRESP  := io.M_AXI_RRESP
            |mod.io.M_AXI_RLAST  := io.M_AXI_RLAST
            |mod.io.M_AXI_RUSER  := io.M_AXI_RUSER
            |mod.io.M_AXI_RVALID := io.M_AXI_RVALID
            |io.M_AXI_RREADY     := mod.io.M_AXI_RREADY
          """
      }

      val isAxi4Port: B = anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4 || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr

      st"""
          |class ${mod.moduleName}Wrapper(val dataWidth: Int ${blockMemoryParaTypeStr(ip)}) extends Module {
          |    val io = IO(new Bundle{
          |        val req = Input(Valid(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)})))
          |        val resp = Output(Valid(new ${mod.moduleName}ResponseBundle(dataWidth)))
          |        ${if(ip == ArbBlockMemoryIP() && anvil.config.memoryAccess != Anvil.Config.MemoryAccess.BramNative) blockMemoryAxi4PortST else st""}
          |    })
          |
          |    val mod = Module(new ${mod.moduleName}(dataWidth${blockMemoryParaStr(ip)}))
          |
          |    val r_req            = RegInit(0.U.asTypeOf(new ${mod.moduleName}RequestBundle(dataWidth${blockMemoryParaStr(ip)})))
          |    val r_req_valid      = RegNext(io.req.valid, init = false.B)
          |    ${if(ip == ArbBlockMemoryIP()) "val r_req_valid_next = RegNext(r_req_valid, init = false.B)" else ""}
          |
          |    ${if(ip == ArbBlockMemoryIP()) "val memory_valid = mod.io.readValid | mod.io.writeValid | mod.io.dmaValid" else ""}
          |    val r_resp_data  = RegNext(mod.io.${respDataStr})
          |    val r_resp_valid = RegNext(${if(ip == ArbBlockMemoryIP()) "memory_valid" else "mod.io.valid"}, init = false.B)
          |
          |    ${reqValidST}
          |
          |    r_req := io.req.bits
          |
          |
          |    ${interfaceLogicST}
          |    io.resp.valid    := r_resp_valid
          |
          |    ${if(ip == ArbBlockMemoryIP() && isAxi4Port) blockMemoryAxi4PortAssignST else st""}
          |}
        """
    }

    return st"""
               |${requestBundleST}
               |${responseBundleST}
               |${IpIOST}
               |${IpArbiterIOST}
               |${arbiterModuleST}
               |${modWrapperST}
               |${testFunctionST}
             """
  }

  @pure def insDeclST(ip: ArbIpType): ST = {
    val targetModule: ArbIpModule = findChiselModule(ip).get
    val moduleInstances: ST = if(targetModule.expression == ArbBlockMemoryIP()) {
        if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative)
          st"""val ${targetModule.instanceName} = Module(new ${targetModule.moduleName}(${targetModule.asInstanceOf[BlockMemory].depth}, ${targetModule.width}))"""
        else if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramAxi4 || anvil.config.memoryAccess == Anvil.Config.MemoryAccess.Ddr)
          st"""val ${targetModule.instanceName} = Module(new ${targetModule.moduleName}(C_M_AXI_DATA_WIDTH = C_M_AXI_DATA_WIDTH, C_M_AXI_ADDR_WIDTH = C_M_AXI_ADDR_WIDTH, C_M_TARGET_SLAVE_BASE_ADDR = C_M_TARGET_SLAVE_BASE_ADDR, MEMORY_DEPTH = MEMORY_DEPTH))"""
        else
          st""
      } else {
          st"""val ${targetModule.instanceName} = Module(new ${targetModule.moduleName}(${targetModule.width}))"""
      }
    return moduleInstances
  }

  @strictpure def insPortCallST(ip: ArbIpType): ST = {
    val targetModule: ArbIpModule = findChiselModule(ip).get
    st"init${targetModule.instanceName}()"
  }

  @pure def insPortFuncST(ip: ArbIpType): ST = {
    val targetModule: ArbIpModule = findChiselModule(ip).get
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
        if(ip == ArbBlockMemoryIP()) {
          muxLogicST = muxLogicST :+ st"o.${targetModule.instanceName}.io.${entry._1} := ${defaultValue(entry._2._2)}"
        } else {
          muxLogicST = muxLogicST :+ st"o.${targetModule.instanceName}_${modIdx}.io.${entry._1} := ${defaultValue(entry._2._2)}"
        }
      }

      return st"""
                 |def init${targetModule.instanceName}_${modIdx}(): Unit = {
                 |  ${(muxLogicST, "\n")}
                 |}
        """
    }

    return st"not implmented for insPortFuncST"
  }

  @pure def insertIPInput(ip: ArbIpType, newHashSMap: HashSMap[String, ArbIpModule.Input], inputMap: ArbInputMap): Unit = {
    // record the original inputMap
    var h: HashSMap[String, ArbIpModule.Input] = inputMap.ipMap.get(ip).get
    // add new element to original inputMap
    for(entry <- newHashSMap.entries) {
      h = h + entry._1 ~> entry._2
    }
    // delete original inputMap
    inputMap.ipMap = inputMap.ipMap - (ip, inputMap.ipMap.get(ip).get)
    // add the updated inputMap
    inputMap.ipMap = inputMap.ipMap + (ip, h)
  }

  @pure def getIpInstanceName(ip: ArbIpType): Option[String] = {
    for(i <- 0 until ipModules.size) {
      if(ipModules(i).expression == ip) {
        return Some(ipModules(i).instanceName)
      }
    }
    return None()
  }

  @pure def getIpModuleName(ip: ArbIpType): Option[String] = {
    for(i <- 0 until ipModules.size) {
      if(ipModules(i).expression == ip) {
        return Some(ipModules(i).moduleName)
      }
    }
    return None()
  }

  @pure def getArbiterIpId(ip: ArbIpType): Option[Z] = {
    for(i <- 0 until ipModules.size) {
      if(ipModules(i).expression == ip) {
        return Some(ipModules(i).arbIpId)
      }
    }
    return None()
  }

  @pure def populateInputs(label: Z, hashSMap: HashSMap[String, (ST, String)]) : HashSMap[String, ArbIpModule.Input] = {
    var inputList: HashSMap[String, ArbIpModule.Input] = HashSMap.empty
    for(entry <- hashSMap.entries) {
      val stateValue: ArbIpModule.StateValue = ArbIpModule.StateValue(label, entry._2._1.render)
      inputList = inputList + entry._1 ~> ArbIpModule.Input(stateValue, entry._2._2)
    }
    return inputList
  }


  /*
    Notes/links:
    * Slang IR: https://github.com/sireum/slang/blob/master/ast/shared/src/main/scala/org/sireum/lang/ast/IR.scala
    * Anvil IR Intrinsic: https://github.com/sireum/anvil/blob/master/shared/src/main/scala/org/sireum/anvil/Intrinsic.scala
   */
  def printProcedure(name: String, program: AST.IR.Program, output: Anvil.Output, maxRegisters: Util.TempVector, globalInfoMap: HashSMap[QName, VarInfo]): Unit = {
    val o = program.procedures(0)
    var r = HashSMap.empty[ISZ[String], ST]
    val (processedProcedureST, topST) = processProcedure(name, o, maxRegisters, globalInfoMap)
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

    val importPaddingST: ST =
      st"""
          |import chisel3._
          |import chisel3.util._
          |import chisel3.experimental._
          |
        """

    @strictpure def xilinxIpWrapper: ISZ[ST] = {
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

      ISZ[ST]() :+
        importPaddingST :+
        xilinxAdderUnsigned64WrapperST :+
        xilinxAdderSigned64WrapperST :+
        xilinxSubtractorUnsigned64WrapperST :+
        xilinxSubtractorSigned64WrapperST :+
        xilinxMultiplierUnsigned64WrapperST :+
        xilinxMultiplierSigned64WrapperST :+
        xilinxDividerUnsigned64WrapperST :+
        xilinxDividerSigned64WrapperST :+
        (if(anvil.config.memoryAccess == Anvil.Config.MemoryAccess.BramNative) xilinxBramWrapperST else st"") :+
        xilinxIndexAdderWrapperST :+
        xilinxIndexMultiplierWrapperST
    }

    @pure def arbiterModuleST: HashSMap[String, ISZ[ST]] = {
      var arbiterModuleMap: HashSMap[String, ISZ[ST]] = HashSMap.empty

      @pure def arbIpSt(moduleSt: ST, arbTemplateSt: ST): ISZ[ST] = {
        var sts: ISZ[ST] = ISZ[ST]()
        sts = sts :+
          importPaddingST :+
          moduleSt :+
          arbTemplateSt

        return sts
      }

      for(i <- 0 until ipModules.size) {
        ipModules(i) match {
          case ArbAdder(signed, _, _, _, _, _, _) =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
          case ArbSubtractor(signed, _, _, _, _, _, _) =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
          case ArbMultiplier(signed, _, _, _, _, _, _) =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
          case ArbDivision(signed, _, _, _, _, _, _) =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
          case ArbRemainder(signed, _, _, _, _, _, _) =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
          case ArbIndexer(_, _, _, _, _, _, _) =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
          case ArbBlockMemory(_, modName, _, _, _, _, _, _, _, _, _) =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
          case _ =>
            arbiterModuleMap = arbiterModuleMap +
              ipModules(i).moduleName ~> arbIpSt(ipModules(i).moduleST, getIpArbiterTemplate(ipModules(i).expression))
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
    if(!anvil.config.noXilinxIp) {
      output.add(T, ISZ("chisel/src/main/scala", s"XilinxIpWrapper.scala"), st"${(xilinxIpWrapper, "\n")}")
    }
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

    // temporary top function
    output.add(T, ISZ("chisel/src/main/scala", s"Top.scala"), topST)

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
          |    Seq(ChiselGeneratorAnnotation(() => new Top(
          |      addrWidth = 32,
          |      dataWidth = 64,
          |      cpWidth = ${anvil.cpTypeByteSize * 8},
          |      spWidth = ${anvil.spTypeByteSize * 8},
          |      idWidth = 6,
          |      depth = ${anvil.config.memory}
          |    )))
          |  )
          |}
          |
        """

    return verilogGenST
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

  @pure def processProcedure(name: String, o: AST.IR.Procedure, maxRegisters: Util.TempVector, globalInfoMap: HashSMap[QName, VarInfo]): (ST, ST) = {

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

    @pure def topST(): ST = {
      var allArbiterST: ISZ[ST] = ISZ[ST]()
      for(e <- ipArbiterUsage.elements) {
        val moduleName: String = getIpModuleName(e).get
        val instanceName: String = getIpInstanceName(e).get
        val paraStr: String = if(e == ArbBlockMemoryIP()) blockMemoryParaAssignmentStr(e) else ""
        val numIpsStr: String = if(e == ArbBlockMemoryIP()) "2" else "1"
        val blockMemConnectionSt: ST =
          if(e == ArbBlockMemoryIP())
            st"""
                |${instanceName}ArbiterModule.io.ipReqs(1).bits := r_mem_req
                |${instanceName}ArbiterModule.io.ipReqs(1).valid := r_mem_req_valid
                |r_mem_resp := ${instanceName}ArbiterModule.io.ipResps(1).bits
                |r_mem_resp_valid := ${instanceName}ArbiterModule.io.ipResps(1).valid
              """
          else
            st""
        allArbiterST = allArbiterST :+
          st"""
              |val ${instanceName}Wrapper = Module(new ${moduleName}Wrapper(dataWidth = dataWidth${paraStr}))
              |val ${instanceName}ArbiterModule = Module(new ${moduleName}ArbiterModule(numIPs = ${numIpsStr}, dataWidth = dataWidth${paraStr}))
              |${instanceName}Wrapper.io.req <> ${instanceName}ArbiterModule.io.ip.req
              |${instanceName}Wrapper.io.resp <> ${instanceName}ArbiterModule.io.ip.resp
              |mod.io.${instanceName}_req <> ${instanceName}ArbiterModule.io.ipReqs(0)
              |mod.io.${instanceName}_resp <> ${instanceName}ArbiterModule.io.ipResps(0)
              |${blockMemConnectionSt}"""
      }

      return st"""
                 |import chisel3._
                 |import chisel3.util._
                 |import chisel3.experimental._
                 |
                 |class Top(addrWidth: Int,
                 |          dataWidth: Int,
                 |          cpWidth: Int,
                 |          spWidth: Int,
                 |          idWidth: Int,
                 |          depth: Int) extends Module {
                 |  val io = IO(new Bundle{
                 |    val start = Input(Bool())
                 |    val valid = Output(Bool())
                 |  })
                 |
                 |  val r_mem_req  = RegInit(0.U.asTypeOf(new BlockMemoryRequestBundle(dataWidth, depth)))
                 |  val r_mem_req_valid = RegInit(false.B)
                 |  val r_mem_resp = Reg(new BlockMemoryResponseBundle(dataWidth))
                 |  val r_mem_resp_valid = RegInit(false.B)
                 |
                 |  val mod = Module(new ${name}(
                 |    addrWidth = addrWidth,
                 |    dataWidth = dataWidth,
                 |    cpWidth = cpWidth,
                 |    spWidth = spWidth,
                 |    idWidth = idWidth,
                 |    depth = depth
                 |  ))
                 |
                 |  ${(allArbiterST, "")}
                 |
                 |  val router  = Module(new Router(nPorts = 2, idWidth = idWidth, cpWidth = cpWidth))
                 |  router.io.out(0) <> mod.io.routeIn
                 |  router.io.in(0) <> mod.io.routeOut
                 |  val r_routeIn         = RegInit(0.U.asTypeOf(new Packet(idWidth = idWidth, cpWidth = cpWidth)))
                 |  val r_routeIn_valid   = RegInit(false.B)
                 |  val r_routeOut        = RegInit(0.U.asTypeOf(new Packet(idWidth = idWidth, cpWidth = cpWidth)))
                 |  val r_routeOut_valid  = RegInit(false.B)
                 |  router.io.in(1).bits  := r_routeOut
                 |  router.io.in(1).valid := r_routeOut_valid
                 |  r_routeIn            := router.io.out(1).bits
                 |  r_routeIn_valid      := router.io.out(1).valid
                 |
                 |  val TopCP = RegInit(0.U(4.W))
                 |  io.valid := Mux(TopCP === 7.U, true.B, false.B)
                 |  switch(TopCP) {
                 |    is(0.U) {
                 |      TopCP := Mux(io.start, 1.U, 0.U)
                 |    }
                 |    is(1.U) {
                 |      r_mem_req_valid := true.B
                 |      r_mem_req.mode := 2.U
                 |      r_mem_req.writeAddr := 0.U
                 |      r_mem_req.writeOffset := 0.U
                 |      r_mem_req.writeLen := 8.U
                 |      r_mem_req.writeData := "hFFFFFFFFFFFFFFFF".U
                 |      when(r_mem_resp_valid) {
                 |        r_mem_req.mode := 0.U
                 |        r_mem_req_valid := false.B
                 |        TopCP := 2.U
                 |      }
                 |    }
                 |    is(2.U) {
                 |      r_routeOut.srcID := 1.U
                 |      r_routeOut.srcCP := 4.U
                 |      r_routeOut.dstID := 0.U
                 |      r_routeOut.dstCP := 3.U
                 |      r_routeOut_valid := true.B
                 |      TopCP := 3.U
                 |    }
                 |    is(3.U) {
                 |      r_routeOut_valid := false.B
                 |      when(r_routeIn_valid) {
                 |        TopCP := r_routeIn.dstCP
                 |      }
                 |    }
                 |    is(4.U) {
                 |      r_mem_req_valid := true.B
                 |      r_mem_req.mode := 1.U
                 |      r_mem_req.readAddr := 20.U
                 |      r_mem_req.readOffset := 0.U
                 |      r_mem_req.readLen := 8.U
                 |      when(r_mem_resp_valid) {
                 |        r_mem_req.mode := 0.U
                 |        r_mem_req_valid := false.B
                 |        TopCP := 5.U
                 |      }
                 |    }
                 |    is(5.U) {
                 |      r_mem_req_valid := true.B
                 |      r_mem_req.mode := 1.U
                 |      r_mem_req.readAddr := 28.U
                 |      r_mem_req.readOffset := 0.U
                 |      r_mem_req.readLen := 8.U
                 |      when(r_mem_resp_valid) {
                 |        r_mem_req.mode := 0.U
                 |        r_mem_req_valid := false.B
                 |        TopCP := 6.U
                 |      }
                 |    }
                 |    is(6.U) {
                 |      r_mem_req_valid := true.B
                 |      r_mem_req.mode := 1.U
                 |      r_mem_req.readAddr := 36.U
                 |      r_mem_req.readOffset := 0.U
                 |      r_mem_req.readLen := 8.U
                 |      when(r_mem_resp_valid) {
                 |        r_mem_req.mode := 0.U
                 |        r_mem_req_valid := false.B
                 |        TopCP := 7.U
                 |      }
                 |    }
                 |    is(7.U) {
                 |      r_mem_req_valid := true.B
                 |      r_mem_req.mode := 1.U
                 |      r_mem_req.readAddr := 44.U
                 |      r_mem_req.readOffset := 0.U
                 |      r_mem_req.readLen := 8.U
                 |      when(r_mem_resp_valid) {
                 |        r_mem_req.mode := 0.U
                 |        r_mem_req_valid := false.B
                 |        TopCP := 8.U
                 |      }
                 |    }
                 |    is(8.U) {
                 |      printf("%x\n", r_mem_resp.data)
                 |    }
                 |  }
                 |}
               """
    }

    @pure def procedureST(stateMachineST: ST, stateFunctionObjectST: ST): ST = {
      //println(stateMachineST.render)
      //println(stateFunctionObjectST.render)

      var allArbIOST: ISZ[ST] = ISZ[ST]()
      var allArbInstanceST: ISZ[ST] = ISZ[ST]()

      for(e <- ipArbiterUsage.elements) {
        val instName: String = getIpInstanceName(e).get

        allArbIOST = allArbIOST :+
          st"""
              |val ${instName}_req    = Valid(new ${getIpModuleName(e).get}RequestBundle(dataWidth${blockMemoryParaStr(e)}))
              |val ${instName}_resp   = Flipped(Valid(new ${getIpModuleName(e).get}ResponseBundle(dataWidth)))
            """

        allArbInstanceST = allArbInstanceST :+
          st"""
              |// ${getIpModuleName(e).get} Arbiter
              |val r_${instName}_req          = Reg(new ${getIpModuleName(e).get}RequestBundle(dataWidth${blockMemoryParaStr(e)}))
              |val r_${instName}_req_valid    = RegInit(false.B)
              |val r_${instName}_resp         = Reg(new ${getIpModuleName(e).get}ResponseBundle(dataWidth))
              |val r_${instName}_resp_valid   = RegInit(false.B)
              |// connection for ${getIpModuleName(e).get} Arbiter
              |r_${instName}_resp       := io.${instName}_resp.bits
              |r_${instName}_resp_valid := io.${instName}_resp.valid
              |io.${instName}_req.bits  := r_${instName}_req
              |io.${instName}_req.valid := r_${instName}_req_valid
            """
      }

      return st"""
                 |import chisel3._
                 |import chisel3.util._
                 |import chisel3.experimental._
                 |
                 |class ${name} (addrWidth: Int,
                 |               dataWidth: Int,
                 |               cpWidth: Int,
                 |               spWidth: Int,
                 |               idWidth: Int,
                 |               depth: Int) extends Module {
                 |
                 |  val io = IO(new Bundle{
                 |    ${(allArbIOST, "")}
                 |    val routeIn     = Flipped(Valid(new Packet(idWidth, cpWidth)))
                 |    val routeOut    = Valid(new Packet(idWidth, cpWidth))
                 |  })
                 |
                 |  // reg for recording how many rounds needed for the left bytes
                 |  val LeftByteRounds = RegInit(0.U(8.W))
                 |  val IdxLeftByteRounds = RegInit(0.U(8.W))
                 |  ${if (anvil.config.useIP) "val indexerValid = RegInit(false.B)" else ""}
                 |  // reg for general purpose
                 |  ${if (!anvil.config.splitTempSizes) s"val ${generalRegName} = RegInit(VecInit(Seq.fill(GENERAL_REG_DEPTH)(0.U(GENERAL_REG_WIDTH.W))))" else s"${generalPurposeRegisterST.render}"}
                 |  ${if(anvil.config.tempGlobal) globalTempST else st""}
                 |  // reg for code pointer
                 |  val ${name}CP = RegInit(2.U(cpWidth.W))
                 |  // reg for stack pointer
                 |  val SP = RegInit(0.U(spWidth.W))
                 |  // reg for display pointer
                 |  val DP = RegInit(0.U(64.W))
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
                 |  r_routeIn         := io.routeIn.bits
                 |  r_routeIn_valid   := io.routeIn.valid
                 |  io.routeOut.bits  := r_routeOut
                 |  io.routeOut.valid := r_routeOut_valid
                 |
                 |  ${(allArbInstanceST, "\n")}
                 |
                 |  StateMachine.stateMachine(this)
                 |}
                 |
                 |${(stateMachineST, "")}
                 |
                 |${(stateFunctionObjectST, "\n")}
               """
    }

    val basicBlockST = processBasicBlock(name, o.body.asInstanceOf[AST.IR.Body.Basic].blocks, hwLog)

    return (procedureST(basicBlockST._1, basicBlockST._2), topST())
  }

  @pure def processBasicBlock(name: String, bs: ISZ[AST.IR.BasicBlock], hwLog: HwSynthesizer2.HwLog): (ST, ST) = {
    for(b <- bs) {
      if(b.label > hwLog.maxNumLabel) {
        hwLog.maxNumLabel = b.label
      }
    }

    val ipPortLogic = HwSynthesizer2.IpPortAssign(anvil, ISZ[ST](), ipModules, ArbInputMap.empty, ISZ[ST](), ISZ[ST]())
    @pure def basicBlockST(grounds: HashSMap[Z, ST], functions: ISZ[ST]): (ST, ST) = {
      var stateSTs: ISZ[ST] = ISZ[ST]()
      stateSTs = stateSTs :+
        st"""
            |is(0.U) {
            |  r_routeOut.srcID := 0.U
            |  r_routeOut.srcCP := 3.U
            |  r_routeOut.dstID := r_srcID
            |  r_routeOut.dstCP := r_srcCP
            |  r_routeOut_valid := true.B
            |  ${name}CP := 2.U
            |}
            |is(2.U) {
            |  r_routeOut_valid := false.B
            |  when(r_routeIn_valid) {
            |    r_srcCP := r_routeIn.srcCP
            |    r_srcID := r_routeIn.srcID
            |    ${name}CP  := r_routeIn.dstCP
            |  }
            |}
          """
      for(pair <- grounds.entries) {
        stateSTs = stateSTs :+ pair._2
      }

      val fmsST: ST =
        st"""
            |object StateMachine {
            |  def stateMachine(o:${name}): Unit = {
            |    import o._
            |    switch(${name}CP) {
            |      ${(stateSTs, "")}
            |    }
            |  }
            |}
          """

      return (
        st"""${(fmsST, "\n")}""",
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
          val indexerName: String = getIpInstanceName(ArbIntrinsicIP(defaultIndexing)).get
          st"""
              |when(r_${indexerName}_resp_valid) {
              |  ${(ipPortLogic.whenStmtST, "")}
              |  ${jST.render}
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
      ipPortLogic.inputMap = ArbInputMap.empty
    }

    return st"""${(groundST, "\n")}"""
  }

  @pure def processJumpIntrinsic(name: String, b: AST.IR.BasicBlock, ipPortLogic: HwSynthesizer2.IpPortAssign, hwLog: HwSynthesizer2.HwLog): ST = {
    var intrinsicST: ISZ[ST] = ISZ[ST]()
    val j = b.jump

    @strictpure def jumpSplitCpST(label: Z): ST = {
      st"${name}CP := ${hwLog.currentLabel}.U"
    }

    j match {
      case AST.IR.Jump.Intrinsic(intrinsic: Intrinsic.GotoLocal) => {
        val targetAddrST: ST = processExpr(AST.IR.Exp.Temp(intrinsic.loc, anvil.cpType, intrinsic.pos), F, ipPortLogic, hwLog)
        if (intrinsic.isTemp) {
          if(anvil.config.cpMax <= 0) {
            intrinsicST = intrinsicST :+ st"${name}CP := ${targetAddrST}"
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
        }
      }
      case j: AST.IR.Jump.Goto => {
        if(anvil.config.cpMax <= 0) {
          intrinsicST = intrinsicST :+ st"${name}CP := ${j.label}.U"
        }
      }
      case j: AST.IR.Jump.If => {
        val cond = processExpr(j.cond, F, ipPortLogic, hwLog)
        if(anvil.config.cpMax <= 0) {
          intrinsicST = intrinsicST :+ st"${name}CP := Mux((${cond.render}.asUInt) === 1.U, ${j.thenLabel}.U, ${j.elseLabel}.U)"
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
        ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

        val instanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
        ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"r_${instanceName}_req.mode := 0.U"

        if(intrinsic.isRead) {
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${globalName(Util.readAlignRes)} := r_${instanceName}_resp.data"
          intrinsicST =
            st"""
                |r_${instanceName}_req.mode := 1.U
                |r_${instanceName}_req.readAddr := ${globalName(Util.readAlignAddr)}
                |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
              """
        } else {
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"
          intrinsicST =
            st"""
                |r_${instanceName}_req.mode := 2.U
                |r_${instanceName}_req.writeAddr := ${globalName(Util.writeAlignAddr)}
                |r_${instanceName}_req.writeData := ${globalName(Util.writeAlignValue)}
                |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
              """
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.TempLoad) => {
        ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

        val readAddrST: ST = processExpr(intrinsic.base, F, ipPortLogic, hwLog)
        val instanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
        val tempST: ST = st"${if (!anvil.config.splitTempSizes) s"${generalRegName}(${intrinsic.temp}.U)" else s"${getGeneralRegName(intrinsic.tipe)}(${intrinsic.temp}.U)"}"
        val byteST: ST = st"(${intrinsic.bytes * 8 - 1}, 0)"
        val signedST: ST = if(intrinsic.isSigned && anvil.config.splitTempSizes) st".asSInt" else st""
        val offsetWidth: Z = log2Up(anvil.config.memory * 8)
        val readOffsetST: ST = if(intrinsic.offset < 0) st"(${intrinsic.offset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.offset}.U"
        ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"
        ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${tempST.render} := r_${instanceName}_resp.data${byteST.render}${signedST.render}"
        ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"r_${instanceName}_req.mode := 0.U"
        intrinsicST =
          st"""
              |r_${instanceName}_req.mode := 1.U
              |r_${instanceName}_req.readAddr := ${readAddrST.render}
              |r_${instanceName}_req.readOffset := ${readOffsetST.render}
              |r_${instanceName}_req.readLen := ${intrinsic.bytes}.U
              |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
            """
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Erase) => {
        ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

        if(anvil.config.memoryAccess != Anvil.Config.MemoryAccess.Default) {
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val eraseBaseST: ST = processExpr(intrinsic.base, F, ipPortLogic, hwLog)
          val eraseOffsetST: ST = if(intrinsic.offset < 0) st"(${intrinsic.offset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.offset}.U"
          val eraseBytesST: ST = st"${intrinsic.bytes}.U"
          val instanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"r_${instanceName}_req.mode := 0.U"
          val ioDmaDstOffsetST: ST = st"r_${instanceName}_req.dmaDstOffset := ${eraseOffsetST.render}"
          intrinsicST =
            st"""
                |r_${instanceName}_req.mode := 3.U
                |r_${instanceName}_req.dmaSrcAddr := 0.U
                |r_${instanceName}_req.dmaDstAddr := ${eraseBaseST.render}
                |r_${instanceName}_req.dmaSrcLen := 0.U
                |r_${instanceName}_req.dmaDstLen := ${eraseBytesST.render}
                |${if(!anvil.config.alignAxi4) ioDmaDstOffsetST.render else ""}
                |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
              """
        }
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Copy) => {
        ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

        val offsetWidth: Z = log2Up(anvil.config.memory * 8)
        val dmaDstAddrST: ST = processExpr(intrinsic.lbase, F, ipPortLogic, hwLog)
        val dmaDstOffsetST: ST = if(intrinsic.loffset < 0) st"(${intrinsic.loffset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.loffset}.U"
        val dmaSrcLenST: ST = processExpr(intrinsic.rhsBytes, F, ipPortLogic, hwLog)
        val dmaSrcAddrST: ST = processExpr(intrinsic.rhs, F, ipPortLogic, hwLog)
        val instanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
        ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"
        ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"r_${instanceName}_req.mode := 0.U"
        val ioDmaDstOffsetST: ST = st"r_${instanceName}_req.dmaDstOffset := ${dmaDstOffsetST.render}"
        intrinsicST =
          st"""
              |r_${instanceName}_req.mode := 3.U
              |r_${instanceName}_req.dmaSrcAddr := ${dmaSrcAddrST.render}
              |r_${instanceName}_req.dmaDstAddr := ${dmaDstAddrST.render}
              |r_${instanceName}_req.dmaSrcLen := ${dmaSrcLenST.render}
              |r_${instanceName}_req.dmaDstLen := ${intrinsic.lhsBytes}.U
              |${if(!anvil.config.alignAxi4) ioDmaDstOffsetST.render else ""}
              |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
            """
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Store) => {
        ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

        @strictpure def isLhsOffsetIndexing(e: AST.IR.Exp): B = e match {
          case AST.IR.Exp.Intrinsic(in: Intrinsic.Indexing) => T
          case _ => F
        }

        val offsetWidth: Z = log2Up(anvil.config.memory * 8)
        val writeAddrST: ST = processExpr(intrinsic.base, F, ipPortLogic, hwLog)
        val writeOffsetST: ST = if(intrinsic.offset < 0) st"(${intrinsic.offset}).S(${offsetWidth}.W).asUInt" else st"${intrinsic.offset}.U"
        val writeLenST: ST = st"${intrinsic.bytes}.U"
        val writeDataST: ST = processExpr(intrinsic.rhs, F, ipPortLogic, hwLog)
        val signedST: ST = if(intrinsic.isSigned) st".asUInt" else st""
        val instanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
        ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"
        ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"r_${instanceName}_req.mode := 0.U"
        intrinsicST =
          st"""
              |r_${instanceName}_req.mode := 2.U
              |r_${instanceName}_req.writeAddr := ${writeAddrST.render}
              |r_${instanceName}_req.writeOffset := ${writeOffsetST.render}
              |r_${instanceName}_req.writeLen := ${writeLenST.render}
              |r_${instanceName}_req.writeData := ${writeDataST.render}${signedST.render}
              |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
            """
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.RegisterAssign) => {
        val targetReg: String = if(intrinsic.isSP) "SP" else "DP"

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
          val ipT: ArbIpType = if(isPlus) ArbBinaryIP(AST.IR.Exp.Binary.Op.Add, F) else ArbBinaryIP(AST.IR.Exp.Binary.Op.Sub, F)
          ipArbiterUsage = ipArbiterUsage + ipT

          var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
          val instanceName: String = getIpInstanceName(ipT).get
          hashSMap = hashSMap +
            ".a" ~> (st"${leftST.render}", "UInt".string) +
            ".b" ~> (st"${rightST.render}", "UInt".string) +
            "_valid" ~> (st"Mux(r_${instanceName}_resp_valid, false.B, true.B)", "Bool".string)
          insertIPInput(ipT, populateInputs(hwLog.stateBlock.get.label, hashSMap), ipPortLogic.inputMap)
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${targetReg} := r_${instanceName}_resp.out"
          intrinsicST = st""
        } else {
          intrinsicST =
            st"""
                |${targetReg} := ${regValueST}"""
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

    @strictpure def isIntrinsicIndexing(e: AST.IR.Exp): B = e match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Indexing) => T
      case _ => F
    }

    @strictpure def isBinaryExp(e: AST.IR.Exp): B = e match {
      case AST.IR.Exp.Binary(_, _, _, _, _) => T
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
          ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

          val instanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
          val readAddrST: ST = processExpr(getBaseOffsetOfIntrinsicLoad(a.rhs).get._1, F, ipPortLogic, hwLog)
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val intrinsicOffset: Z = getBaseOffsetOfIntrinsicLoad(a.rhs).get._2
          val readOffsetST: ST = if(intrinsicOffset < 0) st"(${intrinsicOffset}).S(${offsetWidth}.W).asUInt" else st"${intrinsicOffset}.U"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${lhsST.render} := ${rhsST.render}"
          assignST =
            st"""
                |r_${instanceName}_req.mode := 1.U
                |r_${instanceName}_req.readAddr := ${readAddrST.render}
                |r_${instanceName}_req.readOffset := ${readOffsetST.render}
                |r_${instanceName}_req.readLen := ${anvil.typeByteSize(a.rhs.tipe)}.U
                |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
              """
        } else if(isBinaryExp(a.rhs) || isIntrinsicIndexing(a.rhs)) {
          val lhsContentST: ST = st"${if(isSignedExp(a.rhs)) "(" else ""}${rhsST.render}${if(isSignedExp(a.rhs)) ").asUInt" else ""}"
          val finalST = st"${lhsST} := ${if(!anvil.config.splitTempSizes) lhsContentST.render else s"${rhsST.render}"}"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ finalST
          assignST = st""
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
          ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

          val instanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
          val readAddrST: ST = processExpr(getBaseOffsetOfIntrinsicLoad(a.rhs).get._1, F, ipPortLogic, hwLog)
          val offsetWidth: Z = log2Up(anvil.config.memory * 8)
          val intrinsicOffset: Z = getBaseOffsetOfIntrinsicLoad(a.rhs).get._2
          val readOffsetST: ST = if(intrinsicOffset < 0) st"(${intrinsicOffset}).S(${offsetWidth}.W).asUInt" else st"${intrinsicOffset}.U"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${lhsST.render} := ${rhsST.render}"
          assignST =
            st"""
                |r_${instanceName}_req.mode := 1.U
                |r_${instanceName}_req.readAddr := ${readAddrST.render}
                |r_${instanceName}_req.readOffset := ${readOffsetST.render}
                |r_${instanceName}_req.readLen := ${anvil.typeByteSize(a.rhs.tipe)}.U
                |r_${instanceName}_req_valid := Mux(r_${instanceName}_resp_valid, false.B, true.B)
              """
        } else if(isBinaryExp(a.rhs) || isIntrinsicIndexing(a.rhs)) {
          val lhsContentST: ST = st"${if(isSignedExp(a.rhs)) "(" else ""}${rhsST.render}${if(isSignedExp(a.rhs)) ").asUInt" else ""}"
          val finalST = st"${lhsST} := ${if(!anvil.config.splitTempSizes) lhsContentST.render else s"${rhsST.render}"}"
          ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ finalST
          assignST = st""
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

  @strictpure def globalName(name: ISZ[String]): ST = st"global_${(name, "_")}"

  @pure def processExpr(exp: AST.IR.Exp, isForcedSign: B, ipPortLogic: HwSynthesizer2.IpPortAssign, hwLog: HwSynthesizer2.HwLog): ST = {
    var exprST = st""

    exp match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Register) => {
        exprST = if(intrinsic.isSP) st"SP" else st"DP"
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => {
        ipArbiterUsage = ipArbiterUsage + ArbBlockMemoryIP()

        val indexerInstanceName: String = getIpInstanceName(ArbBlockMemoryIP()).get
        val byteST: ST = st"(${intrinsic.bytes * 8 - 1}, 0)"
        val signedST: ST = if(intrinsic.isSigned) st".asSInt" else st""
        ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${indexerInstanceName}_resp_valid"
        ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"r_${indexerInstanceName}_req.mode := 0.U"
        exprST = st"r_${indexerInstanceName}_resp.data${byteST.render}${signedST.render}"
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Indexing) => {
        hwLog.indexerInCurrentBlock = T

        val indexerIp: ArbIpType = ArbIntrinsicIP(HwSynthesizer.defaultIndexing)
        ipArbiterUsage = ipArbiterUsage + indexerIp
        val instanceName: String = getIpInstanceName(indexerIp).get

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
          ".baseOffset" ~> (st"${baseOffsetST.render}", "UInt".string) +
          ".dataOffset" ~> (st"${dataOffset}.U", "UInt".string) +
          ".index" ~> (st"${indexST.render}", "UInt".string) +
          ".elementSize" ~> (st"${elementSize}.U", "UInt".string) +
          ".mask" ~> (st"${mask}.U", "UInt".string) +
          "_valid" ~> (st"Mux(r_${instanceName}_resp_valid, false.B, true.B)", "Bool".string)
        insertIPInput(ArbIntrinsicIP(defaultIndexing), populateInputs(hwLog.stateBlock.get.label, hashSMap), ipPortLogic.inputMap)

        exprST = st"r_${instanceName}_resp.out"
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

        @pure def genIpArbiterPortLogic(opType: IR.Exp.Binary.Op.Type): ST = {
          val arbBinIp: ArbIpType = ArbBinaryIP(opType, isSIntOperation)

          // add one usage for current binary operation
          ipArbiterUsage = ipArbiterUsage + arbBinIp

          val arbiterID: Z = getArbiterIpId(arbBinIp).get
          val instanceName: String = getIpInstanceName(arbBinIp).get

          var hashSMap: HashSMap[String, (ST, String)] = HashSMap.empty[String, (ST, String)]
          if(isSIntOperation) {
            hashSMap = hashSMap +
              ".a".string ~> (st"${leftST.render}", "SInt".string) +
              ".b".string ~> (st"${rightST.render}", "SInt".string)
          } else {
            hashSMap = hashSMap +
              ".a".string ~> (st"${leftST.render}", "UInt".string) +
              ".b".string ~> (st"${rightST.render}", "UInt".string)
          }
          hashSMap = hashSMap + "_valid".string ~> (st"Mux(r_${instanceName}_resp_valid, false.B, true.B)", "Bool".string)

          insertIPInput(ArbBinaryIP(opType, isSIntOperation), populateInputs(hwLog.stateBlock.get.label, hashSMap), ipPortLogic.inputMap)
          ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"r_${instanceName}_resp_valid"

          val outputName: String = arbBinIp match {
            case ArbBinaryIP(AST.IR.Exp.Binary.Op.Div, _) => "quotient"
            case ArbBinaryIP(AST.IR.Exp.Binary.Op.Rem, _) => "remainder"
            case _ => "out"
          }

          return st"r_${instanceName}_resp.out"
        }

        exp.op match {
          case AST.IR.Exp.Binary.Op.Add => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Sub => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Mul => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Div => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Rem => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.And => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Or  => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Xor => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.CondAnd => {
            halt(s"processExpr, you got an error about Op.CondAnd")
          }
          case AST.IR.Exp.Binary.Op.CondOr => {
            halt(s"processExpr, you got an error about Op.CondOr")
          }
          case AST.IR.Exp.Binary.Op.Eq => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Ne => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Ge => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Gt => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Le => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Lt => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Shr => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Ushr => {
            exprST = genIpArbiterPortLogic(exp.op)
          }
          case AST.IR.Exp.Binary.Op.Shl => {
            exprST = genIpArbiterPortLogic(exp.op)
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
                                         var sts: ISZ[ST],
                                         val ipModules: ISZ[ArbIpModule],
                                         var inputMap: ArbInputMap,
                                         var whenCondST: ISZ[ST],
                                         var whenStmtST: ISZ[ST]) extends MAnvilIRTransformer {
    @pure def getInputPort(ip: ArbIpType): HashSMap[String, ArbIpModule.Input] = {
      return inputMap.ipMap.get(ip).get
    }

    @pure def getIpInstanceName(ip: ArbIpType): Option[String] = {
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
      @pure def inputLogic(ipt: ArbIpType): Unit = {
        val instanceName: String = getIpInstanceName(ipt).get
        val inputs: HashSMap[String, ArbIpModule.Input] = getInputPort(ipt)
        for (entry <- inputs.entries) {
          sts = sts :+ st"r_${instanceName}_req${entry._1} := ${entry._2.stateValue.value}"
        }
      }
      o match {
        case o: AST.IR.Exp.Binary =>
          if(anvil.config.useIP) {
            val signed: B = isSignedExp(o.left) || isSignedExp(o.right)
            inputLogic(ArbBinaryIP(o.op, signed))
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
        val instanceName: String = getIpInstanceName(ArbIntrinsicIP(defaultIndexing)).get
        val inputs: HashSMap[String, ArbIpModule.Input] = getInputPort(ArbIntrinsicIP(defaultIndexing))
        for (entry <- inputs.entries) {
          sts = sts :+ st"r_${instanceName}_req${entry._1} := ${entry._2.stateValue.value}"
        }
      }
      return MAnvilIRTransformer.PreResultIntrinsicIndexing
    }

    override def preIntrinsicRegisterAssign(o: Intrinsic.RegisterAssign): MAnvilIRTransformer.PreResult[Intrinsic.RegisterAssign] = {
      if(anvil.config.useIP) {
        if (o.isInc) {
          val ipT: ArbIpType = o.value match {
            case AST.IR.Exp.Int(_, v, _) => {
              if (v < 0) ArbBinaryIP(AST.IR.Exp.Binary.Op.Sub, F)
              else ArbBinaryIP(AST.IR.Exp.Binary.Op.Add, F)
            }
            case _ => ArbBinaryIP(AST.IR.Exp.Binary.Op.Add, F)
          }
          val instanceName: String = getIpInstanceName(ipT).get
          val inputs: HashSMap[String, ArbIpModule.Input] = getInputPort(ipT)
          for (entry <- inputs.entries) {
            sts = sts :+ st"r_${instanceName}_req${entry._1} := ${entry._2.stateValue.value}"
          }
        }
      }
      return MAnvilIRTransformer.PreResultIntrinsicRegisterAssign
    }
  }
}