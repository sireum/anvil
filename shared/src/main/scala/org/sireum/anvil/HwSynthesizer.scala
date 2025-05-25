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
import org.sireum.anvil.Util.{AnvilIRPrinter, constructLocalId, indexing}
import org.sireum.lang.ast.{IR, Typed}
import org.sireum.lang.ast.IR.{Exp, Jump}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Resolver.{QName, addBuiltIns, typeParamMap}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Position

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

object IndexingLog {
  var flagIndexingInBlock: B = F
  var activeIndex: Z = 0
  def isIndexingInBlock(): B = {
    return flagIndexingInBlock
  }

  def enableFlagIndexingInBlock(): Unit = {
    flagIndexingInBlock = T
  }

  def disableFlagIndexingInBlock(): Unit = {
    flagIndexingInBlock = F
  }
}

@sig trait IpType {

}
@datatype class BinaryIP(t: AST.IR.Exp.Binary.Op.Type, signed: B) extends IpType
@datatype class IntrinsicIP(t: AST.IR.Exp.Intrinsic.Type) extends IpType

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
    IntrinsicIP(HwSynthesizer.defaultIndexing) ~> HashSMap.empty
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
          |    val regA = Reg(${portType}(64.W))
          |    val regB = Reg(${portType}(64.W))
          |    val result = Reg(${portType}(64.W))
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
          |    val regA = Reg(${portType}(64.W))
          |    val regB = Reg(${portType}(64.W))
          |    val result = Reg(${portType}(64.W))
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
                        val exp: IpType) extends ChiselModule {
  @strictpure override def signed: B = signedPort
  @strictpure override def moduleName: String = moduleDeclarationName
  @strictpure override def instanceName: String = moduleInstanceName
  @strictpure override def width: Z = widthOfPort
  @strictpure override def portList: HashSMap[String, String] = {
    HashSMap.empty[String, String] + "baseOffset" ~> "UInt" + "dataOffset" ~> "UInt" + "index" ~> "UInt" +
      "elementSize" ~> "UInt" + "mask" ~> "UInt" + "ready" ~> "Bool"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.out := io.a & io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.out := io.a | io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.out := io.a ^ io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(Bool())
        |    })
        |
        |    io.out := io.a === io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(Bool())
        |    })
        |
        |    io.out := io.a =/= io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(Bool())
        |    })
        |
        |    io.out := io.a >= io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(Bool())
        |    })
        |
        |    io.out := io.a > io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(Bool())
        |    })
        |
        |    io.out := io.a <= io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> s"${portType}"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(${portType}(width.W))
        |        val out = Output(Bool())
        |    })
        |
        |    io.out := io.a < io.b
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> "UInt"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(UInt(width.W))
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.out := Mux(io.b > 64.U, ${if(signed) "io.a >> 64.U" else "0.U"}, io.a >> io.b(6,0))
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> "UInt"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(UInt(width.W))
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.out := Mux(io.b > 64.U, ${if(signed) "0.S" else "0.U"}, io.a << io.b(6,0))
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
    HashSMap.empty[String, String] + "a" ~> s"${portType}" + "b" ~> "UInt"
  }
  @strictpure override def expression: IpType = exp
  @strictpure override def moduleST: ST = {
    st"""
        |class ${moduleName}(val width: Int = 64) extends Module {
        |    val io = IO(new Bundle{
        |        val a = Input(${portType}(width.W))
        |        val b = Input(UInt(width.W))
        |        val out = Output(${portType}(width.W))
        |    })
        |
        |    io.out := Mux(io.b > 64.U, ${if(signed) "0.S" else "0.U"}, io.a${if(signed) ".asUInt" else ""} >> io.b(6,0))${if(signed) ".asSInt" else ""}
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

import HwSynthesizer._
@record class HwSynthesizer(val anvil: Anvil) {
  val sharedMemName: String = "arrayRegFiles"
  val generalRegName: String = "generalRegFiles"

  var ipAlloc: Util.IpAlloc = Util.IpAlloc(HashSMap.empty, HashSMap.empty, 0)

  val xilinxIPValid: B = if(anvil.config.useIP) anvil.config.noXilinxIp else T
  var ipModules: ISZ[ChiselModule] = ISZ[ChiselModule](
    Adder(F, "AdderUnsigned64", "adderUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Add, F), xilinxIPValid),
    Adder(T, "AdderSigned64", "adderSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Add, T), xilinxIPValid),
    Subtractor(F, "SubtractorUnsigned64", "subtractorUnsigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Sub, F), xilinxIPValid),
    Subtractor(T, "SubtractorSigned64", "subtractorSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Sub, T), xilinxIPValid),
    Indexer(F, "Indexer", "indexer", 16, IntrinsicIP(defaultIndexing)),
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
    Remainder(T, "RemainerSigned64", "remainerSigned64", 64, BinaryIP(AST.IR.Exp.Binary.Op.Rem, T), xilinxIPValid)
  )

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
      val modDeclIns: ISZ[ST] = {
        for(i <- 0 until numInstances) yield
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
        muxLogicST = muxLogicST :+ st"o.${targetModule.instanceName}_${modIdx}.io.${entry._1} := ${defaultValue(entry._2)}"
      }

      return st"""
                 |def init${targetModule.instanceName}_${modIdx}() = {
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
    output.add(T, ISZ("chisel/src/main/scala", s"chisel-${name}.scala"), processedProcedureST)
    output.add(T, ISZ("chisel", "build.sbt"), buildSbtST())
    output.add(T, ISZ("chisel", "project", "build.properties"), st"sbt.version=${output.sbtVersion}")

    if(!anvil.config.noXilinxIp) {
      @pure def xilinxAddSub64ST(isAdder: B, sign: B): ST = {
        val opStr: String = if(isAdder) "Adder" else "Subtractor"
        val signStr: String = if(sign) "Signed" else "Unsigned"
        return st"""
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
      @pure def xilinxMul64ST(sign: B): ST = {
        val signStr: String = if(sign) "Signed" else "Unsigned"
        return st"""
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
      @pure def xilinxDiv64ST(sign: B): ST = {
        val signStr: String = if(sign) "Signed" else "Unsigned"
        return st"""
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
      output.add(T, ISZ("chisel/src/test/scala", s"${name}VerilogGeneration.scala"), verilogGenerationST(name))
    } else if (anvil.config.axi4) {
      output.add(T, ISZ("chisel/src/test/scala", s"AXIWrapperChiselGenerated${name}VerilogGeneration.scala"), axiWrapperVerilogGenerationST(name))
    }

    anvil.config.simOpt match {
      case Some(simConfig) => {
        //output.add(T, ISZ("chisel/src/test/scala", s"AXIWrapperChiselGenerated${name}Bench.scala"), AXI4WrapperTestBenchST(name, simConfig.cycles))
        output.add(T, ISZ("chisel/src/test/scala", s"${name}Bench.scala"), testBenchST(name, simConfig.cycles))
      }
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
          |      dut.clock.setTimeout(10000)
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

  @pure def AXI4WrapperTestBenchST(moduleName: String, cycles: Z): ST = {

    val benchST: ST =
      st"""
          |import chisel3._
          |import chiseltest._
          |import chiseltest.simulator.WriteVcdAnnotation
          |import org.scalatest.flatspec.AnyFlatSpec
          |
          |class AXIWrapperChiselGenerated${moduleName}Bench extends AnyFlatSpec with ChiselScalatestTester {
          |  "AXIWrapperChiselGenerated${moduleName}Bench" should "work" in {
          |    test(new AXIWrapperChiselGenerated${moduleName}()).withAnnotations(Seq(WriteVcdAnnotation, VerilatorBackendAnnotation)) { dut =>
          |      dut.clock.setTimeout(10000)
          |
          |      dut.reset.poke(false.B)
          |      for (i <- 0 until (5)) {
          |        dut.clock.step()
          |      }
          |      dut.reset.poke(true.B)
          |      dut.clock.step()
          |
          |      // write valid signal
          |      dut.io.S_AXI_AWVALID.poke(true.B)
          |      dut.io.S_AXI_AWADDR.poke(0.U)
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_WVALID.poke(true.B)
          |      dut.io.S_AXI_WDATA.poke(1.S)
          |      dut.io.S_AXI_WSTRB.poke("b1111".U)
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_BREADY.poke(true.B)
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_AWVALID.poke(false.B)
          |      dut.io.S_AXI_WVALID.poke(false.B)
          |      dut.io.S_AXI_BREADY.poke(false.B)
          |
          |      for(i <- 0 until(${cycles})) {
          |        dut.clock.step()
          |      }
          |
          |      // read ready signals
          |      dut.io.S_AXI_ARVALID.poke(true.B)
          |      dut.io.S_AXI_ARADDR.poke(4.U)
          |      dut.clock.step()
          |
          |      dut.io.S_AXI_RREADY.poke(true.B)
          |      dut.clock.step(20)
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
          |                                        C_S_AXI_ADDR_WIDTH  = C_S_AXI_ADDR_WIDTH ,
          |                                        ARRAY_REG_WIDTH     = ARRAY_REG_WIDTH    ,
          |                                        ARRAY_REG_DEPTH     = ARRAY_REG_DEPTH    ,
          |                                        ${if(!anvil.config.splitTempSizes) "GENERAL_REG_WIDTH   = GENERAL_REG_WIDTH  ," else ""}
          |                                        ${if(!anvil.config.splitTempSizes) "GENERAL_REG_DEPTH   = GENERAL_REG_DEPTH  ," else ""}
          |                                        STACK_POINTER_WIDTH = STACK_POINTER_WIDTH,
          |                                        CODE_POINTER_WIDTH  = CODE_POINTER_WIDTH  ))
          |    mod${name}.io.valid := Mux(io_valid_reg(0) & (io_ready_reg === 0.U), true.B, false.B)
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

      val moduleDeclST: ST = {
        var moduleST: ISZ[ST] = ISZ()
        for(i <- 0 until ipModules.size) {
          moduleST = moduleST :+ ipModules(i).moduleST
        }

        if(!anvil.config.noXilinxIp) {
          moduleST = moduleST :+ divisionBlackBoxST
          moduleST = moduleST :+ multiplierBlackBoxST
          moduleST = moduleST :+ adderSubtractorBlackBoxST
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
        st"""${(instanceST, "\n")}"""
      }

      val instancePortFuncST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for(entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insPortFuncST(b, entry._2)
        }
        instanceST = instanceST :+ insPortFuncST(IntrinsicIP(HwSynthesizer.defaultIndexing), ipAlloc.indexingAllocSize)
        st"""${(instanceST, "\n")}"""
      }

      val instancePortCallST: ST = {
        var instanceST: ISZ[ST] = ISZ()
        for(entry <- ipAlloc.binopAllocSizeMap.entries) {
          val b: IpType = BinaryIP(entry._1._2, entry._1._1)
          instanceST = instanceST :+ insPortCallST(b, entry._2)
        }
        instanceST = instanceST :+ insPortCallST(IntrinsicIP(HwSynthesizer.defaultIndexing), ipAlloc.indexingAllocSize)
        st"""${(instanceST, "\n")}"""
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
          |    val ${sharedMemName} = RegInit(VecInit(Seq.fill(ARRAY_REG_DEPTH)(0.U(ARRAY_REG_WIDTH.W))))
          |    // reg for general purpose
          |    ${if (!anvil.config.splitTempSizes) s"val ${generalRegName} = RegInit(VecInit(Seq.fill(GENERAL_REG_DEPTH)(0.U(GENERAL_REG_WIDTH.W))))" else s"${generalPurposeRegisterST.render}"}
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
          |    ${if(anvil.config.useIP) "val indexerValid = RegInit(false.B)" else ""}
          |
          |    ${if(anvil.config.useIP) instanceDeclST else st""}
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
          |    io.ready := Mux(CP === 0.U, 1.U, 0.U) | Mux(CP === 1.U, 2.U, 0.U)
          |
          |    ${(stateMachineST, "")}
          |}
          |
          |object ${name} {
          |  def init(o: ${name}) {
          |    import o._
          |    ${if(anvil.config.useIP) instancePortFuncST else st""}
          |    ${if(anvil.config.useIP) instancePortCallST else st""}
          |  }
          |}
          |${(stateFunctionObjectST, "\n")}
          |
          |${if (anvil.config.axi4) axi4WrapperST().render else ""}
          """
    }

    val basicBlockST = processBasicBlock(name, o.body.asInstanceOf[AST.IR.Body.Basic].blocks)

    return procedureST(basicBlockST._1, basicBlockST._2)
  }

  @pure def processBasicBlock(name: String, bs: ISZ[AST.IR.BasicBlock]): (ST, ST) = {
    val ipPortLogic = HwSynthesizer.IpPortAssign(anvil, ipAlloc, ISZ[ST](), ipModules, InputMap.empty, ISZ[ST](), ISZ[ST]())
    @strictpure def basicBlockST(grounds: ISZ[ST], functions: ISZ[ST]): (ST, ST) =
      (st"""
          |switch(CP) {
          |  is(2.U) {
          |    CP := Mux(io.valid, 3.U, CP)
          |  }
          |  ${(grounds, "")}
          |}""",
        st"""
            |${(functions, "")}"""
      )

    @pure def groundST(b: AST.IR.BasicBlock, ground: ST, jump: ST): (ST, ST) = {
      var commentST = ISZ[ST]()

      for(g <- b.grounds) {
        commentST = commentST :+ g.prettyST(anvil.printer)
      }
      commentST = commentST :+ b.jump.prettyST(anvil.printer)

      val jumpST: ST = {
        if(IndexingLog.isIndexingInBlock() && !MemCopyLog.isMemCopyInBlock()) {
          val jST = processJumpIntrinsic(BlockLog.getBlock, ipPortLogic)
          val indexerName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get
          st"""
              |when(${indexerName}_${IndexingLog.activeIndex}.io.valid) {
              |  ${jST.render}
              |  ${indexerName}_${IndexingLog.activeIndex}.io.ready := false.B
              |}
            """
        }
        else if(!MemCopyLog.isMemCopyInBlock()) {
          jump
        } else {
          st""
        }
      }

      if(b.label > 1) {
        val functionDefinitionST: ST =
          st"""
              |object Block_${b.label} {
              |  def block_${b.label}(o: ${name}) {
              |    import o._
              |    /*
              |    ${(commentST, "\n")}
              |    */
              |    ${(ground, "")}
              |    ${jumpST}
              |  }
              |}
              """
        val functionCallST: ST =
          st"""
              |is(${b.label}.U) {
              |  Block_${b.label}.block_${b.label}(this)
              |}
              """
        return (functionCallST, functionDefinitionST)
      } else {
        return (st"", st"")
      }
    }

    var allGroundsST = ISZ[ST]()
    var allFunctionsST = ISZ[ST]()

    for (b <- bs) {
      BlockLog.setBlock(b)

      if(b.label != 0) {
        val processedGroundST = processGround(b.grounds, ipPortLogic)
        var jump = processJumpIntrinsic(b, ipPortLogic)
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

        allGroundsST = allGroundsST :+ g._1
        allFunctionsST = allFunctionsST :+ g._2
      }

      IndexingLog.disableFlagIndexingInBlock()
      MemCopyLog.disableFlagMemCopyInBlock()

    }

    return basicBlockST(allGroundsST, allFunctionsST)
  }

  @pure def processGround(gs: ISZ[AST.IR.Stmt.Ground], ipPortLogic: HwSynthesizer.IpPortAssign): ST = {
    var groundST = ISZ[ST]()

    for(g <- gs) {
      g match {
        case g: AST.IR.Stmt.Assign => {
          groundST = groundST :+ processStmtAssign(g, ipPortLogic)
        }
        case g: AST.IR.Stmt.Intrinsic => {
          groundST = groundST :+ processStmtIntrinsic(g, ipPortLogic)
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

    return st"""
               |${(groundST, "\n")}"""
  }

  @pure def processJumpIntrinsic(b: AST.IR.BasicBlock, ipPortLogic: HwSynthesizer.IpPortAssign): ST = {
    var intrinsicST: ISZ[ST] = ISZ[ST]()
    val j = b.jump

    j match {
      case AST.IR.Jump.Intrinsic(intrinsic: Intrinsic.GotoLocal) => {
        if (intrinsic.isTemp) {
          intrinsicST = intrinsicST :+
            st"""
                |CP := ${processExpr(AST.IR.Exp.Temp(intrinsic.loc, anvil.cpType, intrinsic.pos), F, ipPortLogic)}
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

          intrinsicST = intrinsicST :+
            st"""
                |CP := Cat(
                |  ${(returnAddrST, "\n")}
                |)
            """
        }
      }
      case j: AST.IR.Jump.Goto => {
        intrinsicST = intrinsicST :+ st"CP := ${j.label}.U"
      }
      case j: AST.IR.Jump.If => {
        val cond = processExpr(j.cond, F, ipPortLogic)
        intrinsicST = intrinsicST :+ st"CP := Mux((${cond.render}.asUInt) === 1.U, ${j.thenLabel}.U, ${j.elseLabel}.U)"
      }
      case j: AST.IR.Jump.Switch => {
        val condExprST = processExpr(j.exp, F, ipPortLogic)

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
                |is(${processExpr(i.value, F, ipPortLogic).render}) {
                |  CP := ${i.label}.U
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

  @pure def processStmtIntrinsic(i: AST.IR.Stmt.Intrinsic, ipPortLogic: HwSynthesizer.IpPortAssign): ST = {
    var intrinsicST = st""

    i match {
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.TempLoad) => {
        var internalST = ISZ[ST]()
        val rhsOffsetST = processExpr(intrinsic.rhsOffset, F, ipPortLogic)
        val tmpWire = st"__tmp_${TmpWireCount.getCurrent}"

        for(i <- (intrinsic.bytes - 1) to 0 by -1) {
          if(i == 0) {
            internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U)"
          } else {
            internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U),"
          }
        }

        val padST = st".asSInt.pad(${if(!anvil.config.splitTempSizes) "GENERAL_REG_WIDTH" else s"${anvil.typeBitSize(intrinsic.tipe)}"})"
        val placeholder: String = if(IndexingLog.isIndexingInBlock()) "  " else ""
        val indexerInstanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get

        intrinsicST =
          st"""
              |val ${tmpWire} = (${rhsOffsetST.render}).asUInt
              |${if(IndexingLog.isIndexingInBlock()) s"when(${indexerInstanceName}_${IndexingLog.activeIndex}.io.valid){" else ""}
              |${placeholder}${if(!anvil.config.splitTempSizes) s"${generalRegName}(${intrinsic.temp}.U)" else s"${getGeneralRegName(intrinsic.tipe)}(${intrinsic.temp}.U)"} := Cat(
              |  ${placeholder}${(internalST, "\n")}
              |)${placeholder}${if(intrinsic.isSigned) s"${padST.render}" else ""}${if(!anvil.config.splitTempSizes) ".asUInt" else ""}
              |${if(IndexingLog.isIndexingInBlock()) "}" else ""}
            """
        TmpWireCount.incCount()
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Copy) => {
        MemCopyLog.enableFlagMemCopyInBlock()

        // acquire the source and destination address
        val lhsAddrST = processExpr(intrinsic.lhsOffset, F, ipPortLogic)
        val rhsAddrST = processExpr(intrinsic.rhs, F, ipPortLogic)

        val tmpWireLhsST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()
        val tmpWireRhsST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()
        val totalSizeWireST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()
        val leftByteStartST = st"__tmp_${TmpWireCount.getCurrent}"
        TmpWireCount.incCount()

        // compute how many bytes needed for memory copy transfer
        val rhsBytesSt = processExpr(intrinsic.rhsBytes, F, ipPortLogic)
        var BytesTransferST = ISZ[ST]()
        for(i <- 0 to (anvil.config.copySize - 1)) {
          BytesTransferST = BytesTransferST :+ st"${sharedMemName}(${tmpWireLhsST.render} + Idx + ${i}.U) := ${sharedMemName}(${tmpWireRhsST.render} + Idx + ${i}.U)"
        }

        // get the jump statement ST
        val jumpST = processJumpIntrinsic(BlockLog.getBlock, ipPortLogic)
        val indexerInstanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get
        val indexerReadyDisableStr: String = if(IndexingLog.isIndexingInBlock()) s"${indexerInstanceName}_${IndexingLog.activeIndex}.io.ready := false.B" else ""
        val indexerValidStr: String = if(IndexingLog.isIndexingInBlock()) s"when(${indexerInstanceName}_${IndexingLog.activeIndex}.io.valid) {indexerValid := true.B; ${indexerReadyDisableStr}}" else ""
        val indexerConditionStr: String = if(IndexingLog.isIndexingInBlock()) "indexerValid & " else ""

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
              |} ${if(IndexingLog.isIndexingInBlock()) ".elsewhen(indexerValid) {" else ".otherwise {"}
              |  Idx := 0.U
              |  IdxLeftByteRounds := 0.U
              |  LeftByteRounds := 0.U
              |  ${jumpST.render}
              |  ${if(IndexingLog.isIndexingInBlock()) "indexerValid := false.B" else ""}
              |}
            """
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Store) => {
        @strictpure def isLhsOffsetIndexing(e: AST.IR.Exp): B = e match {
          case AST.IR.Exp.Intrinsic(in: Intrinsic.Indexing) => T
          case _ => F
        }
        val lhsOffsetST = processExpr(intrinsic.lhsOffset, F, ipPortLogic)
        val rhsST = processExpr(intrinsic.rhs, intrinsic.isSigned, ipPortLogic)
        var shareMemAssign = ISZ[ST]()
        val tmpWireLhsST = st"__tmp_${TmpWireCount.getCurrent}"
        val tmpWireRhsST = st"__tmp_${TmpWireCount.getCurrent + 1}"
        val tmpWireRhsContent: ST = if(isIntExp(intrinsic.rhs)) {
          st"${rhsST}"
        } else {
          rhsST
        }

        if(isLhsOffsetIndexing(intrinsic.lhsOffset)) {
          val indexerInstanceName: String = getIpInstanceName(IntrinsicIP(defaultIndexing)).get
          shareMemAssign = shareMemAssign :+
            st"when(${indexerInstanceName}_${IndexingLog.activeIndex}.io.valid){"
        }

        for(i <- 0 to (intrinsic.bytes - 1) by 1) {
          shareMemAssign = shareMemAssign :+
            st"${if(isLhsOffsetIndexing(intrinsic.lhsOffset)) "  " else ""}${sharedMemName}(${tmpWireLhsST} + ${i}.U) := ${tmpWireRhsST}(${(i) * 8 + 7}, ${(i) * 8})"
        }

        if(isLhsOffsetIndexing(intrinsic.lhsOffset)) {
          shareMemAssign = shareMemAssign :+
            st"}"
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
        if(anvil.config.useIP) {
          var leftST: ST = st""
          var rightST: ST = st""
          var isPlus: B = F
          val regValueST: ST = processExpr(intrinsic.value, F, ipPortLogic)
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
            insertIPInput(ipT, populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
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
            case AST.IR.Exp.Int(_, v, _) => if (intrinsic.isInc) if (v < 0) st"${targetReg} - ${-v}.U" else st"${targetReg} + ${v}.U" else st"${processExpr(intrinsic.value, F, ipPortLogic)}"
            case _ => if (intrinsic.isInc) st"${targetReg} + ${processExpr(intrinsic.value, F, ipPortLogic)}" else st"${processExpr(intrinsic.value, F, ipPortLogic)}"
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

  @pure def processStmtAssign(a: AST.IR.Stmt.Assign, ipPortLogic: HwSynthesizer.IpPortAssign): ST = {
    var assignST: ST = st""

    @strictpure def isIntrinsicLoad(e: AST.IR.Exp): B = e match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => T
      case _ => F
    }

    a match {
      case a: AST.IR.Stmt.Assign.Temp => {
        val regNo = a.lhs
        val lhsST: ST = if(!anvil.config.splitTempSizes)  st"${generalRegName}(${regNo}.U)" else st"${getGeneralRegName(a.rhs.tipe)}(${regNo}.U)"
        val rhsST = processExpr(a.rhs, F, ipPortLogic)
        if(isIntrinsicLoad(a.rhs)) {
          assignST =
            st"""
                |${lhsST} := Cat{
                |  ${rhsST.render}
                |}
                """
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

  @pure def processExpr(exp: AST.IR.Exp, isForcedSign: B, ipPortLogic: HwSynthesizer.IpPortAssign): ST = {
    var exprST = st""

    exp match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Register) => {
        exprST = if(intrinsic.isSP) st"SP" else st"DP"
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => {
        var rhsExprST = ISZ[ST]()
        val rhsExpr = processExpr(intrinsic.rhsOffset, F, ipPortLogic)
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
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Indexing) => {
        IndexingLog.enableFlagIndexingInBlock()
        val allocIndex = getIpAllocIndex(exp)
        IndexingLog.activeIndex = allocIndex

        val baseOffsetST: ST = processExpr(intrinsic.baseOffset, F, ipPortLogic)
        val dataOffset: Z = intrinsic.dataOffset
        val indexST: ST = processExpr(intrinsic.index, F, ipPortLogic)
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

        insertIPInput(IntrinsicIP(defaultIndexing), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
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
        exprST = st"${processExpr(exp.exp, F, ipPortLogic)}${if(anvil.isSigned(exp.t)) ".asSInt" else ".asUInt"}${if(!anvil.config.splitTempSizes) "" else splitStr}"
      }
      case exp: AST.IR.Exp.Unary => {
        val variableST = processExpr(exp.exp, F, ipPortLogic)
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
        val leftST = st"${processExpr(exp.left, F, ipPortLogic).render}${if(isSIntOperation && (!isSignedExp(exp.left))) ".asSInt" else ""}"
        val rightST = st"${processExpr(exp.right, F, ipPortLogic).render}${if(isSIntOperation && (!isSignedExp(exp.right))) ".asSInt" else ""}"
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Add, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Sub, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
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
            insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Mul, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
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
            insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Div, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
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
            insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Rem, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
            ipPortLogic.whenCondST = ipPortLogic.whenCondST :+ st"${indexerInstanceName}_${allocIndex}.io.valid"
            //ipPortLogic.whenStmtST = ipPortLogic.whenStmtST :+ st"${indexerInstanceName}_${allocIndex}.io.start := RegNext(false.B)"
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.And, signed), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.And, signed)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Or, signed), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Or, signed)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Xor, signed), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Xor, signed)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Eq, signed), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Eq, signed)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Ne, signed), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Ne, signed)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Ge, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Ge, isSIntOperation)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Gt, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Gt, isSIntOperation)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Le, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Le, isSIntOperation)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Lt, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Lt, isSIntOperation)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Shr, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Shr, isSIntOperation)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Ushr, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Ushr, isSIntOperation)).get
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
              insertIPInput(BinaryIP(AST.IR.Exp.Binary.Op.Shl, isSIntOperation), populateInputs(BlockLog.getBlock.label, hashSMap, allocIndex), ipPortLogic.inputMap)
              val indexerInstanceName: String = getIpInstanceName(BinaryIP(AST.IR.Exp.Binary.Op.Shl, isSIntOperation)).get
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
    override def pre_langastIRExpBinary(o: Exp.Binary): MAnvilIRTransformer.PreResult[IR.Exp] = {
      @pure def inputLogic(ipt: IpType): Unit = {
        val instanceIndex: Z = ipAlloc.allocMap.get(Util.IpAlloc.Ext.exp(o)).get
        val instanceName: String = getIpInstanceName(ipt).get
        val inputs: HashSMap[Z, HashSMap[String, ChiselModule.Input]] = getInputPort(ipt)
        val h: HashSMap[String, ChiselModule.Input] = inputs.get(instanceIndex).get
        for (entry <- h.entries) {
          sts = sts :+ st"${instanceName}_${instanceIndex}.io.${entry._1} := ${entry._2.stateValue.value}"
        }
      }
      val signed: B = isSignedExp(o.left) || isSignedExp(o.right)
      if(anvil.config.useIP) {
        inputLogic(BinaryIP(o.op, signed))
      }
      return MAnvilIRTransformer.PreResult_langastIRExpBinary
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