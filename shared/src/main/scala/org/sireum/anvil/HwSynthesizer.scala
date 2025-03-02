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
import org.sireum.lang.symbol.Resolver.{QName, typeParamMap}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}

@datatype class HwSynthesizer(val anvil: Anvil) {

  val sharedMemName: String = "arrayRegFiles"
  val generalRegName: String = "generalRegFiles"
  var tmpWireCount = 0;
  /*
    Notes/links:
    * Slang IR: https://github.com/sireum/slang/blob/master/ast/shared/src/main/scala/org/sireum/lang/ast/IR.scala
    * Anvil IR Intrinsic: https://github.com/sireum/anvil/blob/master/shared/src/main/scala/org/sireum/anvil/Intrinsic.scala
   */
  def printProcedure(name: String, o: AST.IR.Procedure, globalSize: Z, maxRegisters: Z): HashSMap[ISZ[String], ST] = {
    var r = HashSMap.empty[ISZ[String], ST]
    val processedProcedureST = processProcedure(name, o, maxRegisters)
    r = r + ISZ(name) ~> processedProcedureST
    //r = r + ISZ(name) ~> o.prettyST
    return r
  }

  @pure def processProcedure(name: String, o: AST.IR.Procedure, maxRegisters: Z): ST = {

    @strictpure def procedureST(stateMachineST: ST): ST =
      st"""
          |import chisel3._
          |import chisel3.util._
          |import chisel3.experimental._
          |
          |class ${name} (val C_S_AXI_DATA_WIDTH:  Int = 32,
          |           val C_S_AXI_ADDR_WIDTH:  Int = 32,
          |           val ARRAY_REG_WIDTH:     Int = 8,
          |           val ARRAY_REG_DEPTH:     Int = ${anvil.config.memory},
          |           val GENERAL_REG_WIDTH:   Int = 64,
          |           val GENERAL_REG_DEPTH:   Int = ${maxRegisters},
          |           val STACK_POINTER_WIDTH: Int = ${anvil.spTypeByteSize},
          |           val CODE_POINTER_WIDTH:  Int = ${anvil.cpTypeByteSize}) extends Module {
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
          |    val ${sharedMemName} = Reg(Vec(1 << log2Ceil(ARRAY_REG_DEPTH), UInt(ARRAY_REG_WIDTH.W)))
          |    // reg for general purpose
          |    val ${generalRegName} = Reg(Vec(1 << log2Ceil(GENERAL_REG_DEPTH), UInt(GENERAL_REG_WIDTH.W)))
          |    // reg for code pointer
          |    val CP = RegInit(1.U(CODE_POINTER_WIDTH.W))
          |    // reg for stack pointer
          |    val SP = RegInit(0.S(STACK_POINTER_WIDTH.W))
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
          |    ${(stateMachineST,"")}
          |
          |}"""

    val basicBlockST = processBasicBlock(o.body.asInstanceOf[AST.IR.Body.Basic].blocks)

    println(
      st"""
          |${(procedureST(basicBlockST),"")}
          |""".render
    )

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

    @strictpure def groundST(b: AST.IR.BasicBlock, ground: ST, jump: ST): ST =
      st"""
          |is(${b.label}.U) {
          |  ${(ground, "")}
          |  ${jump.render}
          |}
        """

    var groundsST = ISZ[ST]()

    for (b <- bs) {
      println(b)
      if(b.label != 0) {
        val jump = processJumpIntrinsic(b)
        groundsST = groundsST :+ groundST(b, processGround(b.grounds), jump)
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
        var returnAddrST = ISZ[ST]()

        for(i <- 7 to 0 by -1) {
          if(i == 0) {
            returnAddrST = returnAddrST :+ st"${sharedMemName}((SP + ${intrinsic.offset}.S + ${i}.S).asUInt)"
          } else {
            returnAddrST = returnAddrST :+ st"${sharedMemName}((SP + ${intrinsic.offset}.S + ${i}.S).asUInt),"
          }
        }

        intrinsicST =
          st"""
              |CP := Cat(
              |  ${(returnAddrST, "\n")}
              |)
            """
      }
      case j: AST.IR.Jump.Goto => {
        intrinsicST = st"CP := ${j.label}.U"
      }
      case j: AST.IR.Jump.If => {
        val cond = processExpr(j.cond, F)
        intrinsicST = st"CP := Mux(${cond.render}, ${j.thenLabel}.U, ${j.elseLabel}.U)"
      }
      case j: AST.IR.Jump.Return => {
      }
      case _ => {
        halt(s"processJumpIntrinsic unimplemented")
      }
    }

    return intrinsicST
  }

  @pure def processStmtIntrinsic(i: AST.IR.Stmt.Intrinsic): ST = {
    var intrinsicST = st""

    @strictpure def isRhsIntType(exp: AST.IR.Exp): B = exp match {
      case exp: AST.IR.Exp.Int => T
      case _ => F
    }

    i match {
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.TempLoad) => {
        var internalST = ISZ[ST]()
        val rhsOffsetST = processExpr(intrinsic.rhsOffset, T)
        val tmpWire = st"__tmp_${tmpWireCount}"

        for(i <- (intrinsic.bytes - 1) to 0 by -1) {
          if(i == 0) {
            internalST = internalST :+ st"${sharedMemName}((${tmpWire} + ${i}.S).asUInt)"
          } else {
            internalST = internalST :+ st"${sharedMemName}((${tmpWire} + ${i}.S).asUInt),"
          }
        }

        intrinsicST =
          st"""
              |val ${tmpWire} = ${rhsOffsetST.render}
              |${generalRegName}(${intrinsic.temp}) := Cat(
              |  ${(internalST, "\n")}
              |)
            """
        tmpWireCount = tmpWireCount + 1
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Copy) => {
        halt(s"processStmtIntrinsic Intrinsic.Copy unimplemented")
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Store) => {
        val lhsOffsetST = processExpr(intrinsic.lhsOffset, T)
        val rhsST = processExpr(intrinsic.rhs, intrinsic.isSigned)
        var shareMemAssign = ISZ[ST]()
        val tmpWireLhs = st"__tmp_${tmpWireCount}"
        val tmpWireRhs = st"__tmp_${tmpWireCount + 1}"
        val tmpWireRhsContent: ST = if(isRhsIntType(intrinsic.rhs)) {
          st"${rhsST}(${intrinsic.bytes * 8}.W)"
        } else {
          rhsST
        }

        for(i <- 1 to intrinsic.bytes by 1) {
          shareMemAssign = shareMemAssign :+
            st"${sharedMemName}((${tmpWireLhs} + ${i}.S).asUInt) := ${tmpWireRhs}(${(i-1)*8+7}, ${(i-1)*8})"
        }

        intrinsicST =
          st"""
              |val ${tmpWireLhs} = ${lhsOffsetST.render}
              |val ${tmpWireRhs} = ${tmpWireRhsContent.render}
              |${(shareMemAssign, "\n")}
            """
        tmpWireCount = tmpWireCount + 2
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.RegisterAssign) => {
        val targetReg: String = if(intrinsic.isSP) "SP" else "DP"
        val updateContentST: ST =
          if(intrinsic.isInc)
            if(intrinsic.value < 0) st"${targetReg} - ${-intrinsic.value}.S"
            else st"${targetReg} + ${intrinsic.value}.S"
          else st"${intrinsic.value}.S"

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

  @pure def processStmtAssign(a: AST.IR.Stmt.Assign): ST = {
    var assignST: ST = st""

    @strictpure def isIntrinsicLoad(e: AST.IR.Exp): B = e match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => T
      case _ => F
    }

    a match {
      case a: AST.IR.Stmt.Assign.Temp => {
        val regNo = a.lhs
        val lhsST = st"${generalRegName}(${regNo}.U)"
        val rhsST = processExpr(a.rhs, F)
        if(isIntrinsicLoad(a.rhs)) {
          assignST =
            st"""
                |${lhsST} := Cat{
                |  ${rhsST.render}
                |}"""
        } else {
          assignST =
            st"""
                |${lhsST} := ${rhsST.render}"""
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

  @pure def processExpr(exp: AST.IR.Exp, isSPIndexed: B): ST = {
    var exprST = st""

    exp match {
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Register) => {
        exprST = if(intrinsic.isSP) st"SP" else st"DP"
      }
      case AST.IR.Exp.Intrinsic(intrinsic: Intrinsic.Load) => {
        val rhsExpr = processExpr(intrinsic.rhsOffset, T)
        for(i <- intrinsic.bytes-1 to 0 by -1) {
          if(i == 0) {
            exprST = st"${sharedMemName}((${rhsExpr.render} + ${i}.U).asUInt)"
          } else {
            exprST = st"${sharedMemName}((${rhsExpr.render} + ${i}.U).asUInt),"
          }
        }
      }
      case exp: AST.IR.Exp.Temp => {
        val indexPostfix: String = if(anvil.isSigned(exp.tipe)) ".asUInt" else ".U"
        exprST = st"${generalRegName}(${exp.n}${indexPostfix})"
      }
      case exp: AST.IR.Exp.Int => {
        val valuePostfix: String = isSPIndexed match {
          case T => "S"
          case _ => if(anvil.isSigned(exp.tipe)) "S" else "U"
        }
        exprST = st"${exp.value}.${valuePostfix}"
      }
      case exp: AST.IR.Exp.Binary => {
        val leftST = processExpr(exp.left, isSPIndexed)
        val rightST = processExpr(exp.right, isSPIndexed)
        exp.op match {
          case AST.IR.Exp.Binary.Op.Add => {
            exprST = st"${leftST.render} + ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Sub => {
            exprST = st"${leftST.render} - ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Mul => {
            exprST = st"${leftST.render} * ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Div => {
            exprST = st"${leftST.render} / ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Rem => {
            exprST = st"${leftST.render} % ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.And => {
            exprST = st"${leftST.render} & ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Or  => {
            exprST = st"${leftST.render} | ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Xor => {
            exprST = st"${leftST.render} ^ ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.CondAnd => {
            if(isBoolType(exp.tipe)) {
              exprST = st"${leftST.render} && ${rightST.render}"
            } else if(is1BitVector(exp.tipe)) {
              exprST = st"${leftST.render}.asBool && ${rightST.render}.asBool"
            } else {
              halt(s"processExpr, you got an error about Op.CondAnd")
            }
          }
          case AST.IR.Exp.Binary.Op.CondOr => {
            if(isBoolType(exp.tipe)) {
              exprST = st"${leftST.render} || ${rightST.render}"
            } else if(is1BitVector(exp.tipe)) {
              exprST = st"${leftST.render}.asBool || ${rightST.render}.asBool"
            } else {
              halt(s"processExpr, you got an error about Op.CondOr")
            }
          }
          case AST.IR.Exp.Binary.Op.Eq => {
            exprST = st"${leftST.render} === ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Ne => {
            exprST = st"${leftST.render} =/= ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Ge => {
            exprST = st"${leftST.render} <= ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Gt => {
            exprST = st"${leftST.render} < ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Le => {
            exprST = st"${leftST.render} <= ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Lt => {
            exprST = st"${leftST.render} < ${rightST.render}"
          }
          case AST.IR.Exp.Binary.Op.Shr => {
            val right: ST = if(anvil.isSigned(exp.right.tipe)) st"(${rightST}).asUInt" else rightST
            exprST = st"${leftST.render} >> ${right.render}"
          }
          case AST.IR.Exp.Binary.Op.Ushr => {
            val right: ST = if(anvil.isSigned(exp.right.tipe)) st"(${rightST}).asUInt" else rightST
            exprST = st"(${leftST.render}).asUInt >> ${right.render}"
          }
          case AST.IR.Exp.Binary.Op.Shl => {
            val right: ST = if(anvil.isSigned(exp.right.tipe)) st"(${rightST}).asUInt" else rightST
            exprST = st"${leftST.render} << ${right.render}"
          }
          case _ => {
            halt(s"processExpr AST.IR.Exp.Binary unimplemented")
          }
        }
      }
      case _ => {
        halt(s"processExpr unimplemented, ${exp.prettyST.render}")
      }
    }

    return exprST
  }
}