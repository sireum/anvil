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

object TmpWireCount {
  var count: Z = 0
  def getCurrent: Z = {
    return count
  }
  def incCount(): Unit = {
    count = count + 1
  }
}

object MemCopyLog {
  //@strictpure def currentBlock(b: AST.IR.BasicBlock): AST.IR.BasicBlock = b
  var currentBlock: MOption[AST.IR.BasicBlock] = MNone()
  var isMemCopyInBlock: B = F
}

@datatype class HwSynthesizer(val anvil: Anvil) {
  val sharedMemName: String = "arrayRegFiles"
  val generalRegName: String = "generalRegFiles"
  /*
    Notes/links:
    * Slang IR: https://github.com/sireum/slang/blob/master/ast/shared/src/main/scala/org/sireum/lang/ast/IR.scala
    * Anvil IR Intrinsic: https://github.com/sireum/anvil/blob/master/shared/src/main/scala/org/sireum/anvil/Intrinsic.scala
   */
  def printProcedure(name: String, o: AST.IR.Procedure, output: Anvil.Output, maxRegisters: Z): Unit = {
    var r = HashSMap.empty[ISZ[String], ST]
    val processedProcedureST = processProcedure(name, o, maxRegisters)
    r = r + ISZ(name) ~> o.prettyST
    output.add(T, ISZ("ir", s"chisel-${name}.scala"), processedProcedureST)
    return
  }
  @pure def processProcedure(name: String, o: AST.IR.Procedure, maxRegisters: Z): ST = {

    @strictpure def procedureST(stateMachineST: ST): ST =
      st"""
          |import chisel3._
          |import chisel3.util._
          |import chisel3.experimental._
          |
          |class ${name} (val C_S_AXI_DATA_WIDTH:  Int = 32,
          |               val C_S_AXI_ADDR_WIDTH:  Int = 32,
          |               val ARRAY_REG_WIDTH:     Int = 8,
          |               val ARRAY_REG_DEPTH:     Int = ${anvil.config.memory},
          |               val GENERAL_REG_WIDTH:   Int = 64,
          |               val GENERAL_REG_DEPTH:   Int = ${maxRegisters},
          |               val STACK_POINTER_WIDTH: Int = ${anvil.spTypeByteSize*8},
          |               val CODE_POINTER_WIDTH:  Int = ${anvil.cpTypeByteSize*8}) extends Module {
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
          |    val CP = RegInit(2.U(CODE_POINTER_WIDTH.W))
          |    // reg for stack pointer
          |    val SP = RegInit(0.U(STACK_POINTER_WIDTH.W))
          |    // reg for display pointer
          |    val DP = RegInit(0.U(STACK_POINTER_WIDTH.W))
          |    // reg for index in memcopy
          |    val Idx = RegInit(0.U(16.W))
          |    // reg for recording how many rounds needed for the left bytes
          |    val LeftByteRounds = RegInit(0.U(8.W))
          |    val IdxLeftByteRounds = RegInit(0.U(8.W))
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

    @pure def groundST(b: AST.IR.BasicBlock, ground: ST, jump: ST): ST = {
      var commentST = ISZ[ST]()

      for(g <- b.grounds) {
        commentST = commentST :+ g.prettyST
      }
      commentST = commentST :+ b.jump.prettyST

      if(b.label > 1) {
        return st"""
                   |is(${b.label}.U) {
                   |  /*
                   |  ${(commentST, "\n")}
                   |  */
                   |  ${(ground, "")}
                   |  ${if(!MemCopyLog.isMemCopyInBlock) jump.render else st""}
                   |}
                 """
      } else {
        return st""
      }
    }

    var groundsST = ISZ[ST]()

    for (b <- bs) {
      MemCopyLog.currentBlock = MSome(b)

      if(b.label != 0) {
        val jump = processJumpIntrinsic(b)
        groundsST = groundsST :+ groundST(b, processGround(b.grounds), jump)
      }

      if(MemCopyLog.isMemCopyInBlock) {
        MemCopyLog.isMemCopyInBlock = F
      } else {
        MemCopyLog.isMemCopyInBlock = F
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
        val offsetST: ST = if(intrinsic.offset < 0) st"- ${-intrinsic.offset}" else st"+ ${intrinsic.offset}"

        for(i <- (anvil.cpTypeByteSize - 1) to 0 by -1) {
          if(i == 0) {
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
      case j: AST.IR.Jump.Goto => {
        intrinsicST = st"CP := ${j.label}.U"
      }
      case j: AST.IR.Jump.If => {
        println(j.prettyST.render)
        val cond = processExpr(j.cond, F)
        intrinsicST = st"CP := Mux((${cond.render}.asUInt) === 1.U, ${j.thenLabel}.U, ${j.elseLabel}.U)"
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
        val rhsOffsetST = processExpr(intrinsic.rhsOffset, F)
        val tmpWire = st"__tmp_${TmpWireCount.getCurrent}"

        for(i <- (intrinsic.bytes - 1) to 0 by -1) {
          if(i == 0) {
            internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U)"
          } else {
            internalST = internalST :+ st"${sharedMemName}(${tmpWire} + ${i}.U),"
          }
        }

        intrinsicST =
          st"""
              |val ${tmpWire} = (${rhsOffsetST.render}).asUInt
              |${generalRegName}(${intrinsic.temp}.U) := Cat(
              |  ${(internalST, "\n")}
              |).asUInt
            """
        TmpWireCount.incCount()
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.Copy) => {
        MemCopyLog.isMemCopyInBlock = T

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
        val jumpST = processJumpIntrinsic(MemCopyLog.currentBlock.get)

        intrinsicST =
          st"""
              |val ${tmpWireLhsST.render} = ${lhsAddrST.render}
              |val ${tmpWireRhsST.render} = ${rhsAddrST.render}
              |val ${totalSizeWireST.render} = ${rhsBytesSt.render}
              |
              |when(Idx < ${totalSizeWireST.render}) {
              |  ${(BytesTransferST, "\n")}
              |  Idx := Idx + ${anvil.config.copySize}.U
              |  LeftByteRounds := ${totalSizeWireST.render} - Idx - 8.U
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
        val tmpWireRhsContent: ST = if(isRhsIntType(intrinsic.rhs)) {
          st"${rhsST}(${intrinsic.bytes * 8}.W)"
        } else {
          rhsST
        }

        for(i <- 0 to (intrinsic.bytes - 1) by 1) {
          shareMemAssign = shareMemAssign :+
            st"${sharedMemName}(${tmpWireLhsST} + ${i}.U) := ${tmpWireRhsST}(${(i)*8+7}, ${(i)*8})"
        }

        intrinsicST =
          st"""
              |val ${tmpWireLhsST} = ${lhsOffsetST.render}
              |val ${tmpWireRhsST} = (${tmpWireRhsContent.render}).asUInt
              |${(shareMemAssign, "\n")}
            """
        TmpWireCount.incCount()
        TmpWireCount.incCount()
      }
      case AST.IR.Stmt.Intrinsic(intrinsic: Intrinsic.RegisterAssign) => {
        val targetReg: String = if(intrinsic.isSP) "SP" else "DP"
        val updateContentST: ST = intrinsic.value match {
          case AST.IR.Exp.Int(_, v, _) => if (intrinsic.isInc) if (v < 0) st"${targetReg} - ${-v}.U" else st"${targetReg} + ${v}.U" else st"${processExpr(intrinsic.value, F)}"
          case _ => processExpr(intrinsic.value, F)
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
                |${lhsST} := ${if(isSignedExp(a.rhs)) "(" else ""}${rhsST.render}${if(isSignedExp(a.rhs)) ").asUInt" else ""}"""
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
              |)${if(anvil.isSigned(intrinsic.tipe)) ".asSInt" else ""}"""
      }
      case exp: AST.IR.Exp.Temp => {
        exprST = st"${generalRegName}(${exp.n}.U)${if(isSignedExp(exp)) ".asSInt" else ""}"
      }
      case exp: AST.IR.Exp.Int => {
        val valuePostfix: String = isForcedSign match {
          case T => "S"
          case _ => if(anvil.isSigned(exp.tipe)) "S" else "U"
        }
        exprST = st"${exp.value}${if(exp.value > 2147483647 || exp.value < -2147483648) "L" else ""}.${valuePostfix}"
      }
      case exp: AST.IR.Exp.Type => {
        exprST = st"${processExpr(exp.exp, F)}${if(anvil.isSigned(exp.t)) ".asSInt" else ".asUInt"}"
      }
      case exp: AST.IR.Exp.Binary => {
        val isSIntOperation = isSignedExp(exp.left) || isSignedExp(exp.right)
        val leftST = st"${processExpr(exp.left, F).render}${if(isSIntOperation && (!isSignedExp(exp.left))) ".asSInt" else ""}"
        val rightST = st"${processExpr(exp.right, F).render}${if(isSIntOperation && (!isSignedExp(exp.right))) ".asSInt" else ""}"
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
            exprST = st"(${leftST.render} <= ${rightST.render}).asUInt"
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
