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
import org.sireum.lang.{ast => AST}
import org.sireum.message.Position

object Intrinsic {

  // Replaces AST.IR.Exp.LocalVarRef, AST.IR.Exp.GlobalVarRef, AST.IR.Exp.Field, AST.IR.Exp.Index
  @datatype class TempLoad(val temp: Z,
                           val rhsOffset: AST.IR.Exp,
                           val isSigned: B,
                           val bytes: Z,
                           val comment: ST,
                           val tipe: AST.Typed,
                           val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = {
      val lhs: ST =
        if (p.asInstanceOf[Util.AnvilIRPrinter].anvil.config.splitTempSizes)
          st"${p.exp(AST.IR.Exp.Temp(temp, tipe, pos))}"
        else st"$$$temp"
      st"$lhs = *${rhsOffset.prettyST(p)} [${if (isSigned) "signed" else "unsigned"}, $tipe, $bytes]  // $comment"
    }
  }

  // Replaces AST.IR.Exp.LocalVarRef, AST.IR.Exp.GlobalVarRef, AST.IR.Exp.Field, AST.IR.Exp.Index
  @datatype class Load(val rhsOffset: AST.IR.Exp,
                       val isSigned: B,
                       val bytes: Z,
                       val comment: ST,
                       val tipe: AST.Typed,
                       val pos: Position) extends AST.IR.Exp.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = st"*${rhsOffset.prettyST(p)}"
    @strictpure def numOfTemps: Z = rhsOffset.numOfTemps
    @strictpure def depth: Z = 1 + rhsOffset.depth
  }

  @datatype class Indexing(val baseOffset: AST.IR.Exp,
                           val dataOffset: Z,
                           val index: AST.IR.Exp,
                           val maskOpt: Option[Z],
                           val elementSize: Z,
                           val tipe: AST.Typed,
                           val pos: Position) extends AST.IR.Exp.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = st"${baseOffset.prettyST(p)}[+$dataOffset](${index.prettyST(p)}[*$elementSize])"
    @strictpure def numOfTemps: Z = baseOffset.numOfTemps + index.numOfTemps
    @strictpure def depth: Z = {
      val bd = baseOffset.depth
      val index = baseOffset.depth
      1 + (if (bd < index) index else bd)
    }
  }

  // Replaces AST.IR.Stmt.Assign.Local, AST.IR.Stmt.Assign.Field, AST.IR.Stmt.Assign.Global, AST.IR.Stmt.Assign.Index
  @datatype class Store(val lhsOffset: AST.IR.Exp,
                        val isSigned: B,
                        val bytes: Z,
                        val rhs: AST.IR.Exp,
                        val comment: ST,
                        val tipe: AST.Typed,
                        val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = {
      val rhsST = st"${rhs.prettyST(p)} [${if (isSigned) "signed" else "unsigned"}, $tipe, $bytes]  // $comment"
      lhsOffset match {
        case AST.IR.Exp.Intrinsic(in: Indexing) => st"${lhsOffset.prettyST(p)} = $rhsST"
        case _ => st"*${lhsOffset.prettyST(p)} = $rhsST"
      }
    }
  }

  // Replaces AST.IR.Stmt.Assign.Local, AST.IR.Stmt.Assign.Field, AST.IR.Stmt.Assign.Global, AST.IR.Stmt.Assign.Index
  @datatype class Copy(val lhsOffset: AST.IR.Exp,
                       val lhsBytes: Z,
                       val rhsBytes: AST.IR.Exp,
                       val rhs: AST.IR.Exp,
                       val comment: ST,
                       val tipe: AST.Typed,
                       val rhsTipe: AST.Typed,
                       val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = st"${lhsOffset.prettyST(p)} [$tipe, $lhsBytes]  <-  ${rhs.prettyST(p)} [$rhsTipe, ${rhsBytes.prettyST(p)}]  // $comment"
  }

  // Replaces AST.IR.Stmt.Decl
  @datatype class Decl(val undecl: B, val isAlloc: B, val slots: ISZ[Decl.Local], val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = st"${if (isAlloc) if (undecl) "unalloc" else "alloc" else if (undecl) "undecl" else "decl"} ${(for (slot <- slots) yield slot.prettyST, ", ")}"
  }

  object Decl {
    @datatype class Local(val loc: Z, val size: Z, val id: String, val tipe: AST.Typed) {
      @strictpure def prettyST: ST =
        if (size == 0) st"$id: $tipe @$$$loc"
        else st"$id: $tipe [@$loc, $size]"
    }
  }

  @datatype class Register(val isSP: B, val tipe: AST.Typed, val pos: Position) extends AST.IR.Exp.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = if (isSP) st"SP" else st"DP"
    @strictpure def numOfTemps: Z = 0
    @strictpure def depth: Z = 1
  }

  @datatype class RegisterAssign(val isSP: B, val isInc: B, val value: AST.IR.Exp, val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = {
      val reg: String = if (isSP) "SP" else "DP"
      value match {
        case AST.IR.Exp.Int(_, v, _) => if (isInc) if (v < 0) st"$reg = $reg - ${-v}" else st"$reg = $reg + $v" else st"$reg = $v"
        case _ => if (isInc) st"$reg = $reg + ${value.prettyST(p)}" else st"$reg = ${value.prettyST(p)}"
      }
    }
  }

  // Replaces AST.IR.Jump.Return
  @datatype class GotoLocal(val isTemp: B,
                            val loc: Z,
                            val contextOpt: Option[AST.IR.MethodContext],
                            val id: String,
                            val pos: Position) extends AST.IR.Jump.Intrinsic.Type {
    @strictpure def prettyST(p: AST.IR.Printer): ST = {
      val anvil = p.asInstanceOf[Util.AnvilIRPrinter].anvil
      if (isTemp) st"goto $id@${p.exp(AST.IR.Exp.Temp(loc, anvil.cpType, pos)).getOrElse(st"$$$loc")}"
      else st"goto $id@$loc"
    }

    @strictpure def targets: ISZ[Z] = ISZ()
  }
}
