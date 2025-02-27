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
    @strictpure def prettyST: ST = st"$$$temp = *${rhsOffset.prettyST} [${if (isSigned) "signed" else "unsigned"}, $tipe, $bytes]  // $comment"
  }

  // Replaces AST.IR.Exp.LocalVarRef, AST.IR.Exp.GlobalVarRef, AST.IR.Exp.Field, AST.IR.Exp.Index
  @datatype class Load(val rhsOffset: AST.IR.Exp,
                       val isSigned: B,
                       val bytes: Z,
                       val comment: ST,
                       val tipe: AST.Typed,
                       val pos: Position) extends AST.IR.Exp.Intrinsic.Type {
    @strictpure def prettyST: ST = st"*${rhsOffset.prettyST}"
    @strictpure def numOfTemps: Z = rhsOffset.numOfTemps
    @strictpure def depth: Z = 1 + rhsOffset.depth
  }

  // Replaces AST.IR.Stmt.Assign.Local, AST.IR.Stmt.Assign.Field, AST.IR.Stmt.Assign.Global, AST.IR.Stmt.Assign.Index
  @datatype class Store(val lhsOffset: AST.IR.Exp,
                        val isSigned: B,
                        val bytes: Z,
                        val rhs: AST.IR.Exp,
                        val comment: ST,
                        val tipe: AST.Typed,
                        val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST: ST = st"*${lhsOffset.prettyST} = ${rhs.prettyST} [${if (isSigned) "signed" else "unsigned"}, $tipe, $bytes]  // $comment"
  }

  // Replaces AST.IR.Stmt.Assign.Local, AST.IR.Stmt.Assign.Field, AST.IR.Stmt.Assign.Global, AST.IR.Stmt.Assign.Index
  @datatype class Copy(val lhsOffset: AST.IR.Exp,
                       val lhsBytes: Z,
                       val rhsBytes: Z,
                       val rhs: AST.IR.Exp,
                       val comment: ST,
                       val tipe: AST.Typed,
                       val rhsTipe: AST.Typed,
                       val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST: ST = st"${lhsOffset.prettyST} [$tipe, $lhsBytes]  <-  ${rhs.prettyST} [$rhsTipe, $rhsBytes]  // $comment"
  }

  // Replaces AST.IR.Stmt.Decl
  @datatype class Decl(val undecl: B, val isAlloc: B, val slots: ISZ[Decl.Local], val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST: ST = st"${if (isAlloc) if (undecl) "unalloc" else "alloc" else if (undecl) "undecl" else "decl"} ${(for (slot <- slots) yield slot.prettyST, ", ")}"
  }

  object Decl {
    @datatype class Local(val offset: Z, val size: Z, val id: String, val tipe: AST.Typed) {
      @strictpure def prettyST: ST = st"$id: $tipe [@$offset, $size]"
    }
  }

  @datatype class SP(val tipe: AST.Typed, val pos: Position) extends AST.IR.Exp.Intrinsic.Type {
    @strictpure def prettyST: ST = st"SP"
    @strictpure def numOfTemps: Z = 0
    @strictpure def depth: Z = 1
  }

  @datatype class SPAssign(val isInc: B, val value: Z, val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST: ST = {
      val reg = "SP"
      if (isInc) if (value < 0) st"$reg = $reg - ${-value}" else st"$reg = $reg + $value" else st"$reg = $value"
    }
  }

  // Replaces AST.IR.Jump.Return
  @datatype class GotoLocal(val offset: Z,
                            val context: AST.IR.MethodContext,
                            val id: String,
                            val pos: Position) extends AST.IR.Jump.Intrinsic.Type {
    @strictpure def prettyST: ST = st"goto $id@0"

    @strictpure def targets: ISZ[Z] = ISZ()
  }
}
