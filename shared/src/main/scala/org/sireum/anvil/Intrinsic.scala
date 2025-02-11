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
  @datatype class LocalOffset(val isVal: B,
                              val offset: Z,
                              val context: AST.IR.MethodContext,
                              val id: org.sireum.String,
                              val tipe: AST.Typed,
                              val pos: Position) extends AST.IR.Exp.Intrinsic.Type {
    @strictpure def prettyST: ST = st"$id@$offset"
    @strictpure def numOfTemps: Z = 0
  }

  @datatype class LocalOffsetAssign(val copy: B,
                                    val offset: Z,
                                    val context: AST.IR.MethodContext,
                                    val lhs: String,
                                    val rhs: AST.IR.Exp,
                                    val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST: ST = st"$lhs@$offset ${if (copy) ":=" else "="} ${rhs.prettyST}"
    @strictpure def computeLocalsTemps(locals: Z, temps: Z): (Z, Z) = (locals, temps - rhs.numOfTemps)
  }

  @datatype class StackPointer(val add: Z, val pos: Position) extends AST.IR.Stmt.Intrinsic.Type {
    @strictpure def prettyST: ST = st"SP($add)"
    @strictpure def computeLocalsTemps(locals: Z, temps: Z): (Z, Z) = (locals, temps)
  }

  @datatype class GotoLocal(val offset: Z,
                            val context: AST.IR.MethodContext,
                            val id: String,
                            val pos: Position) extends AST.IR.Jump.Intrinsic.Type {
    @strictpure def prettyST: ST = st"goto $id"
    @strictpure def computeLocalsTemps(locals: Z, temps: Z): (Z, Z) = (locals, temps)
    @strictpure def targets: ISZ[Z] = ISZ()
  }
}
