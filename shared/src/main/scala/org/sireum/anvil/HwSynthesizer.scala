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
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.TypeHierarchy

object HwSynthesizer {
  /*
    Notes/links:
    * Slang IR: https://github.com/sireum/slang/blob/master/ast/shared/src/main/scala/org/sireum/lang/ast/IR.scala
      * Slang Typed data structure: https://github.com/sireum/slang/blob/master/ast/shared/src/main/scala/org/sireum/lang/ast/Typed.scala
    * Slang TypeHierarchy: https://github.com/sireum/slang/blob/88c6873c8cb5d5a33686772f0607eac88fee9c9b/tipe/shared/src/main/scala/org/sireum/lang/tipe/TypeHierarchy.scala#L563
      * contains typeMap that maps a type fully qualified name to TypeInfo
      * TypeInfo: https://github.com/sireum/slang/blob/88c6873c8cb5d5a33686772f0607eac88fee9c9b/tipe/shared/src/main/scala/org/sireum/lang/symbol/Info.scala#L851
      * examples of Typed/TypeHierarchy API usage: https://github.com/sireum/slang/blob/88c6873c8cb5d5a33686772f0607eac88fee9c9b/frontend/shared/src/main/scala/org/sireum/lang/IRTranslator.scala#L419-L456
   */
  def printProgram(th: TypeHierarchy, config: Anvil.Config, o: lang.ast.IR.Program, owner: QName, id: String): HashSMap[ISZ[String], ST] = {
    var r = HashSMap.empty[ISZ[String], ST]
    r = r + ISZ("program.scala") ~> o.prettyST
    return r
  }
}