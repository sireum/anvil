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
import org.sireum.alir.TypeSpecializer
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.message.Reporter

object Anvil {

  def synthesize(th: TypeHierarchy, owner: QName, id: String, forwarding: HashMap[QName, QName], reporter: Reporter): Unit = {
    val tsr = TypeSpecializer.specialize(th, ISZ(TypeSpecializer.EntryPoint.Method(owner :+ id)), forwarding, reporter)
    if (reporter.hasError) {
      return
    }
    for (m <- tsr.methods.get(owner).get.elements) {
      val irt = lang.IRTranslator(T, tsr.typeHierarchy)
      var p = irt.translateMethod(None(), m.info.owner, m.info.ast)
      p = lang.IRTranslator.BlockDeclPreamble().transformIRProcedure(p).getOrElse(p)
      p = p(body = irt.toBasic(p.body.asInstanceOf[lang.ast.IR.Body.Block], p.pos))
      println(p)
      println()
    }
  }
}