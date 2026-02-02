// #Sireum
/*
 Copyright (c) 2017-2026,Robby, Kansas State University
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

@datatype class AnvilOutput(val finalOnly: B, val sbtVersion: String, val out: Os.Path) extends Anvil.Output {
  def addH(isFinal: B, path: => ISZ[String], content: => ST, maskOpt: Option[String]): Unit = {
    if (isFinal || !finalOnly) {
      val f = out /+ path
      f.up.mkdirAll()
      f.writeOver(content.render)
      maskOpt match {
        case Some(perm) => f.chmod(perm)
        case _ =>
      }
      if (isFinal) {
        println(s"Wrote $f")
      }
    }
  }

  override def add(isFinal: B, path: => ISZ[String], content: => ST): Unit = {
    addH(isFinal, path, content, None())
  }

  override def addPerm(isFinal: B, path: => ISZ[String], content: => ST, mask: String): Unit = {
    addH(isFinal, path, content, Some(mask))
  }
}

