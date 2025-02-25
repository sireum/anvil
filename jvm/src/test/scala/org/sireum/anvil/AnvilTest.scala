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
import org.sireum.test._

class AnvilTest extends SireumRcSpec {

  val th = lang.FrontEnd.checkedLibraryReporter._1.typeHierarchy
  val dir: Os.Path = Os.path(implicitly[sourcecode.File].value).up.up.up.up.up.up.up / "result"

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, _) => p.last.endsWith(".sc") }
    m
  }

  override def check(path: Vector[Predef.String], content: Predef.String): Boolean = {
    val reporter = message.Reporter.create
    lang.parser.Parser.parseTopUnit[lang.ast.TopUnit.Program](content, T, F, Some(path.mkString("/")), reporter) match {
      case Some(p) if !reporter.hasError =>
        val (th2, p2) = lang.FrontEnd.checkWorksheet(100, Some(th), p, reporter)
        var lastMethod: String = ""
        for (stmt <- p2.body.stmts) {
          stmt match {
            case stmt: lang.ast.Stmt.Method => lastMethod = stmt.sig.id.value
            case _ =>
          }
        }
        (dir / path(0)).removeAll()
        for (p <- Anvil.synthesize(lang.IRTranslator.createFresh, th2, ISZ(), lastMethod, Anvil.Config.empty(path.mkString("/")), reporter).entries) {
          val f = dir /+ ISZ(path.map(String(_)): _*) /+ p._1
          f.up.mkdirAll()
          f.writeOver(p._2.render)
        }
        T
      case _ => return F
    }

  }
}