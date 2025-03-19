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
import org.sireum.anvil.AnvilTest.maxArrayFileMap
import org.sireum.test._

object AnvilTest {
  val memoryFileMap: HashMap[String, Z] = HashMap.empty[String, Z] +
    "add.sc" ~> (128 + 8 * 4) +
    "assert.sc" ~> (512 + 8 * 15) +
    "bubble.sc" ~> (128 + 8 * 11) +
    "construct.sc" ~> (256 + 8 * 3) +
    "divrem.sc" ~> (128 + 8 * 7) +
    "factorial.sc" ~> (128 + 8 * 6) +
    "global.sc" ~> (128 + 8 * 3) +
    "instanceof.sc" ~> (128 + 8 * 2) +
    "local-reuse.sc" ~> (128 + 8 * 4) +
    "mult.sc" ~> (128 + 8 * 10) +
    "print.sc" ~> (768 + 8 * 24) +
    "print-no-float.sc" ~> (256 + 8 * 11) +
    "printU64.sc" ~> (128 + 8 * 11) +
    "seq.sc" ~> (256 + 8 * 2) +
    "shift.sc" ~> (256 + 8 * 11) +
    "sum.sc" ~> (256 + 8 * 6)
  val maxArrayFileMap: HashMap[String, Z] = HashMap.empty[String, Z] + "sum.sc" ~> 3
  val printFileMap: HashMap[String, Z] = HashMap.empty[String, Z] +
    "add.sc" ~> 16 +
    "assert.sc" ~> 128 +
    "bubble.sc" ~> 16 +
    "construct.sc" ~> 16 +
    "divrem.sc" ~> 32 +
    "factorial.sc" ~> 32 +
    "global.sc" ~> 2 +
    "instanceof.sc" ~> 2 +
    "local-reuse.sc" ~> 8 +
    "mult.sc" ~> 64 +
    "print.sc" ~> 64 +
    "print-no-float.sc" ~> 64 +
    "printU64.sc" ~> 64 +
    "seq.sc" ~> 32 +
    "shift.sc" ~> 128 +
    "sum.sc" ~> 8
  val stackTraceFileSet: HashSet[String] = HashSet.empty[String] + "assert.sc"
  val eraseFileSet: HashSet[String] = HashSet.empty[String] + "sum.sc" + "add.sc"
  val dontTestFileSet: HashSet[String] = HashSet.empty[String]
  val defaultMemory: Z = 256
  val defaultPrintSize: Z = 128
  val defaultMaxArraySize: Z = 5
}

class AnvilTest extends SireumRcSpec {

  val th = lang.FrontEnd.checkedLibraryReporter._1.typeHierarchy
  val dir: Os.Path = Os.path(implicitly[sourcecode.File].value).up.up.up.up.up.up.up / "result"

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, _) => !p.last.endsWith("print.sc") }
    m
  }

  override def check(path: Vector[Predef.String], content: Predef.String): Boolean = {
    val reporter = message.Reporter.create
    lang.parser.Parser.parseTopUnit[lang.ast.TopUnit.Program](content, T, F, Some(path.mkString("/")), reporter) match {
      case Some(p) if !reporter.hasError =>
        val (th2, _) = lang.FrontEnd.checkWorksheet(100, Some(th), p, reporter)
        (dir / path(0)).removeAll()
        var config = Anvil.Config.empty
        val file = path(path.size - 1)
        config = config(
          memory = AnvilTest.memoryFileMap.get(file).getOrElse(AnvilTest.defaultMemory),
          printSize = AnvilTest.printFileMap.get(file).getOrElse(AnvilTest.defaultPrintSize),
          stackTrace = AnvilTest.stackTraceFileSet.contains(file),
          erase = AnvilTest.eraseFileSet.contains(file),
          maxArraySize = AnvilTest.maxArrayFileMap.get(file).getOrElse(AnvilTest.defaultMaxArraySize),
          runtimeCheck = T)
        val out = dir /+ ISZ(path.map(String(_)): _*)
        Anvil.synthesize(!AnvilTest.dontTestFileSet.contains(file), lang.IRTranslator.createFresh, th2, ISZ(), config,
          new Anvil.Output {
            def add(isFinal: B, p: => ISZ[String], content: => ST): Unit = {
              val f = out /+ p
              f.up.mkdirAll()
              f.writeOver(content.render)
            }
          override def string: String = "AnvilTest.Output"
        }, reporter)
        reporter.printMessages()
        T
      case _ => return F
    }

  }
}