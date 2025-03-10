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
import org.sireum.test._
import org.sireum.U8._

class IRSimulatorTest extends SireumRcSpec {

  val th = lang.FrontEnd.checkedLibraryReporter._1.typeHierarchy
  val dir: Os.Path = Os.path(implicitly[sourcecode.File].value).up.up.up.up.up.up.up / "result-sim"

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, _) => p.last.endsWith("-test.sc") }
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
        var config = Anvil.Config.empty(path.mkString("/"))
        val file = path(path.size - 1)
//        config = config(
//          printSize = 4096,
//          stackTrace = T,
//          erase = T,
//          runtimeCheck = T)
        config = config(
          memory = AnvilTest.memoryFileMap.get(file).getOrElse(1024),
          printSize = if (AnvilTest.printFileSet.contains(file)) 128 else 0,
          stackTrace = AnvilTest.stackTraceFileSet.contains(file),
          erase = AnvilTest.eraseFileSet.contains(file),
          runtimeCheck = T)
        val out = dir /+ ISZ(path.map(String(_)): _*)
        Anvil.generateIR(T, lang.IRTranslator.createFresh, th2, ISZ(), config, new Anvil.Output {
          def add(isFinal: B, p: => ISZ[String], content: => ST): Unit = {
            val f = out /+ p
            f.up.mkdirAll()
            f.writeOver(content.render)
          }
          override def string: String = "AnvilTest.Output"
        }, reporter) match {
          case Some(ir) =>
            val state = IRSimulator.State.create(ir.anvil.config.memory, ir.maxRegisters)
            val testNumInfoOffset = ir.globalInfoMap.get(Util.testNumName).get.offset
            for (i <- 0 until ir.anvil.typeByteSize(AST.Typed.z)) {
                state.memory(testNumInfoOffset + i) = u8"0xFF"
            }
            IRSimulator(ir.anvil).evalProcedure(state, ir.procedure)
            val displaySize = ir.anvil.config.printSize
            val offset = ir.globalInfoMap.get(Util.displayName).get.offset + ir.anvil.spTypeByteSize +
              ir.anvil.typeShaSize + ir.anvil.typeByteSize(AST.Typed.z)
            val dp = state.DP.toZ
            val (lo, hi): (Z, Z) = if (dp < displaySize) (0, dp) else (dp, displaySize + dp - 1)
            val u8ms = MSZ.create(hi - lo, u8"0")
            var j: Z = 0
            for (i <- lo until hi) {
              u8ms(j) = state.memory((offset + i) % displaySize)
              j = j + 1
            }
            val display = conversions.String.fromU8ms(u8ms)
            print(display)
          case _ =>
        }
        reporter.printMessages()
        T
      case _ => return F
    }

  }
}