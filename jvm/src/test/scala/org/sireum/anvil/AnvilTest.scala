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
import org.sireum.anvil.AnvilTest.{defaultSimThreads, maxArrayFileMap, simCyclesMap}
import org.sireum.test._

object AnvilTest {
  @memoize def memoryFileMap(splitTempSizes: B, tempLocal: B): HashMap[String, Z] = {
    return HashMap.empty[String, Z] +
      "add.sc" ~> (if (tempLocal) 128  else 128 + 8 * 4) +
      "assert.sc" ~> (if (tempLocal) 256 + 8 * 8 else 256 + 8 * 14) +
      "bubble.sc" ~> (if (tempLocal) 128 + 8 * 8 else 128 + 8 * 12) +
      "construct.sc" ~> (if (tempLocal) 256 + 8 * 0 else 256 + 8 * 3) +
      "divrem.sc" ~> (if (tempLocal) 128 + 8 * 4 else 128 + 8 * 7) +
      "factorial.sc" ~> (if (tempLocal) 128 + 8 * 2 else 128 + 8 * 6) +
      "global.sc" ~> (if (tempLocal) 64 + 8 * 7 else 128 + 8 * 3) +
      "instanceof.sc" ~> (if (tempLocal) 128 else 128 + 8 * 3) +
      "local-reuse.sc" ~> (if (tempLocal) 128 + 8 * 1 else 128 + 8 * 4) +
      "mult.sc" ~> (if (tempLocal) 128 + 8 * 6 else 128 + 8 * 10) +
      "print.sc" ~> (if (tempLocal) 768 + 8 * 23  else 768 + 8 * 23) +
      "print-no-float.sc" ~> (if (tempLocal) 256 + 8 * 6 else 256 + 8 * 9) +
      "printU64.sc" ~> (if (tempLocal) 128 + 8 * 5 else 128 + 8 * 11) +
      "seq.sc" ~> (if (tempLocal) 128 + 8 * 14 else 256 + 8 * 2) +
      "shiftS64.sc" ~> (if (tempLocal) 128 + 8 * 14 else 256 + 8 * 3) +
      "shiftU64.sc" ~> (if (tempLocal) 128 + 8 * 13 else 256 + 8 * 3) +
      "sum.sc" ~> (
        if (splitTempSizes) if (tempLocal) 128 + 8 * 16 else 256 + 8 * 7
        else if (tempLocal) 128 + 8 * 15 else 256 + 8 * 6)
  }
  val maxArrayFileMap: HashMap[String, Z] = HashMap.empty[String, Z] + "sum.sc" ~> 3
  val printFileMap: HashMap[String, Z] = HashMap.empty[String, Z] +
    "add.sc" ~> 16 +
    "assert.sc" ~> 64 +
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
    "shiftS64.sc" ~> 64 +
    "shiftU64.sc" ~> 64 +
    "sum.sc" ~> 8
  val stackTraceFileSet: HashSet[String] = HashSet.empty[String] + "assert.sc"
  val eraseFileSet: HashSet[String] = HashSet.empty[String] + "sum.sc" + "add.sc"
  val dontTestFileSet: HashSet[String] = HashSet.empty[String]
  val simCyclesMap: HashMap[String, Z] = HashMap.empty[String, Z]

  val defaultMemory: Z = 256
  val defaultPrintSize: Z = 128
  val defaultMaxArraySize: Z = 5
  val defaultSimThreads: Z = 16
}

class AnvilTest extends SireumRcSpec {

  {
    Os.sireumHomeOpt match {
      case Some(sireumHome) => Init(sireumHome, Os.kind, (sireumHome / "versions.properties").properties).installSbt(F)
      case _ => halt("Please set the SIREUM_HOME environment variable")
    }
  }

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
        val splitTempSizes = T
        val tempLocal = T
        config = config(
          memory = AnvilTest.memoryFileMap(T, T).get(file).getOrElse(AnvilTest.defaultMemory),
          printSize = AnvilTest.printFileMap.get(file).getOrElse(AnvilTest.defaultPrintSize),
          stackTrace = AnvilTest.stackTraceFileSet.contains(file),
          erase = AnvilTest.eraseFileSet.contains(file),
          maxArraySize = AnvilTest.maxArrayFileMap.get(file).getOrElse(AnvilTest.defaultMaxArraySize),
          runtimeCheck = T,
          splitTempSizes = splitTempSizes,
          tempLocal = tempLocal,
          genVerilog = F,
          simOpt = simCyclesMap.get(file).map((cycles: Z) => Anvil.Config.Sim(defaultSimThreads, cycles))
        )
        val out = dir /+ ISZ(path.map(String(_)): _*)
        val irOpt = Anvil.synthesize(!AnvilTest.dontTestFileSet.contains(file), lang.IRTranslator.createFresh, th2, ISZ(), config,
          new Anvil.Output {
            def add(isFinal: B, p: => ISZ[String], content: => ST): Unit = {
              val f = out /+ p
              f.up.mkdirAll()
              f.writeOver(content.render)
            }
          override def string: String = "AnvilTest.Output"
        }, reporter)
        reporter.printMessages()
        if (reporter.hasError) {
          return F
        }
        val ir = irOpt.get

        if (config.genVerilog || config.simOpt.nonEmpty) {
          val sireumHome = Os.sireumHomeOpt.get
          val javaBin = Os.javaExe(Some(sireumHome)).up.canon
          val scalaBin = sireumHome / "bin" / "scala" / "bin"
          val sbt = sireumHome / "bin" / "sbt" / "bin" / (if (Os.isWin) "sbt.bat" else "sbt")
          var envVars = ISZ[(String, String)]()
          //envVars = envVars :+ "PATH" ~> s"$javaBin${Os.pathSepChar}$scalaBin${Os.pathSepChar}${sbt.up.canon}${Os.env("PATH").get}"
          //envVars = envVars :+ "JAVA_OPTS" ~> "--enable-native-access=ALL-UNNAMED -Dfile.encoding=UTF-8"
          config.simOpt match {
            case Some(simConfig) =>
              envVars = envVars :+ "VL_THREADS" ~> simConfig.threads.string
            case _ =>
          }
          val chiselDir = out / "chisel"
          // TODO: complete sbt commands
          val axiWrapperVerilogCommandStr: String = s"test:runMain AXIWrapperChiselGenerated${ir.name}VerilogGeneration"
          val verilogCommandStr: String = s"test:runMain ${ir.name}VerilogGeneration"
          val simCommandStr: String = s"test *${ir.name}Bench"
          if(config.genVerilog && config.axi4) {
            Os.proc(ISZ("bash", sbt.string, s"${axiWrapperVerilogCommandStr}")).at(chiselDir).env(envVars).echo.console.runCheck()
          } else if(config.genVerilog) {
            Os.proc(ISZ("bash", sbt.string, s"${verilogCommandStr}")).at(chiselDir).env(envVars).echo.console.runCheck()
          } else {
            config.simOpt match {
              case Some(simConfig) => Os.proc(ISZ("bash", sbt.string, s"${simCommandStr}")).at(chiselDir).env(envVars).echo.console.runCheck()
              case None() => Os.proc(ISZ("bash", sbt.string, s"${verilogCommandStr}")).at(chiselDir).env(envVars).echo.console.runCheck()
            }
          }
        }

        return T
      case _ => return F
    }

  }
}