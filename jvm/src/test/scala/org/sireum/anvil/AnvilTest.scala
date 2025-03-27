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
      "shiftS64.sc" ~> (if (tempLocal) 128 + 8 * 12 else 256 + 8 * 1) +
      "shiftU64.sc" ~> (if (tempLocal) 128 + 8 * 11 else 256 + 8 * 1) +
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
  val simCyclesMap: HashMap[String, Z] = HashMap.empty[String, Z] +
    "add.sc" ~> 700 +
    "bubble.sc" ~> 700 +
    "construct.sc" ~> 350 +
    "divrem.sc" ~> 1500 +
    "factorial.sc" ~> 700 +
    "global.sc" ~> 200 +
    "instanceof.sc" ~> 200 +
    "local-reuse.sc" ~> 400 +
    "mult.sc" ~> 1000 +
    "printU64.sc" ~> 1000 +
    "seq.sc" ~> 500 +
    "sum.sc" ~> 400

  val defaultMemory: Z = 256
  val defaultPrintSize: Z = 128
  val defaultMaxArraySize: Z = 5
  val defaultSimThreads: Z = 16

  val singleTempId = "single-temp"
  val splitTempId = "split-temp"
  val memLocalId = "mem-local"
  val tempLocalId = "temp-local"

  val isInGitHubAction: B = Os.env("GITHUB_ACTIONS").nonEmpty
}

import AnvilTest._

class AnvilTest extends SireumRcSpec {

  val th = lang.FrontEnd.checkedLibraryReporter._1.typeHierarchy
  val dir: Os.Path = Os.path(implicitly[sourcecode.File].value).up.up.up.up.up.up.up / "result"
  val init: Init = {
    val versions: Map[String, String] = Os.sireumHomeOpt match {
      case Some(sireumHome) => (sireumHome / "versions.properties").properties
      case _ => (dir.up.up / "versions.properties").properties
    }
    val d = (dir.up / "result-java").canon
    val vs = versions + "org.sireum.version.java" ~> "17.0.14+10"
    val init = Init(d, Os.kind, vs)
    init.installJava(vs, F, F)
    init.installSbt(F)
    init.installVerilator()
    init
  }

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, _) => !p.last.endsWith("print.sc") }
    implicit val ordering: Ordering[Vector[Predef.String]] = m.ordering
    for ((k, v) <- m; pair <- {
      var r = Vector[(Vector[Predef.String], Predef.String)]()
      r = r :+ (k.dropRight(1) :+ s"${k.last}_(${AnvilTest.singleTempId},_${AnvilTest.memLocalId})", v)
      r = r :+ (k.dropRight(1) :+ s"${k.last}_(${AnvilTest.singleTempId},_${AnvilTest.tempLocalId})", v)
      r = r :+ (k.dropRight(1) :+ s"${k.last}_(${AnvilTest.splitTempId},_${AnvilTest.memLocalId})", v)
      r = r :+ (k.dropRight(1) :+ s"${k.last}_(${AnvilTest.splitTempId},_${AnvilTest.tempLocalId})", v)
      r
    }) yield pair
  }


  override def check(p: Vector[Predef.String], content: Predef.String): Boolean = {
    val path = p.dropRight(1) :+ p.last.substring(0, p.last.lastIndexOf("_("))
    val file = String(path.last)
    val out = dir /+ ISZ(p.map(String(_)): _*)
    val reporter = message.Reporter.create
    lang.parser.Parser.parseTopUnit[lang.ast.TopUnit.Program](content, T, F, Some(path.mkString("/")), reporter) match {
      case Some(program) if !reporter.hasError =>
        val (th2, _) = lang.FrontEnd.checkWorksheet(100, Some(th), program, reporter)
        (dir / path(0)).removeAll()
        var config = Anvil.Config.empty
        val splitTempSizes = p.last.contains(splitTempId)
        val tempLocal = p.last.contains(tempLocalId)
        config = config(
          memory = memoryFileMap(T, F).get(file).getOrElse(defaultMemory),
          printSize = printFileMap.get(file).getOrElse(defaultPrintSize),
          stackTrace = stackTraceFileSet.contains(file),
          erase = eraseFileSet.contains(file),
          maxArraySize = maxArrayFileMap.get(file).getOrElse(defaultMaxArraySize),
          runtimeCheck = T,
          splitTempSizes = splitTempSizes,
          tempLocal = tempLocal,
          genVerilog = T,
          axi4 = T,
          simOpt = simCyclesMap.get(file).map((cycles: Z) => Anvil.Config.Sim(defaultSimThreads, cycles))
        )

        if (isInGitHubAction && (splitTempSizes || !tempLocal)) {
          config = config(simOpt = None())
        }

        val irOpt = Anvil.synthesize(!dontTestFileSet.contains(file), lang.IRTranslator.createFresh, th2, ISZ(), config,
          AnvilOutput(init.versions.get("org.sireum.version.sbt").get, out), reporter)
        reporter.printMessages()
        if (reporter.hasError) {
          return F
        }
        val ir = irOpt.get

        if (!(config.genVerilog || config.axi4 || config.simOpt.nonEmpty)) {
          return T
        }

        val sbt = init.homeBin / "sbt" / "bin" / (if (Os.isWin) "sbt.bat" else "sbt")
        var envVars = ISZ[(String, String)]()
        val javaBin = Os.javaExe(Some(init.home)).up.canon
        val verilatorBin = init.homeBin / "verilator" / "bin"
        envVars = envVars :+ "PATH" ~> s"$javaBin${Os.pathSepChar}${sbt.up.canon}${Os.pathSepChar}$verilatorBin${Os.pathSepChar}${Os.env("PATH").get}"
        envVars = envVars :+ "JAVA_HOME" ~> javaBin.up.canon.string
        config.simOpt match {
          case Some(simConfig) =>
            envVars = envVars :+ "VL_THREADS" ~> simConfig.threads.string
            envVars = envVars :+ "VERILATOR_ROOT" ~> verilatorBin.up.canon.string
          case _ =>
        }
        val chiselDir = out / "chisel"
        val axiWrapperVerilogCommandStr: String = s"Test/runMain AXIWrapperChiselGenerated${ir.name}VerilogGeneration"
        val verilogCommandStr: String = s"Test/runMain ${ir.name}VerilogGeneration"
        val simCommandStr: String = s"Test/testOnly *${ir.name}Bench"
        val sbtOpts = ISZ[String]("-J-Xss32m")
        if (config.genVerilog) {
          Os.proc(ISZ[String]("bash", sbt.string) ++ sbtOpts :+ s"$verilogCommandStr").
            at(chiselDir).env(envVars).echo.console.runCheck()
        }
        if (config.axi4) {
          Os.proc(ISZ[String]("bash", sbt.string) ++ sbtOpts :+ s"$axiWrapperVerilogCommandStr").
            at(chiselDir).env(envVars).echo.console.runCheck()
        }
        config.simOpt match {
          case Some(_) if verilatorBin.exists =>
            Os.proc(ISZ[String]("bash", sbt.string) ++ sbtOpts :+ s"$simCommandStr").
              at(chiselDir).env(envVars).echo.console.runCheck()
          case _ =>
        }
        return T
      case _ => return F
    }

  }
}