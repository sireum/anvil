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
  @memoize def memoryFileMap(isFirstGen: B, printSize: Z, splitTempSizes: B, tempGlobal: B, tempLocal: B, useIP: B, useMemoryIP: B, alignAxi4: B): HashMap[String, Z] = {
    if (isFirstGen) {
      if (tempGlobal) {
        return HashMap.empty[String, Z] +
          "add.sc" ~> (if (alignAxi4) 136 else 112) +
          "assert.sc" ~> (if (alignAxi4) 336 else 280) +
          "bubble.sc" ~> (if (alignAxi4) 208 else 176) +
          "construct.sc" ~> (if (alignAxi4) 280 else if (useIP) if (useMemoryIP) 248 else 232 else 232) +
          "divrem.sc" ~> (if (alignAxi4) 152 else 128) +
          "dll.sc" ~> (if (alignAxi4) 944 else if (printSize > 0) if (tempLocal) 832 else 844 else 832) +
          "factorial.sc" ~> (if (alignAxi4) 152 else 128) +
          "global.sc" ~> (if (alignAxi4) 120 else 96) +
          "indexing-obj.sc" ~> (if (alignAxi4) 232 else if (useIP) if (useMemoryIP) 184 else 176 else 176) +
          "indexing.sc" ~> (if (alignAxi4) 168 else 136) +
          "instanceof.sc" ~> (if (alignAxi4) 136 else if (useIP) if (useMemoryIP) 112 else 104 else 104) +
          "local-reuse.sc" ~> (if (alignAxi4) 144 else 112) +
          "mult.sc" ~> (if (alignAxi4) 184 else 160) +
          "print.sc" ~> (if (alignAxi4) 952 else 928) +
          "print-no-float.sc" ~> (if (alignAxi4) 352 else if (useIP) if (useMemoryIP) 336 else 296 else 296) +
          "printU64.sc" ~> (if (alignAxi4) 192 else 160) +
          "seq.sc" ~> (if (alignAxi4) 272 else 240) +
          "shiftS64.sc" ~> (if (alignAxi4) 208 else 176) +
          "shiftU64.sc" ~> (if (alignAxi4) 200 else 168) +
          "sum.sc" ~> (if (alignAxi4) 200 else 152)
      } else {
        return HashMap.empty[String, Z] +
          "add.sc" ~> (if (tempLocal) 112 else 160) +
          "assert.sc" ~> (if (tempLocal) 280 else if (useIP) if (useMemoryIP) 376 else 368 else 368) +
          "bubble.sc" ~> (if (tempLocal) 176 else if (useIP) if (useMemoryIP) 232 else 224 else 224) +
          "construct.sc" ~> (if (tempLocal) if (useIP) if (useMemoryIP) 248 else 232 else 232 else if (useMemoryIP) 296 else 256 + 8 * 3) +
          "divrem.sc" ~> (if (tempLocal) 128 else if (useIP) 184 else 184) +
          "dll.sc" ~> (if (printSize > 0) if (tempLocal) 840 else 848 else 832) +
          "factorial.sc" ~> (if (tempLocal) 128 else if (useIP) 176 else 176) +
          "global.sc" ~> (if (tempLocal) 104 else 152) +
          "indexing-obj.sc" ~> (if (tempLocal) if (useIP) if (useMemoryIP) 184 else 176 else 176 else 208) +
          "indexing.sc" ~> (if (tempLocal) 136 else if (useIP) 176 else 176) +
          "instanceof.sc" ~> (if (tempLocal) if (useIP) if (useMemoryIP) 112 else 104 else 104 else if (splitTempSizes) 152 else 144) +
          "local-reuse.sc" ~> (if (tempLocal) 112 else 160) +
          "mult.sc" ~> (if (tempLocal) 160 else if (useIP) if (useMemoryIP) 216 else 208 else 208) +
          "print.sc" ~> (if (tempLocal) 928 else 960) +
          "print-no-float.sc" ~> (if (tempLocal) if (useIP) if (useMemoryIP) 336 else 296 else 296 else if (useMemoryIP) 368 else 336) +
          "printU64.sc" ~> (if (tempLocal) 160 else if (useIP) 216 else 216) +
          "seq.sc" ~> (if (tempLocal) 240 else if (useIP) if (useMemoryIP) 280 else 272 else 272) +
          "shiftS64.sc" ~> (if (tempLocal) 176 else 264) +
          "shiftU64.sc" ~> (if (tempLocal) 168 else if (useIP) 264 else 264) +
          "sum.sc" ~> (if (tempLocal) 152 else if (splitTempSizes) 312 else 304)
      }
    } else {
      if (tempGlobal) {
        if (alignAxi4) {
          return HashMap.empty[String, Z] +
            "add.sc" ~> 120 +
            "assert.sc" ~> 960 +
            "bubble.sc" ~> 248 +
            "construct.sc" ~> 216 +
            "divrem.sc" ~> 72 +
            "dll.sc" ~> 1088 +
            "factorial.sc" ~> 136 +
            "global.sc" ~> 112 +
            "indexing-obj.sc" ~> 560 +
            "indexing.sc" ~> 208 +
            "instanceof.sc" ~> 144 +
            "local-reuse.sc" ~> 120 +
            "mult.sc" ~> 168 +
            "print.sc" ~> 1648 +
            "print-no-float.sc" ~> 592 +
            "printU64.sc" ~> 168 +
            "seq.sc" ~> 208 +
            "shiftS64.sc" ~> 176 +
            "shiftU64.sc" ~> 168 +
            "sum.sc" ~> 520
        } else {
          return HashMap.empty[String, Z] +
            "add.sc" ~> 104 +
            "assert.sc" ~> 240 +
            "bubble.sc" ~> 200 +
            "construct.sc" ~> 200 +
            "divrem.sc" ~> 128 +
            "dll.sc" ~> 664 +
            "factorial.sc" ~> 120 +
            "global.sc" ~> 104 +
            "indexing-obj.sc" ~> 184 +
            "indexing.sc" ~> 136 +
            "instanceof.sc" ~> 112 +
            "local-reuse.sc" ~> 104 +
            "mult.sc" ~> 152 +
            "print.sc" ~> 888 +
            "print-no-float.sc" ~> 336 +
            "printU64.sc" ~> 152 +
            "seq.sc" ~> 240 +
            "shiftS64.sc" ~> 160 +
            "shiftU64.sc" ~> 152 +
            "sum.sc" ~> 216 +
            "1.example.sc" ~> 216 +
            "2.example.sc" ~> 216 +
            "3.example.sc" ~> 216 +
            "4.example.sc" ~> 216 +
            "5.example.sc" ~> 216 +
            "6.example.sc" ~> 216
        }
      } else {
        return HashMap.empty[String, Z] +
          "add.sc" ~> 160 +
          "assert.sc" ~> 416 +
          "bubble.sc" ~> 344 +
          "construct.sc" ~> 352 +
          "divrem.sc" ~> 248 +
          "dll.sc" ~> 760 +
          "factorial.sc" ~> 176 +
          "global.sc" ~> 152 +
          "indexing-obj.sc" ~> 240 +
          "indexing.sc" ~> 208 +
          "instanceof.sc" ~> 160 +
          "local-reuse.sc" ~> 144 +
          "mult.sc" ~> 224 +
          "print.sc" ~> 1096 +
          "print-no-float.sc" ~> 456 +
          "printU64.sc" ~> 208 +
          "seq.sc" ~> 288 +
          "shiftS64.sc" ~> 224 +
          "shiftU64.sc" ~> 224 +
          "sum.sc" ~> 280 +
          "1.example.sc" ~> 280 +
          "2.example.sc" ~> 280 +
          "3.example.sc" ~> 280 +
          "4.example.sc" ~> 280 +
          "5.example.sc" ~> 280 +
          "6.example.sc" ~> 280
      }
    }
  }
  val maxArrayFileMap: HashMap[String, Z] = HashMap.empty[String, Z] +
    "dll" ~> 3 +
    "indexing-obj.sc" ~> 1 +
    "sum.sc" ~> 3
  val printFileMap: HashMap[String, Z] = HashMap.empty[String, Z] +
    "add.sc" ~> 16 +
    "assert.sc" ~> 64 +
    "bubble.sc" ~> 16 +
    "construct.sc" ~> 16 +
    "divrem.sc" ~> 32 +
    "dll.sc" ~> 2 +
    "factorial.sc" ~> 32 +
    "global.sc" ~> 2 +
    "indexing.sc" ~> 8 +
    "indexing-obj.sc" ~> 2 +
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
  val noRuntimeCheckFileSet: HashSet[String] = HashSet.empty[String] + "indexing.sc"
  val simCyclesMap: HashMap[String, Z] = HashMap.empty[String, Z] +
    "add.sc" ~> 1300 +
    "bubble.sc" ~> 2200 +
    "construct.sc" ~> 1200 +
    "divrem.sc" ~> 1500 +
    "factorial.sc" ~> 2100 +
    "global.sc" ~> 400 +
    "indexing.sc" ~> 600 +
    "indexing-obj.sc" ~> 800 +
    "instanceof.sc" ~> 500 +
    "local-reuse.sc" ~> 1100 +
    "mult.sc" ~> 2950 +
    "print-no-float.sc" ~> 1100 +
    "printU64.sc" ~> 2900 +
    "seq.sc" ~> 1500 +
    "shiftS64.sc" ~> 3700 +
    "shiftU64.sc" ~> 4000 +
    "sum.sc" ~> 1900

  val defaultMemory: Z = 256
  val defaultPrintSize: Z = 128
  val defaultMaxArraySize: Z = 5
  val defaultSimThreads: Z = 16

  val singleTempId = "single-temp"
  val splitTempId = "split-temp"
  val memLocalId = "mem-local"
  val tempGlobalId = "temp-global"
  val tempLocalId = "temp-local"
  val withIpId = "with-ip"
  val withoutIpId = "without-ip"
  val withMemIpId = "with-mem-ip"
  val alignId = "align"

  val isInGitHubAction: B = Os.env("GITHUB_ACTIONS").nonEmpty

  def getConfig(isFirstGen: B, file: String, p: Vector[Predef.String]): Anvil.Config = {
    var config = Anvil.Config.empty
    val splitTempSizes = p.last.contains(splitTempId)
    val tempGlobal = p.last.contains(tempGlobalId)
    val tempLocal = p.last.contains(tempLocalId)
    val useMemoryIp = p.last.contains(withMemIpId)
    val alignAxi4 = p.last.contains(alignId)
    val ipMax: Z = if (useMemoryIp || p.last.contains(withIpId)) 0 else -1
    val printSize: Z = printFileMap.get(file).getOrElse(defaultPrintSize)
    config = config(
      isFirstGen = isFirstGen,
      memory = memoryFileMap(isFirstGen, printSize, splitTempSizes, tempGlobal, tempLocal, ipMax >= 0, useMemoryIp, alignAxi4).get(file).
        getOrElse(defaultMemory),
      printSize = printSize,
      stackTrace = stackTraceFileSet.contains(file),
      erase = eraseFileSet.contains(file),
      maxArraySize = maxArrayFileMap.get(file).getOrElse(defaultMaxArraySize),
      runtimeCheck = !noRuntimeCheckFileSet.contains(file),
      splitTempSizes = splitTempSizes,
      tempGlobal = tempGlobal,
      tempLocal = tempLocal,
      genVerilog = T,
      ipMax = ipMax,
      noXilinxIp = F,
      alignAxi4 = alignAxi4,
      simOpt = simCyclesMap.get(file).map((cycles: Z) => Anvil.Config.Sim(defaultSimThreads, cycles)),
      memoryAccess = if (useMemoryIp) Anvil.Config.MemoryAccess.BramNative else Anvil.Config.MemoryAccess.Default
    )
    return config
  }
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
    init.installSbt(T)
    init.installVerilator(T)
    init
  }

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, _) => !p.last.endsWith("print.sc") }
    implicit val ordering: Ordering[Vector[Predef.String]] = m.ordering
    for ((k, v) <- m; pair <- {
      var r = Vector[(Vector[Predef.String], Predef.String)]()
      def combs(i: Int, acc: Vector[Vector[Boolean]]): Vector[Vector[Boolean]] = {
        if (i <= 0) {
          return acc
        }
        var r = Vector[Vector[Boolean]]()
        for (bs <- acc) {
          r = r :+ (bs :+ false)
          r = r :+ (bs :+ true)
        }
        combs(i - 1, r)
      }

      val combSize = 4
      for (bs <- combs(combSize, (for (_ <- 0 until Util.pow(combSize, 2).toInt) yield Vector[Boolean]()).toVector)) {
        assert(bs.size == combSize)
        if (!isInGitHubAction || bs.forall(b => b)) {
          val name = s"${k.last}_${if (bs(0)) AnvilTest.splitTempId else AnvilTest.singleTempId}_${if (bs(1)) AnvilTest.tempLocalId else AnvilTest.memLocalId}_${if (bs(2)) if (bs(3)) AnvilTest.withMemIpId else AnvilTest.withIpId else AnvilTest.withoutIpId}".
            replace('.', '_')
          r = r :+ (k.dropRight(1) :+ name, v)
        }
      }
      r
    }) yield pair
  }


  override def check(p: Vector[Predef.String], content: Predef.String): Boolean = {
    val path = p.dropRight(1) :+ s"${p.last.substring(0, p.last.lastIndexOf("_sc_"))}.sc"
    val file = String(path.last)
    val out = dir /+ ISZ(p.map(String(_)): _*)
    val reporter = message.Reporter.create
    lang.parser.Parser.parseTopUnit[lang.ast.TopUnit.Program](content, T, F, Some(path.mkString("/")), reporter) match {
      case Some(program) if !reporter.hasError =>
        val (th2, _) = lang.FrontEnd.checkWorksheet(100, Some(th), program, reporter)
        (dir / path(0)).removeAll()
        var config = getConfig(F, file, p)

        if (isInGitHubAction) {
          config = config(simOpt = None())
        }

        val irOpt = Anvil.synthesize(!dontTestFileSet.contains(file), lang.IRTranslator.createFresh, th2, ISZ(), config,
          AnvilOutput(F, init.versions.get("org.sireum.version.sbt").get, out), reporter)
        reporter.printMessages()
        if (reporter.hasError) {
          return F
        }
        val ir = irOpt.get

        if (!(config.genVerilog || config.simOpt.nonEmpty)) {
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
        //val axiWrapperVerilogCommandStr: String = s"Test/runMain AXIWrapperChiselGenerated${ir.name}VerilogGeneration"
        val verilogCommandStr: String = s"Test/runMain ${ir.name}VerilogGeneration"
        val simCommandStr: String = s"Test/testOnly *${ir.name}Bench"
        val sbtOpts = ISZ[String]("-J-Xss32m")
        if (config.genVerilog) {
          Os.proc(ISZ[String]("bash", sbt.string) ++ sbtOpts :+ s"$verilogCommandStr").
            at(chiselDir).env(envVars).echo.console.runCheck()
        } /* else if (config.axi4) {
          Os.proc(ISZ[String]("bash", sbt.string) ++ sbtOpts :+ s"$axiWrapperVerilogCommandStr").
            at(chiselDir).env(envVars).echo.console.runCheck()
        }*/ else {
          config.simOpt match {
            case Some(_) if verilatorBin.exists =>
              Os.proc(ISZ[String]("bash", sbt.string) ++ sbtOpts :+ s"$simCommandStr").
                at(chiselDir).env(envVars).echo.console.runCheck()
            case _ =>
          }
        }
        return T
      case _ => return F
    }

  }
}