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
import org.sireum.U64._

object IRSimulatorTest {
  val th = lang.FrontEnd.checkedLibraryReporter._1.typeHierarchy
  val dir: Os.Path = Os.path(implicitly[sourcecode.File].value).up.up.up.up.up.up.up / "result-sim"
  val errAsOut: Boolean = T
}

import IRSimulatorTest._

class IRSimulatorTest extends SireumRcSpec {
  {
    val debug = T & Os.env("GITHUB_ACTIONS").isEmpty
    IRSimulator.DEBUG = T & debug
    IRSimulator.DEBUG_TEMP = T & debug
    IRSimulator.DEBUG_EDIT = T & debug
    IRSimulator.DEBUG_GLOBAL = T & debug
    IRSimulator.DEBUG_LOCAL = F & debug
  }

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, _) => p.last == "factorial.sc" || p.last == "add.sc" || p.last == "bubble.sc" || p.last == "1.example.sc" || p.last == "2.example.sc" || p.last == "3.example.sc" || p.last == "4.example.sc" || p.last == "5.example.sc" || p.last == "6.example.sc"}//!p.last.endsWith("dll.sc") && !p.last.endsWith("print.sc") }
    implicit val ordering: Ordering[Vector[Predef.String]] = m.ordering
    for ((k, v) <- m; pair <- {
      var r = Vector[(Vector[Predef.String], Predef.String)]()

//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.singleTempId}, ${AnvilTest.memLocalId}, ${AnvilTest.withoutIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.singleTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.withoutIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.memLocalId}, ${AnvilTest.withoutIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.withoutIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.tempGlobalId}, ${AnvilTest.withoutIpId})", v)
//
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.singleTempId}, ${AnvilTest.memLocalId}, ${AnvilTest.withIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.singleTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.withIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.memLocalId}, ${AnvilTest.withIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.withIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.tempGlobalId}, ${AnvilTest.withIpId})", v)
//
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.singleTempId}, ${AnvilTest.memLocalId}, ${AnvilTest.withMemIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.singleTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.withMemIpId})", v)
//      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.memLocalId}, ${AnvilTest.withMemIpId})", v)
      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.withMemIpId})", v)
      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.tempGlobalId}, ${AnvilTest.withMemIpId})", v)
      r = r :+ (k.dropRight(1) :+ s"${k.last} (${AnvilTest.splitTempId}, ${AnvilTest.tempLocalId}, ${AnvilTest.tempGlobalId}, ${AnvilTest.withMemIpId}, ${AnvilTest.alignId})", v)

      r
    }) yield pair
  }

  def redirectConsole[T](output: Os.Path, f: () => T): T = {
    val oldOut = System.out
    val oldErr = System.err
    val bout = new java.io.ByteArrayOutputStream() {
      override def write(b: Int): Unit = {
        super.write(b)
        oldOut.write(b)
        oldOut.flush()
      }

      override def write(b: Array[Byte], off: Int, len: Int): Unit = {
        super.write(b, off, len)
        oldOut.write(b, off, len)
        oldOut.flush()
      }
    }
    val berr = if (errAsOut) bout else new java.io.ByteArrayOutputStream() {
      override def write(b: Int): Unit = {
        super.write(b)
        oldErr.write(b)
        oldErr.flush()
      }

      override def write(b: Array[Byte], off: Int, len: Int): Unit = {
        super.write(b, off, len)
        oldErr.write(b, off, len)
        oldErr.flush()
      }
    }
    val out = new java.io.PrintStream(bout)
    val err = new java.io.PrintStream(berr)
    try {
      System.setOut(out)
      System.setErr(err)
      val r = f()
      System.out.flush()
      System.err.flush()
      output.up.mkdirAll()
      return r
    } catch {
      case t: Throwable =>
        val sw = new java.io.StringWriter
        t.printStackTrace(new java.io.PrintWriter(sw))
        sw.flush()
        eprintln(sw.toString)
        System.out.flush()
        System.err.flush()
        throw t
    } finally {
      output.writeOver(bout.toString("UTF-8"))
      if (!errAsOut) {
        output.writeAppend(berr.toString("UTF-8"))
      }
      System.setErr(oldErr)
      System.setOut(oldOut)
    }
  }

  override def check(p: Vector[Predef.String], content: Predef.String): Boolean = {
    val path = p.dropRight(1) :+ p.last.substring(0, p.last.lastIndexOf(" ("))
    val file = String(path.last)
    val out = dir /+ ISZ(p.map(String(_)): _*)
    def checkH(): Boolean = {
      val reporter = message.Reporter.create
      lang.parser.Parser.parseTopUnit[lang.ast.TopUnit.Program](content, T, F, Some(path.mkString("/")), reporter) match {
        case Some(program) if !reporter.hasError =>
          val (th2, p2) = lang.FrontEnd.checkWorksheet(100, Some(th), program, reporter)
          var lastMethod: String = ""
          for (stmt <- p2.body.stmts) {
            stmt match {
              case stmt: lang.ast.Stmt.Method => lastMethod = stmt.sig.id.value
              case _ =>
            }
          }
          out.removeAll()
          val config = AnvilTest.getConfig(F, file, p)
          Anvil.generateIR(T, lang.IRTranslator.createFresh, th2, ISZ(), config, AnvilOutput(F, "", out), reporter) match {
            case Some(ir) =>
              val p = ir.program.procedures(0)
              val state = IRSimulator.State.create(ir.anvil, p.owner :+ p.id, ir.maxRegisters, ir.globalInfoMap, ir.globalTemps)
              val testNumInfoOffset = ir.globalInfoMap.get(Util.testNumName).get.loc
              var locals = ISZ[Intrinsic.Decl.Local]()
              for (entry <- ir.anvil.procedureParamInfo(Util.PBox(ir.program.procedures(0)))._2.entries) {
                val (id, info) = entry
                locals = locals :+ Intrinsic.Decl.Local(info.loc, info.totalSize, id, info.tipe)
              }
              IRSimulator.State.Edit.Temp(
                IRSimulator.State.Edit.Temp.Kind.SP,
                ir.anvil.isFP(ir.anvil.spType),
                ir.anvil.isSigned(ir.anvil.spType),
                ir.anvil.typeBitSize(ir.anvil.spType),
                0,
                IRSimulator.Value.fromZ(ir.globalSize, ir.anvil.typeBitSize(ir.anvil.spType),
                  ir.anvil.isSigned(ir.anvil.spType)),
                IRSimulator.State.Accesses.empty).update(state)
              IRSimulator.State.Edit.Decl(Intrinsic.Decl(F, F, locals, ir.program.procedures(0).pos)).update(state)
              if (config.alignAxi4) {
                assert(testNumInfoOffset % 8 == 0)
                IRSimulator.State.Edit.Memory64(testNumInfoOffset / 8, ISZ(u64"0xFFFFFFFFFFFFFFFF"),
                  IRSimulator.State.Accesses.empty).update(state)
              } else {
                IRSimulator.State.Edit.Memory(testNumInfoOffset,
                  for (_ <- 0 until ir.anvil.typeByteSize(AST.Typed.z)) yield u8"0xFF",
                  IRSimulator.State.Accesses.empty).update(state)
              }
              IRSimulator(ir).evalProcedure(state, ir.program.procedures(0))
              val displaySize = ir.anvil.config.printSize
              if (ir.anvil.config.shouldPrint) {
                val offset = ir.globalInfoMap.get(Util.displayName).get.loc +
                  ir.anvil.typeShaSize + ir.anvil.typeByteSize(AST.Typed.z)
                val dp = if (config.isFirstGen) state.DP.toZ else {
                  val offset = ir.globalInfoMap.get(Util.dpName).get.loc
                  if (config.alignAxi4) {
                    state.memory64(offset / 8).toZ
                  } else {
                    var r = u64"0"
                    var mask = u64"0"
                    val size = ir.anvil.typeByteSize(ir.anvil.dpType)
                    for (i <- 0 until size) {
                      val b = conversions.U8.toU64(state.memory(offset + i))
                      r = r | (b << mask)
                      mask = mask + u64"8"
                    }
                    r.toZ
                  }
                }
                val (lo, hi): (Z, Z) = if (dp < displaySize) (0, dp) else (dp, displaySize + dp - 1)
                val u8ms = MSZ.create(hi - lo, u8"0")
                var j: Z = 0
                if (ir.anvil.config.alignAxi4) {
                  def getU8(addr8: Z): U8 = {
                    val addr64 = addr8 / 8
                    val v = state.memory64(addr64)
                    val rem = addr8 % 8
                    val shift = conversions.Z.toU64(rem) << u64"3"
                    val mask = u64"0xFF" << shift
                    val r = (v & mask) >>> shift
                    //println(s"display: $offset, add8: $addr8, addr64: $addr64, v: $v, shift: ${shift.toZ}, rem: $rem, mask: $mask, r: $r")
                    return conversions.U64.toU8(r)
                  }
                  for (i <- lo until hi) {
                    val addr = offset + (i % displaySize)
                    u8ms(j) = getU8(addr)
                    j = j + 1
                  }
                } else {
                  def getU8(addr8: Z): U8 = {
                    val r = state.memory(addr8)
                    //println(s"display: $offset, add8: $addr8, r: $r")
                    return r
                  }
                  for (i <- lo until hi) {
                    val addr8 = offset + (i % displaySize)
                    u8ms(j) = getU8(addr8)
                    j = j + 1
                  }
                }
                val display = conversions.String.fromU8ms(u8ms)
                print(display)

                Util.postProcessStackTrace(ir.procDescMap, display) match {
                  case Some(d) =>
                    println()
                    println("After post-processing stack trace, display is:")
                    println(d)
                  case _ =>
                }
              }
            case _ =>
          }
          reporter.printMessages()
          T
        case _ => return F
      }
    }
    redirectConsole(out / "output.txt", checkH _)
  }
}