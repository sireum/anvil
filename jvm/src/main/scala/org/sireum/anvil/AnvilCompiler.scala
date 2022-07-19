// #Sireum

package org.sireum.anvil

import org.sireum._
import org.sireum.anvil.Context._
import org.sireum.ops.{ISZOps, StringOps}

object AnvilCompiler {

  type TranspilerMirror = TranspilersCOptionMirror => Z

  val hlsTclFilename: String = "run-hls.tcl"
  val hlsTclBash: String = "run-hls.sh"
  val hlsTclBat: String = "run-hls.bat"

  val hwTclFilename: String = string"run-hw.tcl"
  val hwTclBash: String = string"run-hw.sh"
  val hwTclBat: String = string"run-hw.bat"

  val plScriptFilename: String = "run-petalinux.sh"

  @pure def checkpoint(): Unit = {
    unit()
  }

  def compile(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext, tm: TranspilerMirror): Z = {
    @pure def shouldRunStage(stage: CompileStage.Type): B = {
      return ec.stages.contains(stage)
    }

    @pure def ws(): ProjectWorkspace = {
      return ec.projectContext.projectWorkspace
    }

    // if unmodified.sourcepath contains a single .slang file, return it wrapped in a singleton sequence.
    // otherwise, return an empty sequence (EXPERIMENTAL)
    @pure def tryAltArgs(unmodified: TranspilersCOptionMirror): ISZ[String] = {
      val sp = unmodified.sourcepath

      if (sp.size == z"1") {
        val file = Os.path(sp(z"0"))
        if (file.ext == "slang" && file.exists && file.isFile) {
          return ISZ(file.canon.abs.string)
        }
      }

      return ISZ()
    }

    def invokeTranspilerPass1(): Z = {
      val unmodified: TranspilersCOptionMirror = ec.projectContext.transpilerArgs

      // experimental: sourcepaths containing a single .slang file are converted into a form recognized by CTranspiler
      val a: ISZ[String] = tryAltArgs(unmodified)
      val sp: ISZ[String] = if (a.isEmpty) unmodified.sourcepath else ISZ()

      val modified = TranspilersCOptionMirror(
        help = unmodified.help,
        args = a, // <-- changed
        sourcepath = sp, // <-- changed
        strictAliasing = unmodified.strictAliasing,
        output = Some(ws().transpiled.abs.string), // <-- changed
        verbose = unmodified.verbose,
        apps = unmodified.apps,
        bitWidth = unmodified.bitWidth,
        projectName = unmodified.projectName,
        stackSize = unmodified.stackSize,
        customArraySizes = unmodified.customArraySizes,
        maxArraySize = unmodified.maxArraySize,
        maxStringSize = unmodified.maxStringSize,
        cmakeIncludes = unmodified.cmakeIncludes,
        exts = unmodified.exts,
        libOnly = unmodified.libOnly,
        excludeBuild = unmodified.excludeBuild,
        plugins = unmodified.plugins,
        fingerprint = unmodified.fingerprint,
        stableTypeId = unmodified.stableTypeId,
        unroll = unmodified.unroll,
        save = unmodified.save,
        load = unmodified.load,
        customConstants = unmodified.customConstants,
        forwarding = unmodified.forwarding,
        anvilTranspilerPass = TranspilersCAnvilExecutionPassMirror.First, // <-- changed
        anvilTranspilerContext = ec.projectContext.methodDescriptor // <-- changed
      )

      // todo modify c transpiler call to accept extra c-make-includes when creating blank driver files
      val result = tm(modified) // invoke the CTranspiler

      ec.sandbox match {
        case Some(sb) => {
          // Transpiler passes are always run locally.
          // If a sandbox is specified, it will simply receive a copy of the result.
          //
          // By default, the "sireum anvil sandbox" cli command will install kekinian in the sandbox.
          // Users wanting to run transpiler-pass-1 or transpiler-pass-2 from inside the sandbox can open
          // a shell or vm (via Vagrant or VirtualBox) and run the desired "sireum anvil --stage hls ..." command from
          // within (no --sandbox-path <path> needed).
          // todo consider adding this capability to anvil directly as a flag, e.g. --fully-isolated-build or something
          sb.clearDirectory(sb.workspace.transpiled)
          sb.push(ec.projectContext.projectWorkspace.transpiled, sb.workspace.transpiled)
        }
        case _ => unit()
      }
      return result
    }

    def invokeTranspilerPass2(): Z = {
      val unmodified: TranspilersCOptionMirror = ec.projectContext.transpilerArgs
      val driverExts: ISZ[String] = ws().driverCalls.list.map((p: Os.Path) => p.value)

      val a: ISZ[String] = tryAltArgs(unmodified)
      val sp: ISZ[String] = if (a.isEmpty) unmodified.sourcepath else ISZ()

      val modified = TranspilersCOptionMirror(
        help = unmodified.help,
        args = a, // <-- changed
        sourcepath = sp, // <-- changed
        strictAliasing = unmodified.strictAliasing,
        output = Some(ws().modifiedTranspiled.abs.string), // <-- changed
        verbose = unmodified.verbose,
        apps = unmodified.apps, // we can avoid copying these later because app names are exact aliases
        bitWidth = unmodified.bitWidth,
        projectName = unmodified.projectName,
        stackSize = unmodified.stackSize,
        customArraySizes = unmodified.customArraySizes, // this is also called "sequence size"
        maxArraySize = unmodified.maxArraySize,
        maxStringSize = unmodified.maxStringSize,
        cmakeIncludes = unmodified.cmakeIncludes,
        exts = unmodified.exts ++ driverExts, // <-- changed to prevent ext files from being written
        libOnly = unmodified.libOnly,
        excludeBuild = unmodified.excludeBuild,
        plugins = unmodified.plugins,
        fingerprint = unmodified.fingerprint,
        stableTypeId = unmodified.stableTypeId,
        unroll = unmodified.unroll,
        save = unmodified.save,
        load = unmodified.load,
        customConstants = unmodified.customConstants,
        forwarding = unmodified.forwarding,
        anvilTranspilerPass = TranspilersCAnvilExecutionPassMirror.Second, // <-- changed
        anvilTranspilerContext = ec.projectContext.methodDescriptor // <-- changed
      )

      val result = tm(modified) // invoke the CTranspiler
      ec.sandbox match {
        case Some(sb) => {
          // Transpiler passes are always run locally.
          // Read comments in invokeTranspilerPass1() for a longer explanation.
          sb.clearDirectory(sb.workspace.modifiedTranspiled)
          sb.push(ec.projectContext.projectWorkspace.modifiedTranspiled, sb.workspace.modifiedTranspiled)
        }
        case _ => unit()
      }
      return result
    }

    var status: Z = z"0"
    checkpoint()

    def copySources(): Z = {
      val sp = ec.projectContext.transpilerArgs.sourcepath
      val p = Os.path(st"${(sp, "/")}".render)
      p.copyOverTo(ws().original)
      ec.sandbox match {
        case Some(sb) => {
          sb.clearDirectory(sb.workspace.original)
          sb.push(ws().original, sb.workspace.original)
        }
        case _ => unit()
      }
      return z"0"
    }

    if (shouldRunStage(CompileStage.Hls)) {
      // copy source files into Anvil's workspace
      status = copySources()
      if (status != z"0") {
        return status
      }
      checkpoint()

      // run Anvil's first transpiler pass to produce hls-compatible C code
      status = invokeTranspilerPass1()
      if (status != z"0") {
        return status
      }
      checkpoint()

      assert(ws().transpiled.list.nonEmpty, "Transpiler should have generated some output")

      // run Anvil's HLS stage to generate the function IP and driver files
      status = runHLS(hc, tc, ec)
      if (status != z"0") {
        return status
      }
      checkpoint()
    }

    if (shouldRunStage(CompileStage.Hw)) {
      // run Anvil's HW stage to place the IP into the overall block design, then generate a hardware bitstream file
      status = runHW(hc, tc, ec)
      if (status != z"0") {
        return status
      }
      checkpoint()
    }

    if (shouldRunStage(CompileStage.Sw)) {
      // run Anvil's SW stage to: generate code to call the drivers created in the HLS stage.
      status = runSW(hc, tc, ec)
      if (status != z"0") {
        return status
      }
      checkpoint()

      // re-run the c transpiler with all hw-accelerated functions now calling a unique new extension method
      // generate driver calls inside those new ext methods
      status = invokeTranspilerPass2()
      if (status != z"0") {
        return status
      }
      checkpoint()
    }

    if (shouldRunStage(CompileStage.Os)) {
      // run Anvil's OS stage to place
      status = runOS(hc, tc, ec)
      if (status != z"0") {
        return status
      }
      checkpoint()
    }
    checkpoint()

    return z"0"
  }

  def runHLS(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): Z = {
    val context = ec.projectContext
    val workspace = context.projectWorkspace

    def writeHlsTemplate(): Unit = {

      def createHlsTemplate(): String = {
        // workspace.transpiled holds the hardware-accelerated c code, and we want to ref that in HLS project
        // added cflags and fno-builtin, see https://www.xilinx.com/html_docs/xilinx2017_4/sdaccel_doc/wqn1504034365505.html

        // lookup list of files contained in "anvil_cfiles.txt" (which was generated during HLS step 1)
        // each listed file is relative to workspace.transpiled
        // we want to access them in hls. Hls is launched from project which has in scope our sw/
        // So really we link transpiled and hls, but are one scope up

        // empty corresponds with return
        // todo derive filename from config
        val srcs: ISZ[String] = (workspace.transpiled / string"anvil_cfiles.txt").readLines
          .map((st: String) => workspace.project.relativize(workspace.transpiled / st).string)
          .map((s: String) => StringOps(s).replaceAllLiterally("\\", "/"))

        // todo derive filename from config
        val dirs: ISZ[String] = (workspace.transpiled / string"anvil_include_dirs.txt").readLines
          .map((st: String) => workspace.project.relativize(workspace.transpiled / st).string)
          .map((s: String) => StringOps(s).replaceAllLiterally("\\", "/"))

        // todo derive filename from config
        // the top function's corresponding name in the transpiled c code.
        {
          val expected: String = context.template_project_top_function
          val actual: String = ISZOps((workspace.transpiled / string"anvil_top_function.txt").readLines).first
          // sanity check: the first line of the file written during transpiler-pass-1 matches the target method
          expect(expected == actual,
            st"expected top function $expected did not match the transpiled project's actual top function $actual")
        }

        // todo derive filename from config
        // drop the method name (first line) and all other params are "in" ports because return is our "out" port
        val inPorts: ISZ[String] = ISZOps((workspace.transpiled / string"anvil_top_function.txt").readLines).drop(z"1")

        // empty string represents the function's return value (our "out" port)
        val ports: ISZ[String] = ISZ(string"") ++ inPorts

        // TODO NOTE: data_pack inPort optimization directives only apply to arrays or array-containing structs
        // todo how to make this context pluggable across versions? Potentially needs template.
        // todo re-added -fno-builtin flag to add_files (for manual testing, will remove)
        // todo re-added -reset flag to open_project (for testing, may remove)
        return st"""
                   |open_project -reset ${context.projectWorkspace.hls.name}
                   |set_top ${context.template_project_top_function}
                   |${st"${(for (s <- srcs) yield st"add_files $s -cflags ${"\""}-std=c99 -fno-builtin ${(for (d <- dirs) yield st"-I$d -L$d", " ")}${"\""}", "\n")}".render}
                   |open_solution "${context.template_project_hls_solution}"
                   |set_part {${hc.template_project_part_number}}
                   |create_clock -period 10 -name default
                   |config_export -format ip_catalog -rtl verilog
                   |config_interface -m_axi_addr64
                   |set_directive_inline -region -recursive ${"\""}${context.template_project_top_function}${"\""}
                   |${st"${(for (p <- ports) yield st"set_directive_interface -mode s_axilite ${"\""}${context.template_project_top_function}${"\""} $p", "\n")}".render}
                   |${st"${(for (in <- inPorts) yield st"set_directive_data_pack -byte_pad field_level ${"\""}${context.template_project_top_function}${"\""} $in", "\n")}".render}
                   |csynth_design
                   |export_design -rtl verilog -format ip_catalog
                   |exit
                   |""".render
      }

      @pure def createHlsShellScript(): String = {
        val vivadoScriptCmd = st"${(ISZ(st"vivado_hls", st"-f", st"$hlsTclFilename"), " ")}"
        val vivadoSource: ST = ec.sandbox match {
          case Some(sb) => st"source ${(sb.vivadoSourceScriptPath, string"/")}"
          case _ => st"echo 'WARNING: custom environment detected! Please source vivado settings64.sh before running this script'"
        }
        val lines = ISZ(st"#!/bin/bash", vivadoSource, vivadoScriptCmd)
        val result = st"${(lines, "\n")}"
        return result.render
      }

      @pure def createHlsBatScript(): String = {
        return st"vivado_hls -f $hlsTclFilename".render
      }

      // tcl file (automatically invoked by Anvil)
      Workspace.writeOver(workspace.project / hlsTclFilename, createHlsTemplate())

      // bash script that reruns hls sub-step part 2/2 without first Anvil codegen (manually invoked by mac/linux users)
      Workspace.writeOverScript(workspace.project / hlsTclBash, createHlsShellScript())

      // batch script that reruns hls sub-step part 2/2 without first Anvil codegen (manually invoked by windows users)
      Workspace.writeOverScript(workspace.project / hlsTclBat, createHlsBatScript())
    }

    // run
    writeHlsTemplate()
    ec.sandbox match {
      case Some(sb) => {
        // TODO remove symlinks? test window symlinks with vagrant ssh
        // TODO warn user that the sandbox must be up (check status with vagrant status)

        // clear dirs (in sandbox)
        sb.clearDirectory(sb.workspace.hls)

        // push scripts
        sb.push(workspace.project / hlsTclBat, sb.workspace.project :+ hlsTclBat)
        sb.push(workspace.project / hlsTclBash, sb.workspace.project :+ hlsTclBash)
        sb.push(workspace.project / hlsTclFilename, sb.workspace.project :+ hlsTclFilename)

        // run vivado hls (in sandbox)
        sb.ssh(ISZ("vivado_hls", "-f", hlsTclFilename))

        // pull result
        sb.pull(workspace.hls, sb.workspace.hls)
      }
      case _ => {
        // run vivado hls locally
        runProc(workspace.project, ISZ("vivado_hls", "-f", hlsTclFilename))
      }
    }
    return z"0"
  }

  def runHW(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): Z = {
    return z"0"
  }

  def runSW(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): Z = {
    return z"0"
  }

  def runOS(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): Z = {
    return z"0"
  }

}


