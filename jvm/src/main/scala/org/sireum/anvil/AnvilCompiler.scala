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
 
        return st"""
                   |open_project ${context.projectWorkspace.hls.name}
                   |set_top ${context.template_project_top_function}
                   |${st"${(for (s <- srcs) yield st"add_files $s -cflags ${"\""}-std=c99 ${(for (d <- dirs) yield st"-I$d -L$d", " ")}${"\""}", "\n")}".render}
                   |open_solution "${context.template_project_hls_solution}"
                   |set_part {${hc.template_project_part_number}}
                   |create_clock -period 10 -name default
                   |config_export -format ip_catalog -rtl verilog
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
        sb.ssh(ISZ("vivado_hls", "-f", hlsTclFilename), T, F)

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
    val workspace = ec.projectContext.projectWorkspace

    def writeHwTemplate(): Unit = {

      def tclFile(): String = {
        // TODO need template-selection process in Context (ask for advice)
        return Templates.zedboard_vivado_2020_1(hc, tc, ec)
      }

      @pure def shellScript(): String = {
        val command = st"#!/bin/bash\nvivado -mode batch -source $hwTclFilename"
        val source: ST = ec.sandbox match {
          case Some(sb) => st"source ${(sb.vivadoSourceScriptPath, string"/")}"
          case _ => st"echo 'WARNING: custom environment detected! Please source vivado settings64.sh before running this script'"
        }
        val lines = ISZ(st"#!/bin/bash", source, command)
        val result = st"${(lines, "\n")}"
        return result.render
      }

      @pure def batchScript(): String = {
        return st"vivado -mode batch -source $hwTclBat".render
      }

      Workspace.writeOver(workspace.project / hwTclFilename, tclFile())
      Workspace.writeOverScript(workspace.project / hwTclBash, shellScript())
      Workspace.writeOverScript(workspace.project / hwTclBat, batchScript())
    }

    writeHwTemplate()
    ec.sandbox match {
      case Some(sb) => {
        // clear dirs
        sb.clearDirectory(sb.workspace.hw)

        // push
        sb.push(workspace.project / hwTclBat, sb.workspace.project :+ hwTclBat)
        sb.push(workspace.project / hwTclBash, sb.workspace.project :+ hwTclBash)
        sb.push(workspace.project / hwTclFilename, sb.workspace.project :+ hwTclFilename)

        // run vivado hls
        sb.ssh(ISZ(string"vivado", "-mode", "batch", "-source", hwTclFilename), T, F)

        // pull
        sb.pull(workspace.hw, sb.workspace.hw)
      }
      case _ => runProc(workspace.project, ISZ("vivado", "-mode", "batch", "-source", hwTclFilename))
    }
    return z"0"
  }

  def runSW(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): Z = {

    def writeSwTemplate(): Unit = {

      def generateDriverCall(baseDriverH: String, args: ISZ[AnvilDriverParser.Arg]): String = {
        val returnArgName = "return"
        assert(ISZOps(args.map((arg: AnvilDriverParser.Arg) => arg.name)).contains(returnArgName), s"cannot generate driver call without a return type: $args")

        val retTypeString = ISZOps(args.filter((arg: AnvilDriverParser.Arg) => arg.name == returnArgName)).first.tipe
        val topFn = ec.projectContext.template_project_top_function
        val params = args.filter((arg: AnvilDriverParser.Arg) => arg.name != returnArgName)
        assert(ISZOps(params).forall((arg: AnvilDriverParser.Arg) => arg.kind != AnvilDriverParser.Direction.Out), "params should only contain input args")

        val out: AnvilDriverParser.Arg = {
          val outs = args.filter((arg: AnvilDriverParser.Arg) => arg.name == returnArgName)
          assert(outs.size == z"1", "there must be exactly one output parameter")
          assert(ISZOps(outs).first.kind == AnvilDriverParser.Direction.Out, "return arg must strictly be an out type")
          ISZOps(outs).first
        }

        val paramsST: ST = st"${(for (param <- params) yield st"${param.tipe} ${param.name}", ", ")}"
        val ptrName: String = s"X${StringOps(tc.driverBaseFileName(hc, ec)).firstToUpper}"

        // string template of all arg's setters. Mapped to correct function based on in or out
        @pure def toFnName(param: AnvilDriverParser.Arg): ST = {
          val callerArgs: ST = if (param.isArray) st"(&ptr, 0, (char *) ${param.name}, sizeof((char *) ${param.name}))" else st"(&ptr, ${param.name})"
          val r: ST = param.kind match {
            case AnvilDriverParser.Direction.In => {
              st"${ptrName}_${if (param.isArray) st"Write" else st"Set"}_${param.name}${callerArgs};"
            }
            case AnvilDriverParser.Direction.Out => {
              st"${ptrName}_${if (param.isArray) st"Read" else st"Get"}_${param.name}${callerArgs};"
            }
            case AnvilDriverParser.Direction.InOut => {
              // same as in case // TODO watch for HLS Read/Write permission expansion optimize (disabled)
              st"${ptrName}_${if (param.isArray) st"Write" else st"Set"}_${param.name}${callerArgs};"
            }
          }
          return r
        }

        val setters: ST = st"${(params.map((param: AnvilDriverParser.Arg) => toFnName(param)), "\n")}"
        val getter: ST = st"${toFnName(out)}"
        val instanceName = ec.projectContext.mangledMethodName
        val driverProxyPrefix = ec.projectContext.methodDriverProxyPrefix
        val debugPrint: ST =
          st"""
              |printf("interrupt status: %u\r\n", ${ptrName}_InterruptGetStatus(&ptr));
              |printf("interrupt enabled? %u\r\n", ${ptrName}_InterruptGetEnabled(&ptr));
              |printf("ready? %u\r\n", ${ptrName}_IsReady(&ptr));
              |printf("idle? %u\r\n", ${ptrName}_IsIdle(&ptr));
              |printf("done? %u\r\n", ${ptrName}_IsDone(&ptr));
              """
        val template: ST =
          st"""
              |#include <all.h>
              |
              |#include <${baseDriverH}>
              |
              |${retTypeString} ${driverProxyPrefix}${topFn}(${paramsST}) {
              |    static int initialized = 0;
              |    static int shouldRelease = 0; // unused
              |    static ${ptrName} ptr;
              |
              |    if (initialized == 0) {
              |        printf("About to init...\r\n");
              |        int status = ${ptrName}_Initialize(&ptr, "$instanceName");
              |        if (status != XST_SUCCESS) {
              |            printf("Error initializing acceleration: %d\r\n", status);
              |            exit(EXIT_FAILURE);
              |        }
              |        initialized = 1;
              |        printf("Successful init! Fetching status...\r\n");
              |    }
              |
              |    $debugPrint
              |
              |    printf("About to run\r\n");
              |    while (!${ptrName}_IsReady(&ptr)) {
              |        printf("Device not ready! Looping...\r\n");
              |        $debugPrint
              |    }
              |    $debugPrint
              |    $setters
              |    ${ptrName}_Start(&ptr); // indicate when block can start processing data
              |    while (!${ptrName}_IsDone(&ptr)) {
              |        printf("Device not done! Looping...\r\n");
              |        $debugPrint
              |    }
              |
              |    printf("getting result...\r\n");
              |    ${retTypeString} result;
              |    result = ${ptrName}_Get_return(&ptr);
              |
              |    printf("running sanity check..."); // newline intentionally omitted
              |    // ${retTypeString} result2;
              |    // result2 = $getter;
              |
              |   // if (result == result2) {
              |   //     printf("SUCCESS!\r\n");
              |   // } else {
              |   //     printf("FAILURE!\r\n");
              |   // }
              |
              |    if (shouldRelease != 0) {
              |        printf("Releasing device...\r\n");
              |        int status = ${ptrName}_Release(&ptr);
              |        if (status != XST_SUCCESS) {
              |            printf("Error releasing: status\r\n");
              |            exit(EXIT_FAILURE);
              |        }
              |        printf("Device released!\r\n");
              |    }
              |
              |    printf("Returning!\r\n");
              |
              |    return result;
              |}"""

        return template.render
      }

      // precondition
      assert(tc.hlsDriverImplDirectory(hc, ec).isDir, "Drivers should be generated by HLS stage before SW stage can run.")
      // copy drivers and create bridge in driverCalls
      val drivers = tc.hlsDriverImplDirectory(hc, ec)
      val driverName = tc.driverBaseFileName(hc, ec)
      val baseDriverH = tc.baseDriverHFileName(hc, ec)
      val baseDriverC = tc.baseDriverCFileName(hc, ec)
      val hwDriverH = tc.hwDriverHFileName(hc, ec)
      val linuxDriverC = tc.linuxDriverCFileName(hc, ec)
      val args: ISZ[AnvilDriverParser.Arg] = AnvilDriverParser.readTypes(driverName, drivers / baseDriverH)

      val workspace = ec.projectContext.projectWorkspace

      def driverInterceptCopy(driver: Os.Path, target: Os.Path): Unit = {
        def hhook(sourceLine: String): Jen[String] = {
          val intercepted = tc.applyDriverSourceCodeLineHooks(hc, ec, baseDriverH, sourceLine)
          return Jen.IS(intercepted).map((line: String) => st"$line\n".render)
        }

        val source = driver.readLineStream
        val sourceWithHooks = source.flatMap(hhook _)
        target.writeOverLineStream(sourceWithHooks)
      }

      // copy Vivado-generated drivers while applying sourcecode hooks from ToolchainContext
      driverInterceptCopy(drivers / baseDriverH, workspace.driverCalls / baseDriverH)
      driverInterceptCopy(drivers / baseDriverC, workspace.driverCalls / baseDriverC)
      driverInterceptCopy(drivers / hwDriverH, workspace.driverCalls / hwDriverH)
      driverInterceptCopy(drivers / linuxDriverC, workspace.driverCalls / linuxDriverC)

      // copy Anvil-generated driver. (No need to apply sourcecode hooks to Anvil-generated sourcecode)
      Workspace.writeOver(workspace.driverCalls / s"x${driverName}_anvil.c", generateDriverCall(baseDriverH, args))
    }

    writeSwTemplate()
    ec.sandbox match {
      case Some(sb) => {
        sb.clearDirectory(sb.workspace.driverCalls)
        sb.push(ec.projectContext.projectWorkspace.driverCalls, sb.workspace.driverCalls)
      }
      case _ => unit()
    }

    return z"0"
  }

  def runOS(hc: HardwareContext, tc: ToolchainContext, ec: ExecutionContext): Z = {
    val workspace: ProjectWorkspace = ec.projectContext.projectWorkspace

    @pure def createPetalinuxScript(): String = {

      val appName: String = "anvil"

      @pure def bitbakeTemplateString(): String = {
        val apps = ec.projectContext.transpilerArgs.apps
        val bbFile = s"project-spec/meta-user/recipes-apps/$appName/$appName.bb"

        // note: seems to leave carriage returns:
        //${st"${(args.apps.map((app: String) => s"echo '    install -m 755 ${"${WORKDIR}"}/build/$app ${"${D}${bindir}"}' >> ${"$APP_BB_FILE"}"), "\n")}".render}
        //${StringOps(st"${(ec.projectContext.apps.map((app: String) => s"echo '    install -m 755 ${"${WORKDIR}"}/build/$app ${"${D}${bindir}"}' >> ${"$APP_BB_FILE"}"), "\n")}".render).replaceAllLiterally("\r","")}

        def formatAppNameToBitbake(app: String): String = {
          val lastDotSeparatorIndex: Z = ops.StringOps(app).lastIndexOf(c".")
          if (lastDotSeparatorIndex != z"-1" && lastDotSeparatorIndex != app.size - z"1") {
            val r: String = ops.StringOps(app).substring(lastDotSeparatorIndex + z"1", app.size)
            println(s"WARNING: renaming $app to $r for bitbake compatibility") // todo consider eprintln
            return r
          } else {
            return app
          }
        }

        return s"""
APP_BB_FILE=$bbFile
echo '' > ${"$APP_BB_FILE"}
echo 'SUMMARY = "Generated ${ec.projectContext.template_project_top_function} application."' >> ${"$APP_BB_FILE"}
echo 'SECTION = "PETALINUX/apps"' >> ${"$APP_BB_FILE"}
echo 'LICENSE = "CLOSED"' >> ${"$APP_BB_FILE"}
echo 'PR = "r0"' >> ${"$APP_BB_FILE"}
echo '' >> ${"$APP_BB_FILE"}
echo 'SRC_URI = "${"file://*"}"' >> ${"$APP_BB_FILE"}
echo 'S = "${"${WORKDIR}"}"' >> ${"$APP_BB_FILE"}
echo '' >> ${"$APP_BB_FILE"}
echo 'inherit cmake' >> ${"$APP_BB_FILE"}
echo '' >> ${"$APP_BB_FILE"}
echo 'do_install() {' >> ${"$APP_BB_FILE"}
echo '${"    install -d ${D}/${bindir}"}' >> ${"$APP_BB_FILE"}
${ops.StringOps(st"${(apps.map((app: String) => s"echo '    install -m 755 ${"${WORKDIR}"}/build/${formatAppNameToBitbake(app)} ${"${D}${bindir}"}' >> ${"$APP_BB_FILE"}"), "\n")}".render).replaceAllLiterally("\r","")}
echo '}' >> ${"$APP_BB_FILE"}
echo '' >> ${"$APP_BB_FILE"}
echo 'EXTRA_OECMAKE = ""' >> ${"$APP_BB_FILE"}
"""
      }

      @pure def createSystemUserDtsi(): String = {
        // todo best way to select template (context selector function is ideal, but more trouble than its worth for now)
        // TODO should be part of Context? (deciding)
        return Templates.zedboard_petalinux_2020_1_createSystemUserDtsi(hc, tc, ec)
      }

      val hwPath: String = ec.sandbox match {
        case Some(sb) => st"${(sb.workspace.hw, "/")}".render
        case None() => ec.projectContext.projectWorkspace.hw.abs.string
      }
      val osPath: String = ec.sandbox match {
        case Some(sb) => st"${(sb.workspace.os, "/")}".render
        case None() => ec.projectContext.projectWorkspace.os.abs.string
      }
      val swPath: String = ec.sandbox match {
        case Some(sb) => st"${(sb.workspace.sw, "/")}".render
        case None() => ec.projectContext.projectWorkspace.sw.abs.string
      }

      return s"""
rm -rf /tmp/tmp.*
petalinux-util --webtalk off

echo 'PETALINUX-CREATE PROJECT'
petalinux-create --force --type project --template zynq --name ${workspace.os.canon.name}

# Absolute
# cp  $hwPath/${ec.projectContext.template_project_vivado_design}_wrapper.bit $osPath/${ec.projectContext.template_project_vivado_design}_wrapper.bit
# cp  $hwPath/${ec.projectContext.template_project_vivado_design}_wrapper.xsa $osPath/${ec.projectContext.template_project_vivado_design}_wrapper.xsa

# Relative
cp  ${workspace.hw.canon.name}/${ec.projectContext.template_project_vivado_design}_wrapper.bit ${workspace.os.canon.name}/${ec.projectContext.template_project_vivado_design}_wrapper.bit
cp  ${workspace.hw.canon.name}/${ec.projectContext.template_project_vivado_design}_wrapper.xsa ${workspace.os.canon.name}/${ec.projectContext.template_project_vivado_design}_wrapper.xsa

cd ${workspace.os.canon.name}

mkdir -p project-spec/configs

CONFIG_FILE=project-spec/configs/CONFIG.old
CONFIG_FILE_ALT=project-spec/configs/config.old

touch $$CONFIG_FILE

# We can either enable auto-config and let files be auto updated every time we call petalinux-config (top-level).
# or we can disable this and let files be updated by calling petalinux-config -c <target> for each.
#
# Disable autoconfigs prevents accidently overwriting changes throughout the build.
# However we must now manually build with petalinux-config (build?) -c <target> -x finish

echo 'CONFIG_SUBSYSTEM_AUTOCONFIG_DTS=n' >> $$CONFIG_FILE
echo 'CONFIG_SUBSYSTEM_AUTOCONFIG_PMUFW=n' >> $$CONFIG_FILE

# $${ANVIL_PROJECT}/os/project-spec/configs/linux-xlnx/plnx_kernel.cfg
echo 'CONFIG_SUBSYSTEM_AUTOCONFIG_KERNEL=y' >> $$CONFIG_FILE

# $${ANVIL_PROJECT}/os/project-spec/configs/u-boot-xlnx/config:cfg/platform-auto.h
# NOTE: directory config:cfg does NOT need Microblaze-only file "config.mk"
echo 'CONFIG_SUBSYSTEM_AUTOCONFIG_U__BOOT=y' >> $$CONFIG_FILE

# $${ANVIL_PROJECT}/os/components/plnx_workspace/device-tree/device-tree
echo 'CONFIG_SUBSYSTEM_AUTOCONFIG_DEVICE__TREE=y' >> $$CONFIG_FILE

echo 'CONFIG_SUBSYSTEM_HARDWARE_AUTO=y' >> $$CONFIG_FILE
echo 'CONFIG_SUBSYSTEM_DEVICE__TREE=y' >> $$CONFIG_FILE

# FPGA_MANAGER overrides many CONFIG_SUBSYSTEM options, so disable it
echo 'CONFIG_SUBSYSTEM_FPGA_MANAGER=n' >> $$CONFIG_FILE

# These options are overwritten if FPGA_MANAGER is enabled
echo 'CONFIG_SUBSYSTEM_DTB_OVERLAY=y' >> $$CONFIG_FILE
echo 'CONFIG_SUBSYSTEM_REMOVE_PL_DTB=n' >> $$CONFIG_FILE

#  Userspace IO Drivers
echo 'CONFIG_UIO=y' >> $$CONFIG_FILE
echo 'CONFIG_UIO_PDRV_GENIRQ=y' >> $$CONFIG_FILE
# echo 'CONFIG_UIO_DMEM_GENIRQ=y' >> $$CONFIG_FILE

# For offline builds using local feeds
#echo 'CONFIG_YOCTO_BB_NO_NETWORK=y' >> $$CONFIG_FILE
#echo 'CONFIG_YOCTO_LOCAL_SSTATE_FEEDS=y' >> $$CONFIG_FILE
#echo 'CONFIG_YOCTO_NETWORK_SSTATE_FEEDS=n' >> $$CONFIG_FILE
#echo 'CONFIG_YOCTO_LOCAL_SSTATE_FEEDS_URL="file:///home/vagrant/sswreleases/rel-v2020/arm/sstate-cache"' >> $$CONFIG_FILE
#echo 'CONFIG_YOCTO_NETWORK_SSTATE_FEEDS_URL="file:///home/vagrant/sswreleases/rel-v2020/arm/sstate-cache"' >> $$CONFIG_FILE
#echo 'CONFIG_YOCTO_SSTATE_FEEDS_URL="file:///home/vagrant/sswreleases/rel-v2020/arm/sstate-cache"' >> $$CONFIG_FILE
#echo 'CONFIG_PRE_MIRROR_URL="file:///home/vagrant/sswreleases/rel-v2020/downloads"' >> $$CONFIG_FILE

# Expected to be set automatically by petalinux before make (example values)
#export ARCH=arm
#export DEVICE_TREE=zynq-zed
#export CROSS_COMPILE=arm-linux-gnueabihf-

# Manually set bootargs to handle uio driver
echo 'CONFIG_SUBSYSTEM_BOOTARGS_AUTO=n' >> $$CONFIG_FILE
echo 'CONFIG_SUBSYSTEM_BOOTARGS="console=ttyPS0,115200 earlyprintk uio_pdrv_genirq.of_id=\"generic-uio\""' >> $$CONFIG_FILE
echo 'CONFIG_SUBSYSTEM_BOOTARGS_GENERATED="console=ttyPS0,115200 earlyprintk uio_pdrv_genirq.of_id=\"generic-uio\""' >> $$CONFIG_FILE

# Set machine name to "template" (despite not using a BSP for petalinux-config --get-hw-description=...)
echo 'CONFIG_DTG_MACHINE_NAME="template"' >> $$CONFIG_FILE

# Copy CONFIG.old as config.old to ensure non-interactive config across all versions
cp $$CONFIG_FILE $$CONFIG_FILE_ALT

echo 'PETALINUX-CONFIG (HW-DESCRIPTION)'
# Searches for hardware description in top-level folder of petalinux project
petalinux-config --get-hw-description --silentconfig -v || exit 1

mkdir -p images/linux/

echo 'PETALINUX-CONFIG'
petalinux-config --silentconfig -v || exit 1

echo 'PETALINUX-CREATE ANVIL APP'
petalinux-create -t apps -n $appName --enable || exit 1
rm -rf project-spec/meta-user/recipes-apps/$appName/files/*
rm -rf project-spec/meta-user/recipes-apps/$appName/files/.*
# cp -rL $swPath/modified-transpiled/* project-spec/meta-user/recipes-apps/$appName/files
cp -rL ../${workspace.sw.canon.name}/modified-transpiled/* project-spec/meta-user/recipes-apps/$appName/files

${bitbakeTemplateString()}

# create system-user.dtsi
echo 'PETALINUX-CONFIG KERNEL'
petalinux-config -c kernel --silentconfig -v

${createSystemUserDtsi()}

echo 'PETALINUX-CONFIG U-BOOT'
petalinux-config -c u-boot --silentconfig -v

echo 'PETALINUX-CONFIG ROOTFS'
petalinux-config -c rootfs --silentconfig -v

# pre-kernel (but post app)
echo 'PETALINUX-BUILD FINISH anvil app'
petalinux-build -c anvil       -x finish -v || petalinux-build -c anvil        -v
echo 'PETALINUX-BUILD FINISH u-boot-xlnx'
petalinux-build -c u-boot-xlnx -x finish -v || petalinux-build -c u-boot-xlnx  -v
echo 'PETALINUX-BUILD FINISH device-tree'
petalinux-build -c device-tree -x finish -v || petalinux-build -c device-tree  -v
echo 'PETALINUX-BUILD FINISH fsbl'
petalinux-build -c fsbl        -x finish -v || petalinux-build -c fsbl         -v
echo 'PETALINUX-BUILD FINISH linux-xlnx'
petalinux-build -c linux-xlnx  -x finish -v || petalinux-build -c linux-xlnx   -v
echo 'PETALINUX-BUILD FINISH kernel'
petalinux-build -c kernel      -x finish -v || petalinux-build -c kernel       -v
echo 'PETALINUX-BUILD FINISH u-boot'
petalinux-build -c u-boot      -x finish -v || petalinux-build -c u-boot       -v
echo 'PETALINUX-BUILD FINISH rootfs'
petalinux-build -c rootfs      -x finish -v || petalinux-build -c rootfs       -v
echo 'PETALINUX-BUILD'
petalinux-build -v

echo 'PETALINUX-PACKAGE'
petalinux-package --boot --fsbl images/linux/zynq_fsbl.elf --fpga images/linux/system.bit --u-boot
"""
    }

    // write petalinux script

    Workspace.writeOverScript(workspace.project / plScriptFilename, createPetalinuxScript())
    ec.sandbox match {
      case Some(sb) => {
        // clear dirs
        sb.clearDirectory(sb.workspace.os)

        // push
        sb.push(workspace.project / plScriptFilename, sb.workspace.project :+ plScriptFilename)

        // run petalinux
        val absPath = st"${(sb.workspace.project :+ plScriptFilename, "/")}".render
        sb.ssh(ISZ(absPath), F, T)

        // pull (images only)
        sb.pull(Workspace.mkdir(workspace.os / "images"), sb.workspace.os :+ "images") // way to big to pull the whole thing
      }
      case _ => runProc(workspace.project, ISZ("/bin/bash", "-c", plScriptFilename))
    }

    return z"0"
  }

  object AnvilDriverParser {

    @enum object Direction {
      'In
      'Out
      'InOut
    }

    @datatype class Arg(name: String, tipe: String, kind: Direction.Type, isArray: B, rawFunctionName: String) {
      // empty body
    }

    // uses the generatedDrivers create a mapping of ArgName -> ArgType
    def readTypes(driverName: String, driverHeader: Os.Path): ISZ[Arg] = {

      // TODO technically contextual... but how to add to Context without leaking the impl(s)? Include xml reader too
      val prefix: org.sireum.String = s"X${StringOps(driverName).firstToUpper}_"
      val matchWords: ISZOps[String] = ISZOps(ISZ(s" ${prefix}Get_", s" ${prefix}Set_", s" ${prefix}Write_", s" ${prefix}Read_"))
      val skipWords: ISZOps[String] = ISZOps(ISZ("BaseAddress", "HighAddress", "TotalAddress", "BitWidth", "Depth"))
      var result: ISZ[Arg] = ISZ[Arg]()

      val filteredLines = driverHeader.readLines
        // retain only driver arg functions
        .filter((line: String) => matchWords.exists((matcher: String) => StringOps(line).contains(matcher)))
        // discard all driver arg helper functions
        .filter((line: String) => !skipWords.exists((matcher: String) => StringOps(line).contains(matcher)))

      @pure def splitThenTrim(c: C, s: String): ISZ[String] = {
        return StringOps(s).split((cc: C) => cc == c).map((ss: String) => StringOps(ss).trim)
      }

      @pure def getPortName(signature: String, qualifiedPrefix: String, portOpQualifier: String): String = {

        @pure def trailIfMissing(s: String, trail: String): String = {
          if (StringOps(s).endsWith(trail)) {
            return s
          } else {
            return st"$s$trail".render
          }
        }

        val actualPrefix = trailIfMissing(s"$qualifiedPrefix$portOpQualifier", "_")
        val endIndexExclusive = StringOps(signature).indexOf(c"(")
        val beginIndexInclusive = StringOps(signature).stringIndexOf(actualPrefix) + actualPrefix.size
        return StringOps(signature).substring(beginIndexInclusive, endIndexExclusive)
      }

      for (line <- filteredLines) {
        val fnName = StringOps(StringOps(line).substring(splitThenTrim(c" ", line)(z"0").size, splitThenTrim(c"(", line)(z"0").size)).trim
        val argDirectionName: String = StringOps(StringOps(fnName).substring(prefix.size, StringOps(fnName).indexOfFrom(c"_", prefix.size))).trim
        val argName: String = getPortName(line, prefix, argDirectionName)
        val dir: Direction.Type = argDirectionName match {
          case string"Get" => Direction.Out
          case string"Read" => Direction.Out
          case string"Set" => Direction.In
          case string"Write" => Direction.In
          case _ => error(s"Unable to determine if $argDirectionName's direction from: $argDirectionName", Direction.InOut)
        }
        val isArray: B = argDirectionName match {
          case string"Get" => F
          case string"Set" => F
          case string"Read" => T
          case string"Write" => T
          case _ => error(s"Unable to determine if $argDirectionName is an array or value from: $dir", T)
        }
        val argType: org.sireum.String = isArray match {
          case T => string"char *data"
          case F => {
            val space: C = c" "
            val words = StringOps(line).split((c: C) => c  == space)
            dir match {
              case Direction.In => words(words.lastIndex.decrease)
              case Direction.Out => words(z"0")
              case Direction.InOut => error("InOut dir is determined later", "unused")
            }
          }
        }

        @strictpure def checkArgName(arg: Arg): B = arg.name == argName

        @strictpure def argNameMatcher(o: Option[Arg], arg: Arg): Option[Arg] = if (checkArgName(arg)) Some(arg) else o

        if (ISZOps(result).exists(checkArgName _)) {
          val matchingArg: Option[Arg] = ISZOps(result).foldLeft[Option[Arg]](argNameMatcher _, None())
          matchingArg match {
            // - Remove the old matching arg (expected to contain either Direction.In or Direction.Out) in preparation
            //   for replacing its direction with Direction.InOut instead.
            // - This assumption is safe because only args containing Direction.InOut may have duplicate occurrences.
            // TODO Still, consider adding a sanity check that both arg directions are opposite neither are InOut such as:
            //      (arg.direction is In|Out) AND (match.direction is In|Out) AND (arg.direction is NOT match.direction)
            case Some(matchArg) => result = result - matchArg // remove the old matching arg (which should be In r, we will add InOut instead... // todo check that this dir is opposite of match?
            case None() => error("A matching Arg was expected based on if-statement above.", unit())
          }
          result = result :+ Arg(argName, argType, Direction.InOut, isArray, fnName)
        } else {
          result = result :+ Arg(argName, argType, dir, isArray, fnName)
        }
      }

      return result
    }

  }

}
