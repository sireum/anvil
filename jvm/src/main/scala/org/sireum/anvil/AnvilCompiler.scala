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

    def invokeTranspilerPass1(): Z = {
      val unmodified: TranspilersCOptionMirror = ec.projectContext.transpilerArgs
      // todo check if excludeBuild needed still
      val excludeBuild: ISZ[String] = unmodified.excludeBuild ++ unmodified.apps

      val modified = TranspilersCOptionMirror(
        help = unmodified.help,
        args = unmodified.args,
        sourcepath = unmodified.sourcepath,
        strictAliasing = unmodified.strictAliasing,
        output = Some(ws().transpiled.abs.string), // <-- changed! (was output = o.output)
        verbose = unmodified.verbose,
        apps = unmodified.apps, // we can avoid copying these later because app names are exact aliases
        bitWidth = unmodified.bitWidth,
        projectName = unmodified.projectName,
        stackSize = unmodified.stackSize,
        customArraySizes = unmodified.customArraySizes, // this is also called "sequence size"
        maxArraySize = unmodified.maxArraySize,
        maxStringSize = unmodified.maxStringSize,
        cmakeIncludes = unmodified.cmakeIncludes,
        exts = unmodified.exts, // prevents ext files from being written
        libOnly = unmodified.libOnly,
        excludeBuild = unmodified.excludeBuild,//unmodified.excludeBuild,
        plugins = unmodified.plugins,
        fingerprint = unmodified.fingerprint,
        stableTypeId = unmodified.stableTypeId,
        unroll = unmodified.unroll,
        save = unmodified.save,
        load = unmodified.load,
        customConstants = unmodified.customConstants,
        forwarding = unmodified.forwarding,
        anvilTranspilerPass = TranspilersCAnvilExecutionPassMirror.First, // changed
        anvilTranspilerContext = unmodified.anvilTranspilerContext
      )

      // todo modify c transpiler call to accept extra c-make-includes when creating blank driver files
      return tm(modified) // invoke the CTranspiler
    }

    def invokeTranspilerPass2(): Z = {
      val unmodified: TranspilersCOptionMirror = ec.projectContext.transpilerArgs
      val driverExts: ISZ[String] = ws().driverCalls.list.map((p: Os.Path) => p.value)

      val modified = TranspilersCOptionMirror(
        help = unmodified.help,
        args = unmodified.args,
        sourcepath = unmodified.sourcepath,
        strictAliasing = unmodified.strictAliasing,
        output = Some(ws().modifiedTranspiled.abs.string), // <-- changed! (was output = o.output)
        verbose = unmodified.verbose,
        apps = unmodified.apps, // we can avoid copying these later because app names are exact aliases
        bitWidth = unmodified.bitWidth,
        projectName = unmodified.projectName,
        stackSize = unmodified.stackSize,
        customArraySizes = unmodified.customArraySizes, // this is also called "sequence size"
        maxArraySize = unmodified.maxArraySize,
        maxStringSize = unmodified.maxStringSize,
        cmakeIncludes = unmodified.cmakeIncludes,
        exts = unmodified.exts ++ driverExts, // prevents ext files from being written
        libOnly = unmodified.libOnly,
        excludeBuild = unmodified.excludeBuild,//unmodified.excludeBuild,
        plugins = unmodified.plugins,
        fingerprint = unmodified.fingerprint,
        stableTypeId = unmodified.stableTypeId,
        unroll = unmodified.unroll,
        save = unmodified.save,
        load = unmodified.load,
        customConstants = unmodified.customConstants,
        forwarding = unmodified.forwarding,
        anvilTranspilerPass = TranspilersCAnvilExecutionPassMirror.Second, // changed
        anvilTranspilerContext = unmodified.anvilTranspilerContext
      )

      return tm(modified) // invoke the CTranspiler
    }

    var status: Z = z"0"
    checkpoint()

    def copySources(): Z = {
      val sp = ec.projectContext.transpilerArgs.sourcepath
      val p = Os.path(st"${(sp, "/")}".render)
      p.copyOverTo(ws().original)
      ec.sandbox match {
        case Some(sb) => sb.clearDirectory(sb.workspace.original)
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

      status = invokeTranspilerPass1()
      if (status != z"0") {
        return status
      }
      checkpoint()

      assert(ws().transpiled.list.nonEmpty, "Transpiler should have generated some output")

      // run Anvil's HLS stage to generate the function IP and driver files
      val hls = halt("COMPILER LINK (AnvilStageHLS)") // anvil.AnvilStageHLS(context, workspace, transpilerContext)
//      status = hls.run()
      if (status != z"0") {
        return status
      }
      checkpoint()
    }

    if (shouldRunStage(CompileStage.Hw)) {
      // run Anvil's HW stage to place the IP into the overall block design, then generate a hardware bitstream file
      val hw = halt("COMPILER LINK (AnvilStageHW)") // anvil.AnvilStageHW(context, workspace)
//      status = hw.run()
      if (status != z"0") {
        return status
      }
      checkpoint()
    }

    if (shouldRunStage(CompileStage.Sw)) {
      // run Anvil's SW stage to: generate code to call the drivers created in the HLS stage.
      println("HERE 2!")
      val sw = halt("COMPILER LINK (AnvilStageSW)") // anvil.AnvilStageSW(context, workspace)
//      status = sw.run()
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
      val os = halt("COMPILER LINK (AnvilStageOS)") // anvil.AnvilStageOS(context, workspace)
//      status = os.run()
      if (status != z"0") {
        return status
      }
      checkpoint()
    }
    checkpoint()

    return z"0"
  }

}


