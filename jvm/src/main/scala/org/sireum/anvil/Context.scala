// #Sireum

package org.sireum.anvil

import org.sireum._
import org.sireum.ops.StringOps

/**
* Contains all contextual values (values determined at runtime after parsing but before stage execution) and operations
* used in Anvil.
*
* sandbox mode
* └── SandboxInstallationContext -------------- // A limited context used to create sandboxes. Allows full access to
*                                                  installer workspace.
* compile mode
* ├── ToolchainContext ------------------------ // Conventions, defaults, and assumptions about Xilinx tools.
* │                                                For example: output file formats, version numbers, executables, etc.
* ├── HardwareContext ------------------------- // Constants and derived values that vary by target hardware.
* │                                                For example: part_number, address_layouts, etc.
* └── ExecutionContext ------------------------ // Contains values that vary per-execution.
*     │                                            Such as arguments passed by the user or means to determine which
*     │                                            stages have already been run.
*     ├── ProjectContext ---------------------- // Names, variables, and settings which may vary between projects but
*     │                                            not stages. E.g. "bus name" "solution name" "top function" etc.
*     └── Option[SandboxCompilationContext] --- // Optional context present when Anvil's compiler is passed a sandbox
*         │                                        build delegate.
*         ├── None ---------------------------- // Indicates the "--sandbox /path/to/sandbox" flag was unused.
*         └── Some[SandboxCompilationContext] - // Indicates usage of "--sandbox /path/to/sandbox" flag.
*             └── SandboxCompilationContext --- // Provides operations to enable sandbox build delegation.
*                                                  Push, pull, clean, ssh, etc. Basically the sandbox controller.
*/
object Context {

  @sig trait SandboxContext {
    def port: String // ssh port
    def hostname: String
    def username: String
    def password: String

    /*
     * Run vagrant up with flags appropriate for the given context.
     *
     * For example: calling up() during install *may* allow for provisions, while calling up() during sandbox proxy
     *              build *may* only resume a halted machine.
     */
    def up(): Os.Proc.Result

    def localSandboxProc(proc: ISZ[String]): Os.Proc.Result

    /**
     * Absolute path.
     * For example: represent Os.path("/Users/joe/Desktop") becomes ISZ("", "Users", "joe", "Desktop")
     */
    def installationPath: ISZ[String] = {
      return ISZ("", "opt", "pkg")
    }

    def vivadoVersion: String

    def vivadoPath: ISZ[String] = {
      return installationPath :+ "vivado"
    }

    def petalinuxPath: ISZ[String] = {
      return installationPath :+ "petalinux"
    }

    def sireumPath: ISZ[String] = {
      return installationPath :+ "sireum"
    }

    /*
     * Location of petalinux source script relative to the installation folder.
     */
    def petalinuxSourceScriptPath: ISZ[String]

    /*
     * Location of vivado source script relative to the installation folder.
     */
    def vivadoSourceScriptPath: ISZ[String]

    /*
     * List of dependencies required by petalinux via apt-get.
     * These are available in the user guide for each individual petalinux version.
     */
    def petalinuxDependencies: ISZ[String]
  }

  @sig trait SandboxInstallationContext extends SandboxContext {

    def workspace: InstallerWorkspace

    def installSireum: B

    def petalinuxInstallerPath: Option[Os.Path]

    def xilinxUnifiedPath: Option[Os.Path]

    def vmName(): String

    def numCPUs(): String

    def vramSize(): String

    def memorySizeMB(): String

    def enableGUI(): String

    def disksize(): String

    def graphicsController(): String

    override def localSandboxProc(proc: ISZ[String]): Os.Proc.Result = {
      return runProc(workspace.root, proc)
    }

    def up(): Os.Proc.Result = {
      return localSandboxProc(ISZ("vagrant", "up"))
    }
  }

  @sig trait HardwareContext {

    def template_project_part_number: String

    def template_project_bus: String = {
      return "AXILiteS"
    }

  }

  @sig trait ToolchainContext {

    // all functions which accept the entire workspace to be as flexible as possible for different tool versions
    def driverName(hc: HardwareContext, ec: ExecutionContext): String
    def driverBaseFileName(hc: HardwareContext, ec: ExecutionContext): String
    def versionedDriverName(hc: HardwareContext, ec: ExecutionContext): String
    def hlsDriverImplDirectory(hc: HardwareContext, ec: ExecutionContext): Os.Path

    def baseDriverHFileName(hc: HardwareContext, ec: ExecutionContext): String
    def baseDriverCFileName(hc: HardwareContext, ec: ExecutionContext): String
    def hwDriverHFileName(hc: HardwareContext, ec: ExecutionContext): String
    def linuxDriverCFileName(hc: HardwareContext, ec: ExecutionContext): String

    // given a line of source code from a driver file, return zero to many lines to replace it
    // note: driver source is intercepted in SW stage. Vivado HLS project files are never modified (to respect caches)
    def applyDriverSourceCodeLineHooks(hc: HardwareContext, ec: ExecutionContext, driverFileName: String, sourceLine: String): ISZ[String]

    // todo consider adding helper method "isValidNamingConvention" to check user input against Xilinx tools
  }

  /**
  * Configured for the following toolchain:
  *   - Vivado Design Suite v2020.1
  *   - Petalinux v2020.1
  */
  @datatype class DefaultToolchainContext() extends ToolchainContext {

    override def driverName(hc: HardwareContext, ec: ExecutionContext): String = {
      return ec.projectContext.template_project_top_function
    }

    override def driverBaseFileName(hc: HardwareContext, ec: ExecutionContext): String = {
      return StringOps(driverName(hc, ec)).toLower
    }

    override def versionedDriverName(hc: HardwareContext, ec: ExecutionContext): String = {
      return st"${driverName(hc, ec)}_v1_0".render
    }

    override def hlsDriverImplDirectory(hc: HardwareContext, ec: ExecutionContext): Os.Path = {
      val driverDirectory: String = versionedDriverName(hc, ec)
      val hlsSolutionName = ec.projectContext.template_project_hls_solution
      val projectWorkspace = ec.projectContext.projectWorkspace
      return projectWorkspace.hls / hlsSolutionName / "impl" / "misc" / "drivers" / driverDirectory / "src";
    }

    override def baseDriverHFileName(hc: HardwareContext, ec: ExecutionContext): String = {
      val baseName = driverBaseFileName(hc, ec)
      return s"x$baseName.h"
    }

    override def baseDriverCFileName(hc: HardwareContext, ec: ExecutionContext): String = {
      val baseName = driverBaseFileName(hc, ec)
      return s"x$baseName.c"
    }

    override def hwDriverHFileName(hc: HardwareContext, ec: ExecutionContext): String = {
      val baseName = driverBaseFileName(hc, ec)
      return s"x${baseName}_hw.h"
    }

    override def linuxDriverCFileName(hc: HardwareContext, ec: ExecutionContext): String = {
      val baseName = driverBaseFileName(hc, ec)
      return s"x${baseName}_linux.c"
    }

    override def applyDriverSourceCodeLineHooks(hc: HardwareContext, ec: ExecutionContext, driverFileName: String, sourceLine: String): ISZ[String] = {
      val dh = baseDriverHFileName(hc, ec) // for intercepting typedefs in driver header file
      if (driverFileName == dh) {
        val sl = StringOps(sourceLine).trim
        sl match {
          case "typedef uint32_t u32;" => return ISZ(sl, "typedef uint64_t u64;") // add u64 // todo also add F64?
          case _ => return ISZ(sourceLine) // do not modify (pass through)
        }
      }
      return ISZ(sourceLine) // do not modify (pass through)
    }

  }

  @sig trait ProjectContext {
    def projectWorkspace: ProjectWorkspace
    def transpilerArgs: TranspilersCOptionMirror
    def methodDescriptor: ISZ[String]
    def methodDriverProxyPrefix: String
    def simpleMethodName: String
    def mangledMethodName: String
    def template_project_top_function: String
    def template_project_hls_solution: String
    def template_project_vivado_project: String
    def template_project_vivado_design: String
    def template_project_hls_sources: String
  }

  @enum object CompileStage {
    'Hls
    'Hw
    'Sw
    'Os
  }

  // mirror of Cli.SireumSlangTranspilersCAnvilExecutionPass
  @enum object TranspilersCAnvilExecutionPassMirror {
    'None
    'First
    'Second
  }

  // mirror of Cli.SireumSlangTranspilersCOption
  @datatype class TranspilersCOptionMirror(
                                          val help: String,
                                          val args: ISZ[String],
                                          val sourcepath: ISZ[String],
                                          val strictAliasing: B,
                                          val output: Option[String],
                                          val verbose: B,
                                          val apps: ISZ[String],
                                          val bitWidth: Z,
                                          val projectName: Option[String],
                                          val stackSize: Option[String],
                                          val customArraySizes: ISZ[String],
                                          val maxArraySize: Z,
                                          val maxStringSize: Z,
                                          val cmakeIncludes: ISZ[String],
                                          val exts: ISZ[String],
                                          val libOnly: B,
                                          val excludeBuild: ISZ[String],
                                          val plugins: ISZ[String],
                                          val fingerprint: Z,
                                          val stableTypeId: B,
                                          val unroll: B,
                                          val save: Option[String],
                                          val load: Option[String],
                                          val customConstants: ISZ[String],
                                          val forwarding: ISZ[String],
                                          val anvilTranspilerPass: TranspilersCAnvilExecutionPassMirror.Type,
                                          val anvilTranspilerContext: ISZ[String]
                                        )

  @sig trait ExecutionContext {
    def projectContext: ProjectContext
    def sandbox: Option[SandboxCompilationContext]
    def stages: Set[CompileStage.Type]
  }

  @enum object ScpDirection {
    'LocalToSandbox
    'SandboxToLocal
  }

  def runProc(path: Os.Path, proc: ISZ[String]): Os.Proc.Result = {
    val prefix: ISZ[String] = if (Os.kind == Os.Kind.Win) ISZ("cmd", "/c") else ISZ[String]()
    return Os.proc(prefix ++ proc).at(path).console.runCheck()
  }

  // todo move to Utils file?
  def expect(requirement: B, message: ST): Unit = {
    if (!requirement) {
      val rendered = message.render
      eprintln(rendered)
      halt(rendered)
    }
  }

  def error[T](msg: String, unused: T): T = {
    eprintln(msg)
    Os.exit(z"-1")
    return unused
  }

  @pure def unit(): Unit = {
    // no op
  }

  @pure def contains[T](xs: ISZ[T], x: T): B = {
    return set(xs).contains(x)
  }

  @pure def set[T](xs: ISZ[T]): Set[T] = {
    return Set.empty[T] ++ xs
  }


  @sig trait SandboxCompilationContext extends SandboxContext {

    def workspace: SandboxWorkspace

    override def localSandboxProc(proc: ISZ[String]): Os.Proc.Result = {
      return runProc(workspace.local, proc)
    }

    def up(): Os.Proc.Result = {
      return localSandboxProc(ISZ("vagrant", "up", "--no-provision"))
    }

    def ssh(proc: ISZ[String], vivadoEnv: B, petalinuxEnv: B): Os.Proc.Result = {
      // prepare commands
      val cd_and: ISZ[String] = ISZ("cd", st"${(workspace.project, "/")}".render, "&&")
      val venv_and_opt_and: ISZ[String] = if (vivadoEnv) ISZ("source", st"${(vivadoSourceScriptPath, "/")}".render, "||", "true", "&&") else ISZ()
      val penv_and_opt_and: ISZ[String] = if (petalinuxEnv) ISZ("source", st"${(petalinuxSourceScriptPath, "/")}".render, "||", "true", "&&") else ISZ()

      // order of "venv", "penv", and "cd" do not technically matter, but ordering "cd" last is a measure against
      // unintended directory overrides from smuggled in with "venv" / "penv"
      val modifiedProc: ISZ[String] = ISZ(
        string"/usr/bin/env",
        string"-i",
        st"""TERM='"linux"'""".render,
        st"""SHELL='"/bin/bash"'""".render,
        st"""USER='"$$USER"'""".render,
        st"""PWD='"$$PWD"'""".render,
        st"""LANG='"$$LANG"'""".render,
        st"""HOME='"$$HOME"'""".render,
        st"""SHLVL='"$$SHLVL"'""".render,
        st"""DISPLAY='"$$DISPLAY"'""".render,
        st"""LOGNAME='"$$LOGNAME"'""".render,
        st"PROJECT_HOME='\"${(workspace.project, "/")}\"'".render,
        st"SIREUM_HOME='\"${(sireumPath, "/")}/kekinian\"'".render,
        st"VIVADO_HOME='\"${(ops.ISZOps(vivadoSourceScriptPath).dropRight(z"1"), "/")}\"'".render,
        st"VITIS_HOME='\"${(ops.ISZOps(vivadoSourceScriptPath).dropRight(z"1"), "/")}\"'".render,
        st"PETALINUX_HOME='\"${(petalinuxPath, "/")}\"'".render,
        string"/bin/bash",
        string"-v",
        string"-c",
        st"'${(cd_and ++ venv_and_opt_and ++ cd_and ++ penv_and_opt_and ++ cd_and ++ proc, " ")}'".render
      )

      if (contains(petalinuxDependencies, string"xterm")) {
        return localSandboxProc(ISZ("vagrant", "ssh", "-c", st"TERM=xterm /bin/bash -v -c \"${(modifiedProc, " ")}\"".render))
      } else {
        return localSandboxProc(ISZ("vagrant", "ssh", "-c", st"/bin/bash -v -c \"${(modifiedProc, " ")}\"".render))
      }
    }

    def scp(dir: ScpDirection.Type, localPath: Os.Path, remotePath: ISZ[String]): Os.Proc.Result = {
      assert(localPath.exists)
      assert(remotePath.nonEmpty)

      // Prepare an empty destination folder for copying a directory with scp.
      if (localPath.isDir) {
        dir match {
          case ScpDirection.LocalToSandbox => {
            clearDirectory(remotePath)
          }
          case ScpDirection.SandboxToLocal => {
            localPath.removeAll()
            localPath.mkdirAll()
          }
        }
      }

      val tool: ISZ[String] = ISZ("scp")
      val fileFlag: ISZ[String] = if (localPath.isDir) ISZ("-r") else ISZ()
      val nonStrictHostKeyCheckingFlag: ISZ[String] = ISZ("-o", "StrictHostKeyChecking=no")
      val portFlag: ISZ[String] = ISZ("-P", port)

      val files: ISZ[String] = dir match {
        case ScpDirection.LocalToSandbox => {
          val local = localPath.canon.abs.string
          val remoteParent = st"$username@127.0.0.1:${(ops.ISZOps(remotePath).dropRight(z"1"), "/")}".render
          ISZ(local, remoteParent)
        }
        case ScpDirection.SandboxToLocal => {
          val localParent = localPath.up.canon.abs.string
          val remote = st"$username@127.0.0.1:${(remotePath, "/")}".render
          ISZ(remote, localParent)
        }
      }
      return localSandboxProc(tool ++ fileFlag ++ nonStrictHostKeyCheckingFlag ++ portFlag ++ files)
    }

    def upload(localPath: Os.Path, remotePath: ISZ[String]): Os.Proc.Result = {
      val source: String = localPath.canon.string
      val destination: String = st"${(for (file <- remotePath) yield st"$file", "/")}".render
      return localSandboxProc(ISZ(st"vagrant upload $source $destination".render))
    }

    def clearDirectory(remotePath: ISZ[String]): Os.Proc.Result = {
      // TODO current implementation does not clear files/dirs being used by another app (e.g. opened in vivado hls)
      {
        assert(remotePath.size >= workspace.project.size)
        var pathEscapeCounter = z"0"
        for (i <- z"0" until remotePath.size) {
          if (i < workspace.project.size) {
            assert(remotePath(i) == workspace.project(i))
          }
          remotePath(i) match {
            case "" => assert(i == z"0")
            case "." => assert(i != z"0")
            case ".." => pathEscapeCounter = pathEscapeCounter - z"1"
            case _ => pathEscapeCounter = pathEscapeCounter + z"1"
          }
          assert(pathEscapeCounter >= z"0")
        }
      }

      val path: String = st"${(remotePath, "/")}".render
      val rm: ISZ[String] = ISZ("rm", "-rf", path, "||", "true")
      val and: ISZ[String] = ISZ("&&")
      val mkdir: ISZ[String] = ISZ("mkdir", "-p", path, "||", "true")
      return ssh(mkdir ++ and ++ rm ++ and ++ mkdir, F, F)
    }

    /*
     * Upload a local file (or directory) into the remote sandbox.
     *   - File uploads overwrite existing sandbox files.
     *   - Directory uploads are recursive.
     */
    def push(localPath: Os.Path, remotePath: ISZ[String]): Os.Proc.Result = {
      return scp(ScpDirection.LocalToSandbox, localPath, remotePath)
    }

    /*
     * Download a remote sandbox file (or directory) into the local filesystem.
     *   - File downloads overwrite existing local files.
     *   - Directory downloads are recursive.
     */
    def pull(localPath: Os.Path, remotePath: ISZ[String]): Os.Proc.Result = {
      return scp(ScpDirection.SandboxToLocal, localPath, remotePath)
    }
  }

  //
  // Built-in convenience contexts
  //

  @datatype class HardwareContext_Zynq_7000_SoC_ZedBoard() extends HardwareContext {
    // xc7z020clg484-1
    val template_project_part_number: String = {
      val zedFamily = "xc7z020"
      val zedPackage = "clg484"
      st"$zedFamily$zedPackage-1".render
    }
  }

  @datatype class SimpleProjectContext(val projectWorkspace: ProjectWorkspace,
                                       val methodDescriptor: ISZ[String], // e.g. ISZ("org", "sireum", "Math", "add")
                                       val simpleMethodName: String,      // e.g. "add"
                                       val mangledMethodName: String,     // e.g. "org_sireum_Math_add"
                                                                          // see: "org.sireum.lang.ast.Util.mangleName"
                                       val transpilerArgs: TranspilersCOptionMirror) extends ProjectContext {
//    val methodDriverProxyPrefix: String = string"ANVIL_X"
    val methodDriverProxyPrefix: String = string"" // TODO empty string is a hack to remove method call proxy. Remove?
    val template_project_top_function: String = mangledMethodName
    val template_project_hls_solution: String = "generatedSolution"
    val template_project_vivado_project: String = "generatedProject"
    val template_project_vivado_design: String = "generatedDesign"
    val template_project_hls_sources: String = mangledMethodName
  }

  @sig trait SimpleSSH extends SandboxContext {

    override def port: String = {
      return "2222"
    }

    override def hostname: String = {
      return "anvil"
    }

    override def username: String = {
      return "vagrant"
    }

    override def password: String = {
      return "vagrant"
    }
  }

  @sig trait SimpleInstall extends SandboxInstallationContext {

    override def vmName(): String = {
      return "anvil"
    }

    override def numCPUs(): String = {
      return "12" // (server config)
    }

    override def vramSize(): String = {
      return "48" // (server config)
    }

    override def memorySizeMB(): String = {
      return "49152" // (server config)
    }

    override def enableGUI(): String = {
      return "false" // (server config)
    }

    override def graphicsController(): String = {
      // apparently vmsvga is standard but "accelerate3d" must be set to "off"
      return "vmsvga" // (server config)
    }

    override def disksize(): String = {
      val installPetalinux: B = petalinuxInstallerPath.nonEmpty
      val installXilinx: B = xilinxUnifiedPath.nonEmpty
      val toolsBOM: (B, B, B) = (installSireum, installPetalinux, installXilinx)


      val gb: Z = z"512" // (server config) (intended for multiproject sandbox)
      return st"${gb}GB".render

      /*
       * too confusing for now
       *
      // default extremely rough estimates. Should be part of config
      val gb: Z = toolsBOM match {
        // (isSireum isPetalinux isXilinx) <---- tuple of 3 booleans matching
        case (F, F, F) => z"64"  // CASE #1: environment + dependencies, but no tools preinstalled. sUse little and let users adjust if needed.
        case (F, F, T) => z"128" // CASE #2: big with huge installer
        case (F, T, F) => z"128" // CASE #3: smaller with potentially huge sstate cache
        case (F, T, T) => z"256" // CASE #4: (too small?) big installer + sstate + apps. Can probably lower if run then delete installer before petalinux install.
        case (T, F, F) => z"64"  // CASE #5: sireum tools don't require too much memory, but hint that development may occur on the box.
        case (T, F, T) => z"128" // CASE #6:
        case (T, T, F) => z"128" // CASE #7:
        case (T, T, T) => z"256" // CASE #8: (too small?)
      }
      return st"${gb}GB".render
      */
    }
  }

  @sig trait Petalinux_v2020_1 extends SandboxContext {

    override def petalinuxSourceScriptPath: ISZ[String] = {
      return petalinuxPath :+ "settings.sh"
    }

    /*
     * Derived from UG1144 (v2020.1), "Petalinux Tools Documentation", Table 2: Packages and Linux Workstation Environments
     * https://www.xilinx.com/support/documentation/sw_manuals/xilinx2020_1/ug1144-petalinux-tools-reference-guide.pdf#unique_26
     */
    override def petalinuxDependencies: ISZ[String] = {
      val official: ISZ[String] = ISZ[String](
        "iproute2", "gcc", "g++", "net-tools", "libncurses5-dev", "zlib1g:i386", "libssl-dev", "flex", "bison",
        "libselinux1", "xterm", "autoconf", "libtool", "texinfo", "zlib1g-dev", "gcc-multilib", "build-essential",
        "screen", "pax", "gawk", "python3", "python3-pexpect", "python3-pip", "python3-git", "python3-jinja2",
        "xz-utils", "debianutils", "iputils-ping", "libegl1-mesa", "libsdl1.2-dev", "pylint3", "cpio"
      )

      // val gui = ISZ[String]("xfce4", "gnome-terminal")

      // launch gui by running 'startx' inside guest. (otherwise headless)
      // return gui ++ official
      return official
    }
  }

  @sig trait XilinxUnified_v2020_1 extends SandboxContext {
    override def vivadoVersion: String = {
      return "2020.1"
    }

    override def vivadoSourceScriptPath: ISZ[String] = {
      return vivadoPath ++ ISZ("Vivado", vivadoVersion, "settings64.sh")
    }
  }

  @datatype class SimpleSandboxCompilationContext(val workspace: SandboxWorkspace)
    extends SandboxCompilationContext
    with Petalinux_v2020_1
    with XilinxUnified_v2020_1
    with SimpleSSH {}

  @datatype class SimpleExecutionContext(val projectContext: ProjectContext,
                                         val sandbox: Option[SandboxCompilationContext],
                                         val stages: Set[CompileStage.Type]) extends ExecutionContext {}

  @datatype class SimpleSandboxInstallationContext_v2020_1(val workspace: InstallerWorkspace,
                                                           val installSireum: B,
                                                           val petalinuxInstallerPath: Option[Os.Path],
                                                           val xilinxUnifiedPath: Option[Os.Path])
    extends SandboxInstallationContext
      with SimpleSSH
      with SimpleInstall
      with XilinxUnified_v2020_1
      with Petalinux_v2020_1 {}
}

