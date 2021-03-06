// #Sireum

package org.sireum.anvil

import org.sireum._
import org.sireum.anvil.Workspace.{file, mkdir}

object Workspace {

  def file(path: Os.Path): Os.Path = {
    assert(if (path.exists) path.isFile else T)
    return path
  }

  def mkdir(path: Os.Path): Os.Path = {
    if (path.exists) {
      assert(path.isDir)
    } else {
      path.mkdirAll()
    }
    return path
  }

  def writeOver(path: Os.Path, content: String): Os.Path = {
    if (path.exists) {
      assert(path.isFile)
    } else {
      path.writeOver(content)
    }
    return path
  }

  def writeOverScript(path: Os.Path, content: String): Os.Path = {
    val file = writeOver(path, content)
    file.chmod("+x")
    return file
  }

}

/*
 * ProjectWorkspace
 * └── root (Os.Path)
 *     └── project
 *         ├── hls
 *         ├── hw
 *         ├── os
 *         └── sw
 *             ├── original
 *             ├── driver-calls
 *             ├── transpiled
 *             └── modified-transpiled
 */
@datatype class ProjectWorkspace(val root: Os.Path) {
  val project:            Os.Path = mkdir(root / "project")
  val hls:                Os.Path = mkdir(project / "hls")
  val hw:                 Os.Path = mkdir(project / "hw")
  val sw:                 Os.Path = mkdir(project / "sw")
  val original:           Os.Path = mkdir(sw / "original") // original (slang) sources before transpiling
  val driverCalls:        Os.Path = mkdir(sw / "driver-calls")
  val transpiled:         Os.Path = mkdir(sw / "transpiled") // result of transpiling, needed for HLS to create drivers.
  val modifiedTranspiled: Os.Path = mkdir(sw / "modified-transpiled")
  val os:                 Os.Path = mkdir(project / "os")
}

/*
 * InstallerWorkspace
 * └── root (Os.Path)
 *     ├── downloads
 *     └── provision
 *         └── scripts
 *             └── fix_dash.sh
 *                 ├── install_petalinux.sh
 *                 ├── install_vivado.sh
 *                 ├── install_dependencies.sh
 *                 └── install_kekinian.sh
 */
@datatype class InstallerWorkspace(val root: Os.Path) {
  val provision:                 Os.Path = mkdir(root / "provision")
  val downloads:                 Os.Path = mkdir(root / "downloads")
  val scripts:                   Os.Path = mkdir(provision / "scripts")
  val fixDashScript:             Os.Path = file(scripts / "fix_dash.sh")
  val installPetalinuxScript:    Os.Path = file(scripts / "install_petalinux.sh")
  val installVivadoScript:       Os.Path = file(scripts / "install_vivado.sh")
  val installDependenciesScript: Os.Path = file(scripts / "install_dependencies.sh")
  val installSireumScript:       Os.Path = file(scripts / "install_kekinian.sh")
}

/*
 * SandboxWorkspace
 * ├── local (Os.Path)
 * │   └── path
 * │       └── to
 * │           └── sandbox
 * └── root (ISZ[String])   // string representation of (absolute) workspace paths in the sandbox
 *     └── home
 *         └── vagrant
 *             └── project
 *                 ├── hls
 *                 ├── hw
 *                 ├── os
 *                 └── sw
 *                     ├── original
 *                     ├── driver-calls
 *                     ├── transpiled
 *                     └── modified-transpiled
 */
@datatype class SandboxWorkspace(val local: Os.Path) {
  // when building in sandbox, use strings to represent paths in the vm
  val root:               ISZ[String] = ISZ("", "home", "vagrant")
  val project:            ISZ[String] = root :+ "project"
  val hls:                ISZ[String] = project :+ "hls"
  val hw:                 ISZ[String] = project :+ "hw"
  val sw:                 ISZ[String] = project :+ "sw"
  val original:           ISZ[String] = sw :+ "original"
  val driverCalls:        ISZ[String] = sw :+ "driver-calls"
  val transpiled:         ISZ[String] = sw :+ "transpiled"
  val modifiedTranspiled: ISZ[String] = sw :+ "modified-transpiled"
  val os:                 ISZ[String] = project :+ "os"
}