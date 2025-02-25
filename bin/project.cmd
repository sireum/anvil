::/*#! 2> /dev/null                                   #
@ 2>/dev/null # 2>nul & echo off & goto BOF           #
if [ -z "${SIREUM_HOME}" ]; then                      #
  echo "Please set SIREUM_HOME env var"               #
  exit -1                                             #
fi                                                    #
exec "${SIREUM_HOME}/bin/sireum" slang run "$0" "$@"  #
:BOF
setlocal
if not defined SIREUM_HOME (
  echo Please set SIREUM_HOME env var
  exit /B -1
)
"%SIREUM_HOME%\bin\sireum.bat" slang run %0 %*
exit /B %errorlevel%
::!#*/
// #Sireum

import org.sireum._
import org.sireum.project.ProjectUtil._
import org.sireum.project.Project

val library = "library"

val alir = "alir"

val frontend = "slang-frontend"

val anvil = "anvil"

val homeDir = Os.slashDir.up.canon

val (shared, jvm) = moduleSharedJvmPub(
  baseId = s"$anvil",
  baseDir = homeDir,
  sharedDeps = ISZ(alir, s"$frontend-shared"),
  sharedIvyDeps = ISZ(),
  jvmDeps = ISZ(library, frontend),
  jvmIvyDeps = ISZ(),
  pubOpt = pub(
    desc = "Anvil",
    url = "github.com/sireum/anvil",
    licenses = bsd2,
    devs = ISZ(robby, kejunChen)
  )
)

val project = Project.empty + shared + jvm

projectCli(Os.cliArgs, project)