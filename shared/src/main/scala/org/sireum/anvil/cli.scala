// #Sireum
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
import org.sireum.cli.CliOpt._

object cli {

  val anvil: Tool = Tool(
    name = "anvil",
    command = "anvil",
    description = "High-level hardware synthesizer",
    header = "Anvil HLS",
    usage = "<option>* <fully-qualified-method-name> [ <slang-file.sc> ]",
    usageDescOpt = None(),
    opts = ISZ(
      Opt(name = "sourcepath", longKey = "sourcepath", shortKey = Some('s'),
        tpe = Type.Path(T, None()),
        description = "Sourcepath of Slang .scala files"),
      Opt(name = "strictAliasing", longKey = "strict-aliasing", shortKey = None(),
        tpe = Type.Flag(F),
        description = "Enable strict aliasing check"),
      Opt(name = "memory", longKey = "memory", shortKey = Some('m'),
        tpe = Type.Num(sep = None(), default = 512, min = Some(64), max = None()),
        description = "Memory size in kilobytes"),
      Opt(name = "erase", longKey = "erase", shortKey = Some('e'),
        tpe = Type.Flag(default = F),
        description = "Securely erase memory chunks as they are reclaimed"),
      Opt(name = "depth", longKey = "depth", shortKey = Some('d'),
        tpe = Type.Num(sep = None(), default = 1, min = Some(0), max = None()),
        description = "Maximum expression depth to coalesce (0 means unbounded)"),
      Opt(name = "runtimeCheck", longKey = "runtime-check", shortKey = Some('r'),
        tpe = Type.Flag(default = F),
        description = "Enable implicit and explicit runtime assertion checking"),
      Opt(name = "stackTrace", longKey = "stack-trace", shortKey = Some('t'),
        tpe = Type.Flag(default = F),
        description = "Enable call stack tracing"),
      Opt(name = "copy", longKey = "copy", shortKey = None(),
        tpe = Type.Num(sep = None(), default = 8, min = Some(8), max = None()),
        description = "The maximum number of bytes per cycle for memory copy operation"),
      Opt(name = "printSize", longKey = "print", shortKey = Some('p'),
        tpe = Type.NumFlag(default = 0, min = Some(4), max = None()),
        description = "Printing console buffer size in kilobytes (rounded up to a power of 2)"),
      Opt(name = "output", longKey = "output-dir", shortKey = Some('o'),
        tpe = Type.Path(F, Some("out")),
        description = "Output directory synthesized files"),
      Opt(name = "axi4", longKey = "axi4", shortKey = None(),
        tpe = Type.Flag(F), description = "Enable AXI4 interface"),
      Opt(name = "customDivRem", longKey = "custom-div-rem", shortKey = None(),
        tpe = Type.Flag(F), description = "Enable custom division and remainder implementations"),
      Opt(name = "verbose", longKey = "verbose", shortKey = None(),
        tpe = Type.Flag(F), description = "Enable verbose mode")
    ),
    groups = ISZ(
      OptGroup(name = "Configuration", opts = ISZ(
        Opt(name = "bitWidth", longKey = "bits", shortKey = Some('b'),
          tpe = Type.NumChoice(None(), ISZ(64, 32, 16, 8)),
          description = "Default bit-width for unbounded integer types (e.g., Z)"),
        Opt(name = "projectName", longKey = "name", shortKey = Some('n'),
          tpe = Type.Str(sep = None(), default = None()),
          description = "Project name")
      )),
      OptGroup(name = "Array Bounds", opts = ISZ(
        Opt(name = "customArraySizes", longKey = "sequence", shortKey = Some('q'),
          tpe = Type.Str(Some(';'), None()),
          description = "Custom maximum sequence sizes, each in the form of <type>=<size>, where <type> is either IS[,], MS[,], ISZ[], MSZ[], or ZS with fully qualified index and element types where applicable"),
        Opt(name = "maxArraySize", longKey = "sequence-size", shortKey = None(),
          tpe = Type.Num(None(), 100, None(), None()),
          description = "Default maximum sequence size"),
        Opt(name = "maxStringSize", longKey = "string-size", shortKey = None(),
          tpe = Type.Num(None(), 100, None(), None()),
          description = "Maximum string size")
      )),
      OptGroup(name = "Persistence", opts = ISZ(
        Opt(name = "save", longKey = "save", shortKey = None(), tpe = Type.Path(F, None()),
          description = "Path to save type information to (outline should not be enabled)"),
        Opt(name = "load", longKey = "load", shortKey = None(), tpe = Type.Path(F, None()),
          description = "Path to load type information from")
      )),
      OptGroup(name = "Substitutions", opts = ISZ(
        Opt(name = "customConstants", longKey = "constants", shortKey = Some('c'),
          tpe = Type.Str(Some(';'), None()),
          description = "Custom constant for object variables, each in the form of <name>=<lit>, where <name> is a qualified name of an object var and <lit> is a Slang literal expression")
      ))
    )
  )

}