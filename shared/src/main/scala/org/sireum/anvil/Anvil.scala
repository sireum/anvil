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
import org.sireum.alir.TypeSpecializer
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Info
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.message.Reporter

object Anvil {

  @datatype class Config(val projectName: String,
                         val defaultBitWidth: Z,
                         val maxStringSize: Z,
                         val maxArraySize: Z,
                         val customArraySizes: HashMap[AST.Typed, Z],
                         val customConstants: HashMap[QName, AST.Exp])

  object Config {
    @strictpure def empty(projectName: String): Config =
      Config(projectName, 64, 100, 100, HashMap.empty, HashMap.empty)
  }

  val kind: String = "Anvil"

  def synthesize(th: TypeHierarchy, owner: QName, id: String, config: Config, reporter: Reporter): HashSMap[ISZ[String], ST] = {
    val tsr = TypeSpecializer.specialize(th, ISZ(TypeSpecializer.EntryPoint.Method(owner :+ id)), HashMap.empty,
      reporter)
    if (tsr.extMethods.nonEmpty) {
      reporter.error(None(), kind, s"@ext methods are not supported")
    }
    if (reporter.hasError) {
      return HashSMap.empty
    }
    val threeAddressCode = T

    val irt = lang.IRTranslator(threeAddressCode = threeAddressCode, th = tsr.typeHierarchy)

    var globals = ISZ[AST.IR.Global]()
    var procedures = ISZ[AST.IR.Procedure]()
    
    for (p <- tsr.objectVars.entries) {
      val (owner, ids) = p
      var objPosOpt: Option[message.Position] = th.nameMap.get(owner) match {
        case Some(info: Info.Object) => Some(info.posOpt.get)
        case _ => None()
      }
      globals = globals :+ AST.IR.Global(AST.Typed.b, owner, objPosOpt.get)
      var stmts = ISZ[AST.Stmt]()
      for (id <- ids.elements) {
        val name = owner :+ id
        val v = th.nameMap.get(name).get.asInstanceOf[Info.Var]
        globals = globals :+ AST.IR.Global(v.typedOpt.get, name, v.posOpt.get)
        if (objPosOpt.isEmpty) {
          objPosOpt = v.posOpt
        }
        stmts = stmts :+ AST.Stmt.Assign(AST.Exp.Ident(v.ast.id, AST.ResolvedAttr(v.posOpt, v.resOpt, v.typedOpt)),
          v.ast.initOpt.get, AST.Attr(v.posOpt))
      }
      val pos = objPosOpt.get
      val objInitId = "<objinit>"
      val name = owner :+ objInitId
      val objInit = irt.translateMethodH(F, None(), owner, objInitId, ISZ(), ISZ(),
        AST.Typed.Fun(AST.Purity.Impure, F, ISZ(), AST.Typed.unit), pos, Some(AST.Body(stmts, ISZ())))
      var body = objInit.body.asInstanceOf[AST.IR.Body.Block]
      body = body(block = body.block(stmts = AST.IR.Stmt.Block(ISZ(
        AST.IR.Stmt.If(AST.IR.Exp.GlobalVarRef(name, AST.Typed.b, pos),
          AST.IR.Stmt.Block(ISZ(AST.IR.Stmt.Return(None(), pos)), pos),
          AST.IR.Stmt.Block(ISZ(), pos), pos),
        AST.IR.Stmt.Assign.Global(F, name, AST.IR.Exp.Bool(T, pos), pos)
      ), pos) +: body.block.stmts))
      procedures = procedures :+ objInit(body = irt.toBasic(body, objInit.pos))
    }

    for (ms <- tsr.methods.values; m <- ms.elements) {
      procedures = procedures :+ irt.translateMethod(T, None(), m.info.owner, m.info.ast)
    }

    var r = HashSMap.empty[ISZ[String], ST]

    val program = AST.IR.Program(threeAddressCode, ISZ(), procedures)
    r = r + ISZ("ir", "program.sir") ~> program.prettyST
    r = r ++ HwSynthesizer(th, config, owner, id).printProgram(program).entries
    return r
  }
}