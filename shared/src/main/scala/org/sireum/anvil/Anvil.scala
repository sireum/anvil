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

  @record class GroundOffsetTransformer(m: HashMap[String, Z]) extends AST.MIRTransformer {
    override def postIRExpLocalVarRef(o: AST.IR.Exp.LocalVarRef): MOption[AST.IR.Exp] = {
      val offset = m.get(o.id).get
      return MSome(AST.IR.Exp.Intrinsic(Intrinsic.LocalOffset(o.isVal, offset, o.context, o.id, o.tipe, o.pos)))
    }

    override def postIRStmtGround(o: AST.IR.Stmt.Ground): MOption[AST.IR.Stmt.Ground] = {
      o match {
        case o: AST.IR.Stmt.Assign.Local =>
          val offset = m.get(o.lhs).get
          return MSome(AST.IR.Stmt.Intrinsic(Intrinsic.LocalOffsetAssign(o.copy, offset, o.context, o.lhs, o.rhs, o.pos)))
        case _ => return MNone()
      }
    }
  }

  val kind: String = "Anvil"
  val returnLocalId: String = "$ret"
  val cpType: AST.Typed = AST.Typed.z

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
    var procedureMap = HashSMap.empty[AST.IR.MethodContext, AST.IR.Procedure]
    val hws = HwSynthesizer(th, config, tsr.typeImpl, owner, id)
    
    for (vs <- tsr.objectVars.entries) {
      val (owner, ids) = vs
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
      val p = objInit(body = irt.toBasic(body, objInit.pos))
      procedureMap = procedureMap + p.context ~> p
    }

    def transformOffset(proc: AST.IR.Procedure): (Z, AST.IR.Procedure) = {
      val body = proc.body.asInstanceOf[AST.IR.Body.Basic]
      val blocks = body.blocks
      var blockMap: HashSMap[Z, AST.IR.BasicBlock] = HashSMap ++ (for (b <- blocks) yield (b.label, b))
      var blockLocalOffsetMap = HashMap.empty[Z, (Z, HashMap[String, Z])]
      var maxOffset: Z = 0
      ;{
        var m = HashMap.empty[String, Z]
        var offset: Z = 0
        for (param <- ops.ISZOps(proc.paramNames).zip(proc.tipe.args)) {
          m = m + param._1 ~> offset
          offset = offset + hws.typeByteSize(param._2)
        }
        blockLocalOffsetMap = blockLocalOffsetMap + blocks(0).label ~> (offset, m)
        maxOffset = offset
      }
      var work = ISZ(blocks(0))
      while (work.nonEmpty) {
        var next = ISZ[AST.IR.BasicBlock]()
        for (b <- work) {
          var (offset, m) = blockLocalOffsetMap.get(b.label).get
          var grounds = ISZ[AST.IR.Stmt.Ground]()
          for (g <- b.grounds) {
            g match {
              case g: AST.IR.Stmt.Decl =>
                val mult: Z = if (g.undecl) -1 else 1
                for (l <- g.locals) {
                  if (g.undecl) {
                    m = m -- ISZ(l.id)
                  } else {
                    m = m + l.id ~> offset
                  }
                  offset = offset + hws.typeByteSize(l.tipe) * mult
                }
                if (maxOffset < offset) {
                  maxOffset = offset
                }
                grounds = grounds :+ g
              case _ =>
                grounds = grounds :+ GroundOffsetTransformer(m).transformIRStmtGround(g).getOrElse(g)
            }
          }
          blockMap = blockMap + b.label ~> b(grounds = grounds)
          for (target <- b.jump.targets) {
            blockLocalOffsetMap.get(target) match {
              case Some((po, pm)) =>
                assert(offset == po && m == pm, s"$target: offset = $offset, po = $po, m = $m, pm = $pm")
              case _ =>
                blockLocalOffsetMap = blockLocalOffsetMap + target ~> (offset, m)
                next = next :+ blockMap.get(target).get
            }
          }
        }
        work = next
      }
      return (maxOffset, proc(body = body(blocks = blockMap.values)))
    }

    var procedureSizeMap = HashMap.empty[AST.IR.MethodContext, Z]
    val main: AST.IR.Procedure = {
      var mainOpt = Option.none[AST.IR.Procedure]()
      for (ms <- tsr.methods.values; m <- ms.elements) {
        var p = irt.translateMethod(T, None(), m.info.owner, m.info.ast)
        p = p(paramNames = returnLocalId +: p.paramNames, tipe = p.tipe(args = cpType +: p.tipe.args))
        val (maxOffset, p2) = transformOffset(p)
        p = p2
        procedureSizeMap = procedureSizeMap + p.context ~> maxOffset
        procedureMap = procedureMap + p.context ~> p
        if (m.info.owner == owner && m.info.ast.sig.id.value == id) {
          mainOpt = Some(p)
        }
      }
      mainOpt.get
    }

    def mergeProcedures(): ISZ[AST.IR.BasicBlock] = {
      var seen = HashSet.empty[AST.IR.MethodContext]
      var work = ISZ[AST.IR.Procedure](main)
      var mergedBlocks = ISZ[AST.IR.BasicBlock]()
      while (work.nonEmpty) {
        var next = ISZ[AST.IR.Procedure]()
        for (p <- work) {
          seen = seen + p.context
          var addBeginningMap = HashSMap.empty[Z, ISZ[AST.IR.Stmt.Ground]]
          var blocks = ISZ[AST.IR.BasicBlock]()
          for (b <- p.body.asInstanceOf[AST.IR.Body.Basic].blocks) {
            def processInvoke(g: AST.IR.Stmt.Ground, lhsOpt: Option[Z], e: AST.IR.Exp.Apply, label: Z): Unit = {
              val mc = AST.IR.MethodContext(e.isInObject, e.owner, e.id, e.methodType(args = cpType +: e.methodType.args))
              val called = procedureMap.get(mc).get
              if (!seen.contains(mc)) {
                next = next :+ called
              }
              val spAdd = procedureSizeMap.get(p.context).get
              var grounds = ISZ[AST.IR.Stmt.Ground](
                AST.IR.Stmt.Intrinsic(Intrinsic.StackPointer(spAdd, e.pos))
              )
              var locals = ISZ[AST.IR.Stmt.Decl.Local]()
              for (param <- ops.ISZOps(called.paramNames).zip(called.tipe.args)) {
                locals = locals :+ AST.IR.Stmt.Decl.Local(param._1, param._2)
              }
              grounds = grounds :+ AST.IR.Stmt.Decl(F, T, called.context, locals, e.pos)
              var paramOffset: Z = 0
              for (param <- ops.ISZOps(ops.ISZOps(called.paramNames).zip(mc.t.args)).zip(AST.IR.Exp.Int(cpType, 0, label, e.pos) +: e.args)) {
                grounds = grounds :+ AST.IR.Stmt.Intrinsic(
                  Intrinsic.LocalOffsetAssign(F, paramOffset, mc, param._1._1, param._2, e.pos))
                paramOffset = paramOffset + hws.typeByteSize(param._1._2)
              }
              var bgrounds = ISZ[AST.IR.Stmt.Ground](
                AST.IR.Stmt.Decl(T, T, called.context, for (i <- locals.size - 1 to 0 by -1) yield locals(i), e.pos),
                AST.IR.Stmt.Intrinsic(Intrinsic.StackPointer(-spAdd, e.pos))
              )
              lhsOpt match {
                case Some(lhs) => bgrounds = AST.IR.Stmt.Assign.Temp(lhs, AST.IR.Exp.Intrinsic(
                  Intrinsic.LocalOffset(F, 0, mc, returnLocalId, cpType, e.pos)), e.pos) +: bgrounds
                case _ =>
              }
              addBeginningMap = addBeginningMap + label ~> bgrounds
              blocks = blocks :+ b(grounds = grounds,
                jump = AST.IR.Jump.Goto(called.body.asInstanceOf[AST.IR.Body.Basic].blocks(0).label, e.pos))
            }
            b.jump match {
              case j: AST.IR.Jump.Goto if b.grounds.size == 1 =>
                b.grounds(0) match {
                  case g: AST.IR.Stmt.Expr => processInvoke(g, None(), g.exp, j.label)
                  case g: AST.IR.Stmt.Assign.Temp if g.rhs.isInstanceOf[AST.IR.Exp.Apply] =>
                    processInvoke(g, Some(g.lhs), g.rhs.asInstanceOf[AST.IR.Exp.Apply], j.label)
                  case _ =>
                }
              case j: AST.IR.Jump.Return if p.context != main.context =>
                blocks = blocks :+ b(jump = AST.IR.Jump.Intrinsic(Intrinsic.GotoLocal(0, p.context, returnLocalId, j.pos)))
              case _ => blocks = blocks :+ b
            }
          }
          for (b <- blocks) {
            addBeginningMap.get(b.label) match {
              case Some(grounds) => mergedBlocks = mergedBlocks :+ b(grounds = grounds ++ b.grounds)
              case _ => mergedBlocks = mergedBlocks :+ b
            }
          }
        }
        work = next
      }
      return mergedBlocks
    }

    val program = AST.IR.Program(threeAddressCode, globals,
      ISZ(main(body = main.body.asInstanceOf[AST.IR.Body.Basic](blocks = mergeProcedures()))))

    var r = HashSMap.empty[ISZ[String], ST]
    r = r + ISZ("ir", "program.sir") ~> program(procedures = procedureMap.values).prettyST
    r = r + ISZ("ir", "program-merged.sir") ~> program.prettyST
    r = r ++ hws.printProgram(program).entries
    return r
  }
}