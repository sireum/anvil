// #Sireum
// @formatter:off

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

// This file is auto-generated from Intrinsic.scala

// This file is auto-generated from IR.scala

package org.sireum.anvil

import org.sireum._

object AnvilIRTransformer {

  @datatype class PreResult[Context, T](val ctx: Context,
                                        val continu: B,
                                        val resultOpt: Option[T])

  @datatype class TPostResult[Context, T](val ctx: Context,
                                          val resultOpt: Option[T])

  @sig trait PrePost[Context] {

    @pure def pre_langastIRMethodContext(ctx: Context, o: org.sireum.lang.ast.IR.MethodContext): PreResult[Context, org.sireum.lang.ast.IR.MethodContext] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicTempLoad(ctx: Context, o: Intrinsic.TempLoad): PreResult[Context, Intrinsic.TempLoad] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExp(ctx: Context, o: org.sireum.lang.ast.IR.Exp): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      o match {
        case o: org.sireum.lang.ast.IR.Exp.Bool => return pre_langastIRExpBool(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Int => return pre_langastIRExpInt(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.F32 => return pre_langastIRExpF32(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.F64 => return pre_langastIRExpF64(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.R => return pre_langastIRExpR(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.String => return pre_langastIRExpString(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Temp => return pre_langastIRExpTemp(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.LocalVarRef => return pre_langastIRExpLocalVarRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.GlobalVarRef => return pre_langastIRExpGlobalVarRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.EnumElementRef => return pre_langastIRExpEnumElementRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.FieldVarRef => return pre_langastIRExpFieldVarRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Unary => return pre_langastIRExpUnary(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Binary => return pre_langastIRExpBinary(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.If => return pre_langastIRExpIf(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Construct => return pre_langastIRExpConstruct(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Apply => return pre_langastIRExpApply(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Indexing => return pre_langastIRExpIndexing(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Type => return pre_langastIRExpType(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Intrinsic => return pre_langastIRExpIntrinsic(ctx, o)
      }
    }

    @pure def pre_langastIRExpBool(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Bool): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicLoad(ctx: Context, o: Intrinsic.Load): PreResult[Context, Intrinsic.Load] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpInt(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Int): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpF32(ctx: Context, o: org.sireum.lang.ast.IR.Exp.F32): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicIndexing(ctx: Context, o: Intrinsic.Indexing): PreResult[Context, Intrinsic.Indexing] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpF64(ctx: Context, o: org.sireum.lang.ast.IR.Exp.F64): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpR(ctx: Context, o: org.sireum.lang.ast.IR.Exp.R): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpString(ctx: Context, o: org.sireum.lang.ast.IR.Exp.String): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicStore(ctx: Context, o: Intrinsic.Store): PreResult[Context, Intrinsic.Store] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpTemp(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Temp): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpLocalVarRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.LocalVarRef): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicCopy(ctx: Context, o: Intrinsic.Copy): PreResult[Context, Intrinsic.Copy] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpGlobalVarRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.GlobalVarRef): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpEnumElementRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.EnumElementRef): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicDecl(ctx: Context, o: Intrinsic.Decl): PreResult[Context, Intrinsic.Decl] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpFieldVarRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.FieldVarRef): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicDeclLocal(ctx: Context, o: Intrinsic.Decl.Local): PreResult[Context, Intrinsic.Decl.Local] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicRegister(ctx: Context, o: Intrinsic.Register): PreResult[Context, Intrinsic.Register] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpUnary(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Unary): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicRegisterAssign(ctx: Context, o: Intrinsic.RegisterAssign): PreResult[Context, Intrinsic.RegisterAssign] = {
      return PreResult(ctx, T, None())
    }

    @pure def preIntrinsicGotoLocal(ctx: Context, o: Intrinsic.GotoLocal): PreResult[Context, Intrinsic.GotoLocal] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpBinary(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Binary): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpIf(ctx: Context, o: org.sireum.lang.ast.IR.Exp.If): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpConstruct(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Construct): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpApply(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Apply): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpIndexing(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Indexing): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpType(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Type): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpIntrinsic(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Intrinsic): PreResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRExpIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Intrinsic.Type): PreResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = {
      o match {
        case o: Intrinsic.Load =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = preIntrinsicLoad(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Indexing =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = preIntrinsicIndexing(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Register =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = preIntrinsicRegister(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
          }
          return r
      }
    }

    @pure def pre_langastIRStmt(ctx: Context, o: org.sireum.lang.ast.IR.Stmt): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.Expr =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtExpr(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignLocal(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignGlobal(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignTemp(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignField(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignIndex(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Decl =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtDecl(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtIntrinsic(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assertume => return pre_langastIRStmtAssertume(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Print => return pre_langastIRStmtPrint(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Halt => return pre_langastIRStmtHalt(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.AssignPattern => return pre_langastIRStmtAssignPattern(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Block => return pre_langastIRStmtBlock(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.If => return pre_langastIRStmtIf(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Match => return pre_langastIRStmtMatch(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.While => return pre_langastIRStmtWhile(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.For => return pre_langastIRStmtFor(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Return => return pre_langastIRStmtReturn(ctx, o)
      }
    }

    @pure def pre_langastIRStmtGround(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Ground): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.Expr => return pre_langastIRStmtExpr(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignLocal(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Ground](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignGlobal(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Ground](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignTemp(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Ground](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignField(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Ground](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignIndex(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Ground](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Decl => return pre_langastIRStmtDecl(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Intrinsic => return pre_langastIRStmtIntrinsic(ctx, o)
      }
    }

    @pure def pre_langastIRStmtExpr(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Expr): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtAssign(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Local => return pre_langastIRStmtAssignLocal(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Global => return pre_langastIRStmtAssignGlobal(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp => return pre_langastIRStmtAssignTemp(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Field => return pre_langastIRStmtAssignField(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Index => return pre_langastIRStmtAssignIndex(ctx, o)
      }
    }

    @pure def pre_langastIRStmtAssignLocal(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Local): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtAssignGlobal(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Global): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtAssignTemp(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Temp): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtAssignField(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Field): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtAssignIndex(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Index): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtDecl(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Decl): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtDeclLocal(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Decl.Local): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Decl.Local] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtIntrinsic(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Intrinsic): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = {
      o match {
        case o: Intrinsic.TempLoad =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicTempLoad(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Store =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicStore(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Copy =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicCopy(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Decl =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicDecl(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.RegisterAssign =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicRegisterAssign(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
      }
    }

    @pure def pre_langastIRStmtAssertume(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assertume): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtPrint(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Print): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtHalt(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Halt): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtAssignPattern(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.AssignPattern): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtBlock(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Block): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtIf(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.If): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtMatch(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Match): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtMatchCase(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Match.Case): PreResult[Context, org.sireum.lang.ast.IR.Stmt.Match.Case] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtWhile(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.While): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtFor(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtForRange(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For.Range): PreResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr => return pre_langastIRStmtForRangeExpr(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.For.Range.Step => return pre_langastIRStmtForRangeStep(ctx, o)
      }
    }

    @pure def pre_langastIRStmtForRangeExpr(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr): PreResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtForRangeStep(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For.Range.Step): PreResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRStmtReturn(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Return): PreResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJump(ctx: Context, o: org.sireum.lang.ast.IR.Jump): PreResult[Context, org.sireum.lang.ast.IR.Jump] = {
      o match {
        case o: org.sireum.lang.ast.IR.Jump.Goto => return pre_langastIRJumpGoto(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.If => return pre_langastIRJumpIf(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Return => return pre_langastIRJumpReturn(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Switch => return pre_langastIRJumpSwitch(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Halt => return pre_langastIRJumpHalt(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Intrinsic => return pre_langastIRJumpIntrinsic(ctx, o)
      }
    }

    @pure def pre_langastIRJumpGoto(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Goto): PreResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJumpIf(ctx: Context, o: org.sireum.lang.ast.IR.Jump.If): PreResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJumpReturn(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Return): PreResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJumpSwitch(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Switch): PreResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJumpSwitchCase(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Switch.Case): PreResult[Context, org.sireum.lang.ast.IR.Jump.Switch.Case] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJumpHalt(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Halt): PreResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJumpIntrinsic(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Intrinsic): PreResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRJumpIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Intrinsic.Type): PreResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = {
      o match {
        case o: Intrinsic.GotoLocal =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = preIntrinsicGotoLocal(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Jump.Intrinsic.Type)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Jump.Intrinsic.Type](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Jump.Intrinsic.Type")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Jump.Intrinsic.Type]())
          }
          return r
      }
    }

    @pure def pre_langastIRExpBlock(ctx: Context, o: org.sireum.lang.ast.IR.ExpBlock): PreResult[Context, org.sireum.lang.ast.IR.ExpBlock] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRBasicBlock(ctx: Context, o: org.sireum.lang.ast.IR.BasicBlock): PreResult[Context, org.sireum.lang.ast.IR.BasicBlock] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRBody(ctx: Context, o: org.sireum.lang.ast.IR.Body): PreResult[Context, org.sireum.lang.ast.IR.Body] = {
      o match {
        case o: org.sireum.lang.ast.IR.Body.Block => return pre_langastIRBodyBlock(ctx, o)
        case o: org.sireum.lang.ast.IR.Body.Basic => return pre_langastIRBodyBasic(ctx, o)
      }
    }

    @pure def pre_langastIRBodyBlock(ctx: Context, o: org.sireum.lang.ast.IR.Body.Block): PreResult[Context, org.sireum.lang.ast.IR.Body] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRBodyBasic(ctx: Context, o: org.sireum.lang.ast.IR.Body.Basic): PreResult[Context, org.sireum.lang.ast.IR.Body] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRProcedure(ctx: Context, o: org.sireum.lang.ast.IR.Procedure): PreResult[Context, org.sireum.lang.ast.IR.Procedure] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRGlobal(ctx: Context, o: org.sireum.lang.ast.IR.Global): PreResult[Context, org.sireum.lang.ast.IR.Global] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRProgram(ctx: Context, o: org.sireum.lang.ast.IR.Program): PreResult[Context, org.sireum.lang.ast.IR.Program] = {
      return PreResult(ctx, T, None())
    }

    @pure def pre_langastIRPrinter(ctx: Context, o: org.sireum.lang.ast.IR.Printer): PreResult[Context, org.sireum.lang.ast.IR.Printer] = {
      o match {
        case o: org.sireum.lang.ast.IR.Printer.Empty =>
          val r: PreResult[Context, org.sireum.lang.ast.IR.Printer] = pre_langastIRPrinterEmpty(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Printer)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Printer](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Printer")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Printer]())
          }
          return r
      }
    }

    @pure def pre_langastIRPrinterEmpty(ctx: Context, o: org.sireum.lang.ast.IR.Printer.Empty): PreResult[Context, org.sireum.lang.ast.IR.Printer.Empty] = {
      return PreResult(ctx, T, None())
    }

    @pure def post_langastIRMethodContext(ctx: Context, o: org.sireum.lang.ast.IR.MethodContext): TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicTempLoad(ctx: Context, o: Intrinsic.TempLoad): TPostResult[Context, Intrinsic.TempLoad] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExp(ctx: Context, o: org.sireum.lang.ast.IR.Exp): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      o match {
        case o: org.sireum.lang.ast.IR.Exp.Bool => return post_langastIRExpBool(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Int => return post_langastIRExpInt(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.F32 => return post_langastIRExpF32(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.F64 => return post_langastIRExpF64(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.R => return post_langastIRExpR(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.String => return post_langastIRExpString(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Temp => return post_langastIRExpTemp(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.LocalVarRef => return post_langastIRExpLocalVarRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.GlobalVarRef => return post_langastIRExpGlobalVarRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.EnumElementRef => return post_langastIRExpEnumElementRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.FieldVarRef => return post_langastIRExpFieldVarRef(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Unary => return post_langastIRExpUnary(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Binary => return post_langastIRExpBinary(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.If => return post_langastIRExpIf(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Construct => return post_langastIRExpConstruct(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Apply => return post_langastIRExpApply(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Indexing => return post_langastIRExpIndexing(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Type => return post_langastIRExpType(ctx, o)
        case o: org.sireum.lang.ast.IR.Exp.Intrinsic => return post_langastIRExpIntrinsic(ctx, o)
      }
    }

    @pure def post_langastIRExpBool(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Bool): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicLoad(ctx: Context, o: Intrinsic.Load): TPostResult[Context, Intrinsic.Load] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpInt(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Int): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpF32(ctx: Context, o: org.sireum.lang.ast.IR.Exp.F32): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicIndexing(ctx: Context, o: Intrinsic.Indexing): TPostResult[Context, Intrinsic.Indexing] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpF64(ctx: Context, o: org.sireum.lang.ast.IR.Exp.F64): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpR(ctx: Context, o: org.sireum.lang.ast.IR.Exp.R): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpString(ctx: Context, o: org.sireum.lang.ast.IR.Exp.String): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicStore(ctx: Context, o: Intrinsic.Store): TPostResult[Context, Intrinsic.Store] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpTemp(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Temp): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpLocalVarRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.LocalVarRef): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicCopy(ctx: Context, o: Intrinsic.Copy): TPostResult[Context, Intrinsic.Copy] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpGlobalVarRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.GlobalVarRef): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpEnumElementRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.EnumElementRef): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicDecl(ctx: Context, o: Intrinsic.Decl): TPostResult[Context, Intrinsic.Decl] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpFieldVarRef(ctx: Context, o: org.sireum.lang.ast.IR.Exp.FieldVarRef): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicDeclLocal(ctx: Context, o: Intrinsic.Decl.Local): TPostResult[Context, Intrinsic.Decl.Local] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicRegister(ctx: Context, o: Intrinsic.Register): TPostResult[Context, Intrinsic.Register] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpUnary(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Unary): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicRegisterAssign(ctx: Context, o: Intrinsic.RegisterAssign): TPostResult[Context, Intrinsic.RegisterAssign] = {
      return TPostResult(ctx, None())
    }

    @pure def postIntrinsicGotoLocal(ctx: Context, o: Intrinsic.GotoLocal): TPostResult[Context, Intrinsic.GotoLocal] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpBinary(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Binary): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpIf(ctx: Context, o: org.sireum.lang.ast.IR.Exp.If): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpConstruct(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Construct): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpApply(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Apply): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpIndexing(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Indexing): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpType(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Type): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpIntrinsic(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Intrinsic): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRExpIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Intrinsic.Type): TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = {
      o match {
        case o: Intrinsic.Load =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = postIntrinsicLoad(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Indexing =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = postIntrinsicIndexing(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Register =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = postIntrinsicRegister(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
          }
          return r
      }
    }

    @pure def post_langastIRStmt(ctx: Context, o: org.sireum.lang.ast.IR.Stmt): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.Expr =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtExpr(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignLocal(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignGlobal(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignTemp(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignField(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignIndex(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Decl =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtDecl(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtIntrinsic(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assertume => return post_langastIRStmtAssertume(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Print => return post_langastIRStmtPrint(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Halt => return post_langastIRStmtHalt(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.AssignPattern => return post_langastIRStmtAssignPattern(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Block => return post_langastIRStmtBlock(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.If => return post_langastIRStmtIf(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Match => return post_langastIRStmtMatch(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.While => return post_langastIRStmtWhile(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.For => return post_langastIRStmtFor(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Return => return post_langastIRStmtReturn(ctx, o)
      }
    }

    @pure def post_langastIRStmtGround(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Ground): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.Expr => return post_langastIRStmtExpr(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignLocal(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Ground)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Ground](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignGlobal(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Ground)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Ground](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignTemp(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Ground)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Ground](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignField(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Ground)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Ground](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignIndex(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Ground)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Ground](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Ground]())
          }
          return r
        case o: org.sireum.lang.ast.IR.Stmt.Decl => return post_langastIRStmtDecl(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Intrinsic => return post_langastIRStmtIntrinsic(ctx, o)
      }
    }

    @pure def post_langastIRStmtExpr(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Expr): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtAssign(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Local => return post_langastIRStmtAssignLocal(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Global => return post_langastIRStmtAssignGlobal(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp => return post_langastIRStmtAssignTemp(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Field => return post_langastIRStmtAssignField(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.Assign.Index => return post_langastIRStmtAssignIndex(ctx, o)
      }
    }

    @pure def post_langastIRStmtAssignLocal(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Local): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtAssignGlobal(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Global): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtAssignTemp(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Temp): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtAssignField(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Field): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtAssignIndex(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign.Index): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtDecl(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Decl): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtDeclLocal(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Decl.Local): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl.Local] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtIntrinsic(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Intrinsic): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = {
      o match {
        case o: Intrinsic.TempLoad =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicTempLoad(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Store =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicStore(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Copy =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicCopy(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.Decl =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicDecl(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
        case o: Intrinsic.RegisterAssign =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicRegisterAssign(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
          }
          return r
      }
    }

    @pure def post_langastIRStmtAssertume(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assertume): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtPrint(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Print): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtHalt(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Halt): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtAssignPattern(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.AssignPattern): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtBlock(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Block): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtIf(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.If): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtMatch(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Match): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtMatchCase(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Match.Case): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Match.Case] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtWhile(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.While): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtFor(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtForRange(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For.Range): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = {
      o match {
        case o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr => return post_langastIRStmtForRangeExpr(ctx, o)
        case o: org.sireum.lang.ast.IR.Stmt.For.Range.Step => return post_langastIRStmtForRangeStep(ctx, o)
      }
    }

    @pure def post_langastIRStmtForRangeExpr(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtForRangeStep(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For.Range.Step): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRStmtReturn(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Return): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJump(ctx: Context, o: org.sireum.lang.ast.IR.Jump): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
      o match {
        case o: org.sireum.lang.ast.IR.Jump.Goto => return post_langastIRJumpGoto(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.If => return post_langastIRJumpIf(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Return => return post_langastIRJumpReturn(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Switch => return post_langastIRJumpSwitch(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Halt => return post_langastIRJumpHalt(ctx, o)
        case o: org.sireum.lang.ast.IR.Jump.Intrinsic => return post_langastIRJumpIntrinsic(ctx, o)
      }
    }

    @pure def post_langastIRJumpGoto(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Goto): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJumpIf(ctx: Context, o: org.sireum.lang.ast.IR.Jump.If): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJumpReturn(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Return): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJumpSwitch(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Switch): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJumpSwitchCase(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Switch.Case): TPostResult[Context, org.sireum.lang.ast.IR.Jump.Switch.Case] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJumpHalt(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Halt): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJumpIntrinsic(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Intrinsic): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRJumpIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Intrinsic.Type): TPostResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = {
      o match {
        case o: Intrinsic.GotoLocal =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = postIntrinsicGotoLocal(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Jump.Intrinsic.Type)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Jump.Intrinsic.Type](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Jump.Intrinsic.Type")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Jump.Intrinsic.Type]())
          }
          return r
      }
    }

    @pure def post_langastIRExpBlock(ctx: Context, o: org.sireum.lang.ast.IR.ExpBlock): TPostResult[Context, org.sireum.lang.ast.IR.ExpBlock] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRBasicBlock(ctx: Context, o: org.sireum.lang.ast.IR.BasicBlock): TPostResult[Context, org.sireum.lang.ast.IR.BasicBlock] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRBody(ctx: Context, o: org.sireum.lang.ast.IR.Body): TPostResult[Context, org.sireum.lang.ast.IR.Body] = {
      o match {
        case o: org.sireum.lang.ast.IR.Body.Block => return post_langastIRBodyBlock(ctx, o)
        case o: org.sireum.lang.ast.IR.Body.Basic => return post_langastIRBodyBasic(ctx, o)
      }
    }

    @pure def post_langastIRBodyBlock(ctx: Context, o: org.sireum.lang.ast.IR.Body.Block): TPostResult[Context, org.sireum.lang.ast.IR.Body] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRBodyBasic(ctx: Context, o: org.sireum.lang.ast.IR.Body.Basic): TPostResult[Context, org.sireum.lang.ast.IR.Body] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRProcedure(ctx: Context, o: org.sireum.lang.ast.IR.Procedure): TPostResult[Context, org.sireum.lang.ast.IR.Procedure] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRGlobal(ctx: Context, o: org.sireum.lang.ast.IR.Global): TPostResult[Context, org.sireum.lang.ast.IR.Global] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRProgram(ctx: Context, o: org.sireum.lang.ast.IR.Program): TPostResult[Context, org.sireum.lang.ast.IR.Program] = {
      return TPostResult(ctx, None())
    }

    @pure def post_langastIRPrinter(ctx: Context, o: org.sireum.lang.ast.IR.Printer): TPostResult[Context, org.sireum.lang.ast.IR.Printer] = {
      o match {
        case o: org.sireum.lang.ast.IR.Printer.Empty =>
          val r: TPostResult[Context, org.sireum.lang.ast.IR.Printer] = post_langastIRPrinterEmpty(ctx, o) match {
           case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Printer)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Printer](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Printer")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Printer]())
          }
          return r
      }
    }

    @pure def post_langastIRPrinterEmpty(ctx: Context, o: org.sireum.lang.ast.IR.Printer.Empty): TPostResult[Context, org.sireum.lang.ast.IR.Printer.Empty] = {
      return TPostResult(ctx, None())
    }

  }

  @pure def transformISZ[Context, T](ctx: Context, s: IS[Z, T], f: (Context, T) => TPostResult[Context, T] @pure): TPostResult[Context, IS[Z, T]] = {
    val s2: MS[Z, T] = s.toMS
    var changed: B = F
    var ctxi = ctx
    for (i <- s2.indices) {
      val e: T = s(i)
      val r: TPostResult[Context, T] = f(ctxi, e)
      ctxi = r.ctx
      changed = changed || r.resultOpt.nonEmpty
      s2(i) = r.resultOpt.getOrElse(e)
    }
    if (changed) {
      return TPostResult(ctxi, Some(s2.toIS))
    } else {
      return TPostResult[Context, IS[Z, T]](ctxi, None[IS[Z, T]]())
    }
  }

  @pure def transformOption[Context, T](ctx: Context, option: Option[T], f: (Context, T) => TPostResult[Context, T] @pure): TPostResult[Context, Option[T]] = {
    option match {
      case Some(v) =>
        val r = f(ctx, v)
        r.resultOpt match {
          case Some(_) => return TPostResult(r.ctx, Some(r.resultOpt))
          case _ => return TPostResult[Context, Option[T]](r.ctx, None[Option[T]]())
        }
      case _ => return TPostResult[Context, Option[T]](ctx, None[Option[T]]())
    }
  }

}

import AnvilIRTransformer._

@datatype class AnvilIRTransformer[Context](val pp: PrePost[Context]) {

  @pure def transform_langastIRMethodContext(ctx: Context, o: org.sireum.lang.ast.IR.MethodContext): TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.MethodContext] = pp.pre_langastIRMethodContext(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.MethodContext = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.MethodContext = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = pp.post_langastIRMethodContext(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicTempLoad(ctx: Context, o: Intrinsic.TempLoad): TPostResult[Context, Intrinsic.TempLoad] = {
    val preR: PreResult[Context, Intrinsic.TempLoad] = pp.preIntrinsicTempLoad(ctx, o)
    val r: TPostResult[Context, Intrinsic.TempLoad] = if (preR.continu) {
      val o2: Intrinsic.TempLoad = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhsOffset)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(rhsOffset = r0.resultOpt.getOrElse(o2.rhsOffset))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.TempLoad = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.TempLoad] = pp.postIntrinsicTempLoad(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRExp(ctx: Context, o: org.sireum.lang.ast.IR.Exp): TPostResult[Context, org.sireum.lang.ast.IR.Exp] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Exp] = pp.pre_langastIRExp(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Exp = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = o2 match {
        case o2: org.sireum.lang.ast.IR.Exp.Bool =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Int =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.F32 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.F64 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.R =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.String =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Temp =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.LocalVarRef =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.GlobalVarRef =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.EnumElementRef =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.FieldVarRef =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.receiver)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(receiver = r0.resultOpt.getOrElse(o2.receiver))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Unary =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.exp)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Binary =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.left)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.right)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(left = r0.resultOpt.getOrElse(o2.left), right = r1.resultOpt.getOrElse(o2.right))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.If =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.cond)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.thenExp)
          val r2: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r1.ctx, o2.elseExp)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(cond = r0.resultOpt.getOrElse(o2.cond), thenExp = r1.resultOpt.getOrElse(o2.thenExp), elseExp = r2.resultOpt.getOrElse(o2.elseExp))))
          else
            TPostResult(r2.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Construct =>
          val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(preR.ctx, o2.args, transform_langastIRExp _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(args = r0.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Apply =>
          val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(preR.ctx, o2.args, transform_langastIRExp _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(args = r0.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Indexing =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.exp)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp), index = r1.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Type =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.exp)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Exp.Intrinsic =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = transform_langastIRExpIntrinsicType(preR.ctx, o2.intrinsic)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(intrinsic = r0.resultOpt.getOrElse(o2.intrinsic))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Exp = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = pp.post_langastIRExp(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicLoad(ctx: Context, o: Intrinsic.Load): TPostResult[Context, Intrinsic.Load] = {
    val preR: PreResult[Context, Intrinsic.Load] = pp.preIntrinsicLoad(ctx, o)
    val r: TPostResult[Context, Intrinsic.Load] = if (preR.continu) {
      val o2: Intrinsic.Load = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhsOffset)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(rhsOffset = r0.resultOpt.getOrElse(o2.rhsOffset))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.Load = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.Load] = pp.postIntrinsicLoad(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicIndexing(ctx: Context, o: Intrinsic.Indexing): TPostResult[Context, Intrinsic.Indexing] = {
    val preR: PreResult[Context, Intrinsic.Indexing] = pp.preIntrinsicIndexing(ctx, o)
    val r: TPostResult[Context, Intrinsic.Indexing] = if (preR.continu) {
      val o2: Intrinsic.Indexing = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.baseOffset)
      val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.index)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
        TPostResult(r1.ctx, Some(o2(baseOffset = r0.resultOpt.getOrElse(o2.baseOffset), index = r1.resultOpt.getOrElse(o2.index))))
      else
        TPostResult(r1.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.Indexing = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.Indexing] = pp.postIntrinsicIndexing(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicStore(ctx: Context, o: Intrinsic.Store): TPostResult[Context, Intrinsic.Store] = {
    val preR: PreResult[Context, Intrinsic.Store] = pp.preIntrinsicStore(ctx, o)
    val r: TPostResult[Context, Intrinsic.Store] = if (preR.continu) {
      val o2: Intrinsic.Store = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.lhsOffset)
      val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
        TPostResult(r1.ctx, Some(o2(lhsOffset = r0.resultOpt.getOrElse(o2.lhsOffset), rhs = r1.resultOpt.getOrElse(o2.rhs))))
      else
        TPostResult(r1.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.Store = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.Store] = pp.postIntrinsicStore(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicCopy(ctx: Context, o: Intrinsic.Copy): TPostResult[Context, Intrinsic.Copy] = {
    val preR: PreResult[Context, Intrinsic.Copy] = pp.preIntrinsicCopy(ctx, o)
    val r: TPostResult[Context, Intrinsic.Copy] = if (preR.continu) {
      val o2: Intrinsic.Copy = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.lhsOffset)
      val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhsBytes)
      val r2: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r1.ctx, o2.rhs)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
        TPostResult(r2.ctx, Some(o2(lhsOffset = r0.resultOpt.getOrElse(o2.lhsOffset), rhsBytes = r1.resultOpt.getOrElse(o2.rhsBytes), rhs = r2.resultOpt.getOrElse(o2.rhs))))
      else
        TPostResult(r2.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.Copy = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.Copy] = pp.postIntrinsicCopy(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicDecl(ctx: Context, o: Intrinsic.Decl): TPostResult[Context, Intrinsic.Decl] = {
    val preR: PreResult[Context, Intrinsic.Decl] = pp.preIntrinsicDecl(ctx, o)
    val r: TPostResult[Context, Intrinsic.Decl] = if (preR.continu) {
      val o2: Intrinsic.Decl = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, IS[Z, Intrinsic.Decl.Local]] = transformISZ(preR.ctx, o2.slots, transformIntrinsicDeclLocal _)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(slots = r0.resultOpt.getOrElse(o2.slots))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.Decl = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.Decl] = pp.postIntrinsicDecl(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicDeclLocal(ctx: Context, o: Intrinsic.Decl.Local): TPostResult[Context, Intrinsic.Decl.Local] = {
    val preR: PreResult[Context, Intrinsic.Decl.Local] = pp.preIntrinsicDeclLocal(ctx, o)
    val r: TPostResult[Context, Intrinsic.Decl.Local] = if (preR.continu) {
      val o2: Intrinsic.Decl.Local = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.Decl.Local = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.Decl.Local] = pp.postIntrinsicDeclLocal(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicRegister(ctx: Context, o: Intrinsic.Register): TPostResult[Context, Intrinsic.Register] = {
    val preR: PreResult[Context, Intrinsic.Register] = pp.preIntrinsicRegister(ctx, o)
    val r: TPostResult[Context, Intrinsic.Register] = if (preR.continu) {
      val o2: Intrinsic.Register = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.Register = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.Register] = pp.postIntrinsicRegister(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicRegisterAssign(ctx: Context, o: Intrinsic.RegisterAssign): TPostResult[Context, Intrinsic.RegisterAssign] = {
    val preR: PreResult[Context, Intrinsic.RegisterAssign] = pp.preIntrinsicRegisterAssign(ctx, o)
    val r: TPostResult[Context, Intrinsic.RegisterAssign] = if (preR.continu) {
      val o2: Intrinsic.RegisterAssign = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.value)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(value = r0.resultOpt.getOrElse(o2.value))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.RegisterAssign = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.RegisterAssign] = pp.postIntrinsicRegisterAssign(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformIntrinsicGotoLocal(ctx: Context, o: Intrinsic.GotoLocal): TPostResult[Context, Intrinsic.GotoLocal] = {
    val preR: PreResult[Context, Intrinsic.GotoLocal] = pp.preIntrinsicGotoLocal(ctx, o)
    val r: TPostResult[Context, Intrinsic.GotoLocal] = if (preR.continu) {
      val o2: Intrinsic.GotoLocal = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: Intrinsic.GotoLocal = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, Intrinsic.GotoLocal] = pp.postIntrinsicGotoLocal(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRExpIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Intrinsic.Type): TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = pp.pre_langastIRExpIntrinsicType(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Exp.Intrinsic.Type = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = o2 match {
        case o2: Intrinsic.Load =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhsOffset)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhsOffset = r0.resultOpt.getOrElse(o2.rhsOffset))))
          else
            TPostResult(r0.ctx, None())
        case o2: Intrinsic.Indexing =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.baseOffset)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(baseOffset = r0.resultOpt.getOrElse(o2.baseOffset), index = r1.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r1.ctx, None())
        case o2: Intrinsic.Register =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Exp.Intrinsic.Type = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = pp.post_langastIRExpIntrinsicType(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmt(ctx: Context, o: org.sireum.lang.ast.IR.Stmt): TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt] = pp.pre_langastIRStmt(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.Expr =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Apply] = transform_langastIRExpApply(preR.ctx, o2.exp)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhs = r0.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhs = r0.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.receiver)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(receiver = r0.resultOpt.getOrElse(o2.receiver), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.receiver)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.index)
          val r2: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r1.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(receiver = r0.resultOpt.getOrElse(o2.receiver), index = r1.resultOpt.getOrElse(o2.index), rhs = r2.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r2.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Decl =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          val r1: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt.Decl.Local]] = transformISZ(r0.ctx, o2.locals, transform_langastIRStmtDeclLocal _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), locals = r1.resultOpt.getOrElse(o2.locals))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = transform_langastIRStmtIntrinsicType(preR.ctx, o2.intrinsic)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(intrinsic = r0.resultOpt.getOrElse(o2.intrinsic))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assertume =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.cond)
          val r1: TPostResult[Context, Option[org.sireum.lang.ast.IR.ExpBlock]] = transformOption(r0.ctx, o2.messageOpt, transform_langastIRExpBlock _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(cond = r0.resultOpt.getOrElse(o2.cond), messageOpt = r1.resultOpt.getOrElse(o2.messageOpt))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Print =>
          val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(preR.ctx, o2.args, transform_langastIRExp _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(args = r0.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Halt =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.message)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(message = r0.resultOpt.getOrElse(o2.message))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.AssignPattern =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Block =>
          val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt]] = transformISZ(preR.ctx, o2.stmts, transform_langastIRStmt _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(stmts = r0.resultOpt.getOrElse(o2.stmts))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.If =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.cond)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(r0.ctx, o2.thenBlock)
          val r2: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(r1.ctx, o2.elseBlock)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(cond = r0.resultOpt.getOrElse(o2.cond), thenBlock = r1.resultOpt.getOrElse(o2.thenBlock), elseBlock = r2.resultOpt.getOrElse(o2.elseBlock))))
          else
            TPostResult(r2.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Match =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.exp)
          val r1: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt.Match.Case]] = transformISZ(r0.ctx, o2.cases, transform_langastIRStmtMatchCase _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp), cases = r1.resultOpt.getOrElse(o2.cases))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.While =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.ExpBlock] = transform_langastIRExpBlock(preR.ctx, o2.cond)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(r0.ctx, o2.block)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(cond = r0.resultOpt.getOrElse(o2.cond), block = r1.resultOpt.getOrElse(o2.block))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.For =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = transform_langastIRStmtForRange(r0.ctx, o2.range)
          val r2: TPostResult[Context, Option[org.sireum.lang.ast.IR.ExpBlock]] = transformOption(r1.ctx, o2.condOpt, transform_langastIRExpBlock _)
          val r3: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(r2.ctx, o2.block)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty || r3.resultOpt.nonEmpty)
            TPostResult(r3.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), range = r1.resultOpt.getOrElse(o2.range), condOpt = r2.resultOpt.getOrElse(o2.condOpt), block = r3.resultOpt.getOrElse(o2.block))))
          else
            TPostResult(r3.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Return =>
          val r0: TPostResult[Context, Option[org.sireum.lang.ast.IR.Exp]] = transformOption(preR.ctx, o2.expOpt, transform_langastIRExp _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(expOpt = r0.resultOpt.getOrElse(o2.expOpt))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt] = pp.post_langastIRStmt(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtGround(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Ground): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = pp.pre_langastIRStmtGround(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Ground = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.Expr =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Apply] = transform_langastIRExpApply(preR.ctx, o2.exp)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhs = r0.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhs = r0.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.receiver)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(receiver = r0.resultOpt.getOrElse(o2.receiver), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.receiver)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.index)
          val r2: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r1.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(receiver = r0.resultOpt.getOrElse(o2.receiver), index = r1.resultOpt.getOrElse(o2.index), rhs = r2.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r2.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Decl =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          val r1: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt.Decl.Local]] = transformISZ(r0.ctx, o2.locals, transform_langastIRStmtDeclLocal _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), locals = r1.resultOpt.getOrElse(o2.locals))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = transform_langastIRStmtIntrinsicType(preR.ctx, o2.intrinsic)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(intrinsic = r0.resultOpt.getOrElse(o2.intrinsic))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Ground = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Ground] = pp.post_langastIRStmtGround(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtAssign(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Assign): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = pp.pre_langastIRStmtAssign(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Assign = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhs = r0.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhs = r0.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.receiver)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(receiver = r0.resultOpt.getOrElse(o2.receiver), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.receiver)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.index)
          val r2: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r1.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(receiver = r0.resultOpt.getOrElse(o2.receiver), index = r1.resultOpt.getOrElse(o2.index), rhs = r2.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r2.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Assign = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Assign] = pp.post_langastIRStmtAssign(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtDeclLocal(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Decl.Local): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl.Local] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Decl.Local] = pp.pre_langastIRStmtDeclLocal(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl.Local] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Decl.Local = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Decl.Local = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl.Local] = pp.post_langastIRStmtDeclLocal(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = pp.pre_langastIRStmtIntrinsicType(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = o2 match {
        case o2: Intrinsic.TempLoad =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.rhsOffset)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(rhsOffset = r0.resultOpt.getOrElse(o2.rhsOffset))))
          else
            TPostResult(r0.ctx, None())
        case o2: Intrinsic.Store =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.lhsOffset)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(lhsOffset = r0.resultOpt.getOrElse(o2.lhsOffset), rhs = r1.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r1.ctx, None())
        case o2: Intrinsic.Copy =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.lhsOffset)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.rhsBytes)
          val r2: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r1.ctx, o2.rhs)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(lhsOffset = r0.resultOpt.getOrElse(o2.lhsOffset), rhsBytes = r1.resultOpt.getOrElse(o2.rhsBytes), rhs = r2.resultOpt.getOrElse(o2.rhs))))
          else
            TPostResult(r2.ctx, None())
        case o2: Intrinsic.Decl =>
          val r0: TPostResult[Context, IS[Z, Intrinsic.Decl.Local]] = transformISZ(preR.ctx, o2.slots, transformIntrinsicDeclLocal _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(slots = r0.resultOpt.getOrElse(o2.slots))))
          else
            TPostResult(r0.ctx, None())
        case o2: Intrinsic.RegisterAssign =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(value = r0.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = pp.post_langastIRStmtIntrinsicType(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtMatchCase(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Match.Case): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Match.Case] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Match.Case] = pp.pre_langastIRStmtMatchCase(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Match.Case] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Match.Case = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl] = transform_langastIRStmtDecl(preR.ctx, o2.decl)
      val r1: TPostResult[Context, Option[org.sireum.lang.ast.IR.ExpBlock]] = transformOption(r0.ctx, o2.condOpt, transform_langastIRExpBlock _)
      val r2: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(r1.ctx, o2.body)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
        TPostResult(r2.ctx, Some(o2(decl = r0.resultOpt.getOrElse(o2.decl), condOpt = r1.resultOpt.getOrElse(o2.condOpt), body = r2.resultOpt.getOrElse(o2.body))))
      else
        TPostResult(r2.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Match.Case = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Match.Case] = pp.post_langastIRStmtMatchCase(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtForRange(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.For.Range): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = pp.pre_langastIRStmtForRange(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.For.Range = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.For.Range.Expr =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.exp)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Stmt.For.Range.Step =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.start)
          val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.end)
          val r2: TPostResult[Context, Option[org.sireum.lang.ast.IR.Exp]] = transformOption(r1.ctx, o2.byOpt, transform_langastIRExp _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(start = r0.resultOpt.getOrElse(o2.start), end = r1.resultOpt.getOrElse(o2.end), byOpt = r2.resultOpt.getOrElse(o2.byOpt))))
          else
            TPostResult(r2.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.For.Range = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.For.Range] = pp.post_langastIRStmtForRange(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRJump(ctx: Context, o: org.sireum.lang.ast.IR.Jump): TPostResult[Context, org.sireum.lang.ast.IR.Jump] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Jump] = pp.pre_langastIRJump(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Jump] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Jump = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Jump] = o2 match {
        case o2: org.sireum.lang.ast.IR.Jump.Goto =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Jump.If =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.cond)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(cond = r0.resultOpt.getOrElse(o2.cond))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Jump.Return =>
          val r0: TPostResult[Context, Option[org.sireum.lang.ast.IR.Exp]] = transformOption(preR.ctx, o2.expOpt, transform_langastIRExp _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(expOpt = r0.resultOpt.getOrElse(o2.expOpt))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Jump.Switch =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.exp)
          val r1: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Jump.Switch.Case]] = transformISZ(r0.ctx, o2.cases, transform_langastIRJumpSwitchCase _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(exp = r0.resultOpt.getOrElse(o2.exp), cases = r1.resultOpt.getOrElse(o2.cases))))
          else
            TPostResult(r1.ctx, None())
        case o2: org.sireum.lang.ast.IR.Jump.Halt =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: org.sireum.lang.ast.IR.Jump.Intrinsic =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = transform_langastIRJumpIntrinsicType(preR.ctx, o2.intrinsic)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(intrinsic = r0.resultOpt.getOrElse(o2.intrinsic))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Jump = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Jump] = pp.post_langastIRJump(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRJumpSwitchCase(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Switch.Case): TPostResult[Context, org.sireum.lang.ast.IR.Jump.Switch.Case] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Jump.Switch.Case] = pp.pre_langastIRJumpSwitchCase(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Jump.Switch.Case] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Jump.Switch.Case = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(preR.ctx, o2.value)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(value = r0.resultOpt.getOrElse(o2.value))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Jump.Switch.Case = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Jump.Switch.Case] = pp.post_langastIRJumpSwitchCase(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRJumpIntrinsicType(ctx: Context, o: org.sireum.lang.ast.IR.Jump.Intrinsic.Type): TPostResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = pp.pre_langastIRJumpIntrinsicType(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Jump.Intrinsic.Type = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = o2 match {
        case o2: Intrinsic.GotoLocal =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Jump.Intrinsic.Type = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = pp.post_langastIRJumpIntrinsicType(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRExpBlock(ctx: Context, o: org.sireum.lang.ast.IR.ExpBlock): TPostResult[Context, org.sireum.lang.ast.IR.ExpBlock] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.ExpBlock] = pp.pre_langastIRExpBlock(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.ExpBlock] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.ExpBlock = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt]] = transformISZ(preR.ctx, o2.stmts, transform_langastIRStmt _)
      val r1: TPostResult[Context, org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(r0.ctx, o2.exp)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
        TPostResult(r1.ctx, Some(o2(stmts = r0.resultOpt.getOrElse(o2.stmts), exp = r1.resultOpt.getOrElse(o2.exp))))
      else
        TPostResult(r1.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.ExpBlock = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.ExpBlock] = pp.post_langastIRExpBlock(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRBasicBlock(ctx: Context, o: org.sireum.lang.ast.IR.BasicBlock): TPostResult[Context, org.sireum.lang.ast.IR.BasicBlock] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.BasicBlock] = pp.pre_langastIRBasicBlock(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.BasicBlock] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.BasicBlock = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt.Ground]] = transformISZ(preR.ctx, o2.grounds, transform_langastIRStmtGround _)
      val r1: TPostResult[Context, org.sireum.lang.ast.IR.Jump] = transform_langastIRJump(r0.ctx, o2.jump)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
        TPostResult(r1.ctx, Some(o2(grounds = r0.resultOpt.getOrElse(o2.grounds), jump = r1.resultOpt.getOrElse(o2.jump))))
      else
        TPostResult(r1.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.BasicBlock = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.BasicBlock] = pp.post_langastIRBasicBlock(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRBody(ctx: Context, o: org.sireum.lang.ast.IR.Body): TPostResult[Context, org.sireum.lang.ast.IR.Body] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Body] = pp.pre_langastIRBody(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Body] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Body = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Body] = o2 match {
        case o2: org.sireum.lang.ast.IR.Body.Block =>
          val r0: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(preR.ctx, o2.block)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(block = r0.resultOpt.getOrElse(o2.block))))
          else
            TPostResult(r0.ctx, None())
        case o2: org.sireum.lang.ast.IR.Body.Basic =>
          val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.BasicBlock]] = transformISZ(preR.ctx, o2.blocks, transform_langastIRBasicBlock _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(blocks = r0.resultOpt.getOrElse(o2.blocks))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Body = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Body] = pp.post_langastIRBody(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRProcedure(ctx: Context, o: org.sireum.lang.ast.IR.Procedure): TPostResult[Context, org.sireum.lang.ast.IR.Procedure] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Procedure] = pp.pre_langastIRProcedure(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Procedure] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Procedure = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.Body] = transform_langastIRBody(preR.ctx, o2.body)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(body = r0.resultOpt.getOrElse(o2.body))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Procedure = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Procedure] = pp.post_langastIRProcedure(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRGlobal(ctx: Context, o: org.sireum.lang.ast.IR.Global): TPostResult[Context, org.sireum.lang.ast.IR.Global] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Global] = pp.pre_langastIRGlobal(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Global] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Global = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Global = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Global] = pp.post_langastIRGlobal(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRProgram(ctx: Context, o: org.sireum.lang.ast.IR.Program): TPostResult[Context, org.sireum.lang.ast.IR.Program] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Program] = pp.pre_langastIRProgram(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Program] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Program = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Global]] = transformISZ(preR.ctx, o2.globals, transform_langastIRGlobal _)
      val r1: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Procedure]] = transformISZ(r0.ctx, o2.procedures, transform_langastIRProcedure _)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
        TPostResult(r1.ctx, Some(o2(globals = r0.resultOpt.getOrElse(o2.globals), procedures = r1.resultOpt.getOrElse(o2.procedures))))
      else
        TPostResult(r1.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Program = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Program] = pp.post_langastIRProgram(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRPrinter(ctx: Context, o: org.sireum.lang.ast.IR.Printer): TPostResult[Context, org.sireum.lang.ast.IR.Printer] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Printer] = pp.pre_langastIRPrinter(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Printer] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Printer = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, org.sireum.lang.ast.IR.Printer] = o2 match {
        case o2: org.sireum.lang.ast.IR.Printer.Empty =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Printer = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Printer] = pp.post_langastIRPrinter(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRPrinterEmpty(ctx: Context, o: org.sireum.lang.ast.IR.Printer.Empty): TPostResult[Context, org.sireum.lang.ast.IR.Printer.Empty] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Printer.Empty] = pp.pre_langastIRPrinterEmpty(ctx, o)
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Printer.Empty] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Printer.Empty = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Printer.Empty = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Printer.Empty] = pp.post_langastIRPrinterEmpty(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRExpApply(ctx: Context, o: org.sireum.lang.ast.IR.Exp.Apply): TPostResult[Context, org.sireum.lang.ast.IR.Exp.Apply] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Exp.Apply] = pp.pre_langastIRExpApply(ctx, o) match {
     case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Exp.Apply)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Exp.Apply](r))
     case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Apply")
     case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Exp.Apply]())
    }
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Apply] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Exp.Apply = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(preR.ctx, o2.args, transform_langastIRExp _)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(args = r0.resultOpt.getOrElse(o2.args))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Exp.Apply = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Exp.Apply] = pp.post_langastIRExpApply(r.ctx, o2) match {
     case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Exp.Apply)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Exp.Apply](result))
     case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Apply")
     case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Exp.Apply]())
    }
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtBlock(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Block): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = pp.pre_langastIRStmtBlock(ctx, o) match {
     case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Block)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Block](r))
     case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Block")
     case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Block]())
    }
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Block = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt]] = transformISZ(preR.ctx, o2.stmts, transform_langastIRStmt _)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(stmts = r0.resultOpt.getOrElse(o2.stmts))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Block = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Block] = pp.post_langastIRStmtBlock(r.ctx, o2) match {
     case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Block)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Block](result))
     case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Block")
     case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Block]())
    }
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transform_langastIRStmtDecl(ctx: Context, o: org.sireum.lang.ast.IR.Stmt.Decl): TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl] = {
    val preR: PreResult[Context, org.sireum.lang.ast.IR.Stmt.Decl] = pp.pre_langastIRStmtDecl(ctx, o) match {
     case PreResult(preCtx, continu, Some(r: org.sireum.lang.ast.IR.Stmt.Decl)) => PreResult(preCtx, continu, Some[org.sireum.lang.ast.IR.Stmt.Decl](r))
     case PreResult(_, _, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Decl")
     case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[org.sireum.lang.ast.IR.Stmt.Decl]())
    }
    val r: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Decl = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(preR.ctx, o2.context)
      val r1: TPostResult[Context, IS[Z, org.sireum.lang.ast.IR.Stmt.Decl.Local]] = transformISZ(r0.ctx, o2.locals, transform_langastIRStmtDeclLocal _)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
        TPostResult(r1.ctx, Some(o2(context = r0.resultOpt.getOrElse(o2.context), locals = r1.resultOpt.getOrElse(o2.locals))))
      else
        TPostResult(r1.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Decl = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, org.sireum.lang.ast.IR.Stmt.Decl] = pp.post_langastIRStmtDecl(r.ctx, o2) match {
     case TPostResult(postCtx, Some(result: org.sireum.lang.ast.IR.Stmt.Decl)) => TPostResult(postCtx, Some[org.sireum.lang.ast.IR.Stmt.Decl](result))
     case TPostResult(_, Some(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Decl")
     case TPostResult(postCtx, _) => TPostResult(postCtx, None[org.sireum.lang.ast.IR.Stmt.Decl]())
    }
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

}