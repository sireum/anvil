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

// This file is auto-generated from Intrinsic.scala, IR.scala

package org.sireum.anvil

import org.sireum._

object MAnvilIRTransformer {

  @record class PreResult[T](val continu: B,
                             val resultOpt: MOption[T])

  val PreResult_langastIRMethodContext: PreResult[org.sireum.lang.ast.IR.MethodContext] = PreResult(T, MNone())

  val PostResult_langastIRMethodContext: MOption[org.sireum.lang.ast.IR.MethodContext] = MNone()

  val PreResultIntrinsicTempLoad: PreResult[Intrinsic.TempLoad] = PreResult(T, MNone())

  val PostResultIntrinsicTempLoad: MOption[Intrinsic.TempLoad] = MNone()

  def transformISZ[T](s: IS[Z, T], f: T => MOption[T]): MOption[IS[Z, T]] = {
    val s2: MS[Z, T] = s.toMS
    var changed: B = F
    for (i <- s2.indices) {
      val e: T = s(i)
      val r: MOption[T] = f(e)
      changed = changed || r.nonEmpty
      s2(i) = r.getOrElse(e)
    }
    if (changed) {
      return MSome(s2.toIS)
    } else {
      return MNone()
    }
  }

  val PreResult_langastIRExpBool: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpBool: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpInt: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpInt: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpF32: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpF32: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResultIntrinsicLoad: PreResult[Intrinsic.Load] = PreResult(T, MNone())

  val PostResultIntrinsicLoad: MOption[Intrinsic.Load] = MNone()

  val PreResult_langastIRExpF64: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpF64: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpR: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpR: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpString: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpString: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResultIntrinsicIndexing: PreResult[Intrinsic.Indexing] = PreResult(T, MNone())

  val PostResultIntrinsicIndexing: MOption[Intrinsic.Indexing] = MNone()

  val PreResult_langastIRExpTemp: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpTemp: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpLocalVarRef: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpLocalVarRef: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpGlobalVarRef: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpGlobalVarRef: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResultIntrinsicStore: PreResult[Intrinsic.Store] = PreResult(T, MNone())

  val PostResultIntrinsicStore: MOption[Intrinsic.Store] = MNone()

  val PreResult_langastIRExpEnumElementRef: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpEnumElementRef: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpFieldVarRef: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpFieldVarRef: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpUnary: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpUnary: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResultIntrinsicCopy: PreResult[Intrinsic.Copy] = PreResult(T, MNone())

  val PostResultIntrinsicCopy: MOption[Intrinsic.Copy] = MNone()

  val PreResult_langastIRExpBinary: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpBinary: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResultIntrinsicDecl: PreResult[Intrinsic.Decl] = PreResult(T, MNone())

  val PostResultIntrinsicDecl: MOption[Intrinsic.Decl] = MNone()

  val PreResultIntrinsicDeclLocal: PreResult[Intrinsic.Decl.Local] = PreResult(T, MNone())

  val PostResultIntrinsicDeclLocal: MOption[Intrinsic.Decl.Local] = MNone()

  val PreResultIntrinsicRegister: PreResult[Intrinsic.Register] = PreResult(T, MNone())

  val PostResultIntrinsicRegister: MOption[Intrinsic.Register] = MNone()

  val PreResultIntrinsicRegisterAssign: PreResult[Intrinsic.RegisterAssign] = PreResult(T, MNone())

  val PostResultIntrinsicRegisterAssign: MOption[Intrinsic.RegisterAssign] = MNone()

  val PreResult_langastIRExpIf: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpIf: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResultIntrinsicGotoLocal: PreResult[Intrinsic.GotoLocal] = PreResult(T, MNone())

  val PostResultIntrinsicGotoLocal: MOption[Intrinsic.GotoLocal] = MNone()

  def transformOption[T](option: Option[T], f: T => MOption[T]): MOption[Option[T]] = {
    option match {
      case Some(v) =>
        val r = f(v)
        r match {
          case MSome(v2) => return MSome(Some(v2))
          case _ => return MNone()
        }
      case _ => return MNone()
    }
  }

  val PreResult_langastIRExpConstruct: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpConstruct: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpApply: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpApply: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpIndexing: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpIndexing: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpType: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpType: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRExpIntrinsic: PreResult[org.sireum.lang.ast.IR.Exp] = PreResult(T, MNone())

  val PostResult_langastIRExpIntrinsic: MOption[org.sireum.lang.ast.IR.Exp] = MNone()

  val PreResult_langastIRStmtExpr: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = PreResult(T, MNone())

  val PostResult_langastIRStmtExpr: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = MNone()

  val PreResult_langastIRStmtAssignLocal: PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = PreResult(T, MNone())

  val PostResult_langastIRStmtAssignLocal: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = MNone()

  val PreResult_langastIRStmtAssignGlobal: PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = PreResult(T, MNone())

  val PostResult_langastIRStmtAssignGlobal: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = MNone()

  val PreResult_langastIRStmtAssignTemp: PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = PreResult(T, MNone())

  val PostResult_langastIRStmtAssignTemp: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = MNone()

  val PreResult_langastIRStmtAssignField: PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = PreResult(T, MNone())

  val PostResult_langastIRStmtAssignField: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = MNone()

  val PreResult_langastIRStmtAssignIndex: PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = PreResult(T, MNone())

  val PostResult_langastIRStmtAssignIndex: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = MNone()

  val PreResult_langastIRStmtDecl: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = PreResult(T, MNone())

  val PostResult_langastIRStmtDecl: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = MNone()

  val PreResult_langastIRStmtDeclLocal: PreResult[org.sireum.lang.ast.IR.Stmt.Decl.Local] = PreResult(T, MNone())

  val PostResult_langastIRStmtDeclLocal: MOption[org.sireum.lang.ast.IR.Stmt.Decl.Local] = MNone()

  val PreResult_langastIRStmtIntrinsic: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = PreResult(T, MNone())

  val PostResult_langastIRStmtIntrinsic: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = MNone()

  val PreResult_langastIRStmtAssertume: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtAssertume: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtPrint: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtPrint: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtHalt: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtHalt: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtAssignPattern: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtAssignPattern: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtBlock: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtBlock: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtIf: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtIf: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtMatch: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtMatch: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtMatchCase: PreResult[org.sireum.lang.ast.IR.Stmt.Match.Case] = PreResult(T, MNone())

  val PostResult_langastIRStmtMatchCase: MOption[org.sireum.lang.ast.IR.Stmt.Match.Case] = MNone()

  val PreResult_langastIRStmtWhile: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtWhile: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtFor: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtFor: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRStmtForRangeExpr: PreResult[org.sireum.lang.ast.IR.Stmt.For.Range] = PreResult(T, MNone())

  val PostResult_langastIRStmtForRangeExpr: MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = MNone()

  val PreResult_langastIRStmtForRangeStep: PreResult[org.sireum.lang.ast.IR.Stmt.For.Range] = PreResult(T, MNone())

  val PostResult_langastIRStmtForRangeStep: MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = MNone()

  val PreResult_langastIRStmtReturn: PreResult[org.sireum.lang.ast.IR.Stmt] = PreResult(T, MNone())

  val PostResult_langastIRStmtReturn: MOption[org.sireum.lang.ast.IR.Stmt] = MNone()

  val PreResult_langastIRJumpGoto: PreResult[org.sireum.lang.ast.IR.Jump] = PreResult(T, MNone())

  val PostResult_langastIRJumpGoto: MOption[org.sireum.lang.ast.IR.Jump] = MNone()

  val PreResult_langastIRJumpIf: PreResult[org.sireum.lang.ast.IR.Jump] = PreResult(T, MNone())

  val PostResult_langastIRJumpIf: MOption[org.sireum.lang.ast.IR.Jump] = MNone()

  val PreResult_langastIRJumpReturn: PreResult[org.sireum.lang.ast.IR.Jump] = PreResult(T, MNone())

  val PostResult_langastIRJumpReturn: MOption[org.sireum.lang.ast.IR.Jump] = MNone()

  val PreResult_langastIRJumpSwitch: PreResult[org.sireum.lang.ast.IR.Jump] = PreResult(T, MNone())

  val PostResult_langastIRJumpSwitch: MOption[org.sireum.lang.ast.IR.Jump] = MNone()

  val PreResult_langastIRJumpSwitchCase: PreResult[org.sireum.lang.ast.IR.Jump.Switch.Case] = PreResult(T, MNone())

  val PostResult_langastIRJumpSwitchCase: MOption[org.sireum.lang.ast.IR.Jump.Switch.Case] = MNone()

  val PreResult_langastIRJumpHalt: PreResult[org.sireum.lang.ast.IR.Jump] = PreResult(T, MNone())

  val PostResult_langastIRJumpHalt: MOption[org.sireum.lang.ast.IR.Jump] = MNone()

  val PreResult_langastIRJumpIntrinsic: PreResult[org.sireum.lang.ast.IR.Jump] = PreResult(T, MNone())

  val PostResult_langastIRJumpIntrinsic: MOption[org.sireum.lang.ast.IR.Jump] = MNone()

  val PreResult_langastIRExpBlock: PreResult[org.sireum.lang.ast.IR.ExpBlock] = PreResult(T, MNone())

  val PostResult_langastIRExpBlock: MOption[org.sireum.lang.ast.IR.ExpBlock] = MNone()

  val PreResult_langastIRBasicBlock: PreResult[org.sireum.lang.ast.IR.BasicBlock] = PreResult(T, MNone())

  val PostResult_langastIRBasicBlock: MOption[org.sireum.lang.ast.IR.BasicBlock] = MNone()

  val PreResult_langastIRBodyBlock: PreResult[org.sireum.lang.ast.IR.Body] = PreResult(T, MNone())

  val PostResult_langastIRBodyBlock: MOption[org.sireum.lang.ast.IR.Body] = MNone()

  val PreResult_langastIRBodyBasic: PreResult[org.sireum.lang.ast.IR.Body] = PreResult(T, MNone())

  val PostResult_langastIRBodyBasic: MOption[org.sireum.lang.ast.IR.Body] = MNone()

  val PreResult_langastIRProcedure: PreResult[org.sireum.lang.ast.IR.Procedure] = PreResult(T, MNone())

  val PostResult_langastIRProcedure: MOption[org.sireum.lang.ast.IR.Procedure] = MNone()

  val PreResult_langastIRGlobal: PreResult[org.sireum.lang.ast.IR.Global] = PreResult(T, MNone())

  val PostResult_langastIRGlobal: MOption[org.sireum.lang.ast.IR.Global] = MNone()

  val PreResult_langastIRProgram: PreResult[org.sireum.lang.ast.IR.Program] = PreResult(T, MNone())

  val PostResult_langastIRProgram: MOption[org.sireum.lang.ast.IR.Program] = MNone()

  val PreResult_langastIRPrinterEmpty: PreResult[org.sireum.lang.ast.IR.Printer.Empty] = PreResult(T, MNone())

  val PostResult_langastIRPrinterEmpty: MOption[org.sireum.lang.ast.IR.Printer.Empty] = MNone()

}

import MAnvilIRTransformer._

@msig trait MAnvilIRTransformer {

  def pre_langastIRMethodContext(o: org.sireum.lang.ast.IR.MethodContext): PreResult[org.sireum.lang.ast.IR.MethodContext] = {
    return PreResult_langastIRMethodContext
  }

  def preIntrinsicTempLoad(o: Intrinsic.TempLoad): PreResult[Intrinsic.TempLoad] = {
    return PreResultIntrinsicTempLoad
  }

  def pre_langastIRExp(o: org.sireum.lang.ast.IR.Exp): PreResult[org.sireum.lang.ast.IR.Exp] = {
    o match {
      case o: org.sireum.lang.ast.IR.Exp.Bool => return pre_langastIRExpBool(o)
      case o: org.sireum.lang.ast.IR.Exp.Int => return pre_langastIRExpInt(o)
      case o: org.sireum.lang.ast.IR.Exp.F32 => return pre_langastIRExpF32(o)
      case o: org.sireum.lang.ast.IR.Exp.F64 => return pre_langastIRExpF64(o)
      case o: org.sireum.lang.ast.IR.Exp.R => return pre_langastIRExpR(o)
      case o: org.sireum.lang.ast.IR.Exp.String => return pre_langastIRExpString(o)
      case o: org.sireum.lang.ast.IR.Exp.Temp => return pre_langastIRExpTemp(o)
      case o: org.sireum.lang.ast.IR.Exp.LocalVarRef => return pre_langastIRExpLocalVarRef(o)
      case o: org.sireum.lang.ast.IR.Exp.GlobalVarRef => return pre_langastIRExpGlobalVarRef(o)
      case o: org.sireum.lang.ast.IR.Exp.EnumElementRef => return pre_langastIRExpEnumElementRef(o)
      case o: org.sireum.lang.ast.IR.Exp.FieldVarRef => return pre_langastIRExpFieldVarRef(o)
      case o: org.sireum.lang.ast.IR.Exp.Unary => return pre_langastIRExpUnary(o)
      case o: org.sireum.lang.ast.IR.Exp.Binary => return pre_langastIRExpBinary(o)
      case o: org.sireum.lang.ast.IR.Exp.If => return pre_langastIRExpIf(o)
      case o: org.sireum.lang.ast.IR.Exp.Construct => return pre_langastIRExpConstruct(o)
      case o: org.sireum.lang.ast.IR.Exp.Apply => return pre_langastIRExpApply(o)
      case o: org.sireum.lang.ast.IR.Exp.Indexing => return pre_langastIRExpIndexing(o)
      case o: org.sireum.lang.ast.IR.Exp.Type => return pre_langastIRExpType(o)
      case o: org.sireum.lang.ast.IR.Exp.Intrinsic => return pre_langastIRExpIntrinsic(o)
    }
  }

  def pre_langastIRExpBool(o: org.sireum.lang.ast.IR.Exp.Bool): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpBool
  }

  def pre_langastIRExpInt(o: org.sireum.lang.ast.IR.Exp.Int): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpInt
  }

  def pre_langastIRExpF32(o: org.sireum.lang.ast.IR.Exp.F32): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpF32
  }

  def preIntrinsicLoad(o: Intrinsic.Load): PreResult[Intrinsic.Load] = {
    return PreResultIntrinsicLoad
  }

  def pre_langastIRExpF64(o: org.sireum.lang.ast.IR.Exp.F64): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpF64
  }

  def pre_langastIRExpR(o: org.sireum.lang.ast.IR.Exp.R): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpR
  }

  def pre_langastIRExpString(o: org.sireum.lang.ast.IR.Exp.String): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpString
  }

  def preIntrinsicIndexing(o: Intrinsic.Indexing): PreResult[Intrinsic.Indexing] = {
    return PreResultIntrinsicIndexing
  }

  def pre_langastIRExpTemp(o: org.sireum.lang.ast.IR.Exp.Temp): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpTemp
  }

  def pre_langastIRExpLocalVarRef(o: org.sireum.lang.ast.IR.Exp.LocalVarRef): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpLocalVarRef
  }

  def pre_langastIRExpGlobalVarRef(o: org.sireum.lang.ast.IR.Exp.GlobalVarRef): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpGlobalVarRef
  }

  def preIntrinsicStore(o: Intrinsic.Store): PreResult[Intrinsic.Store] = {
    return PreResultIntrinsicStore
  }

  def pre_langastIRExpEnumElementRef(o: org.sireum.lang.ast.IR.Exp.EnumElementRef): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpEnumElementRef
  }

  def pre_langastIRExpFieldVarRef(o: org.sireum.lang.ast.IR.Exp.FieldVarRef): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpFieldVarRef
  }

  def pre_langastIRExpUnary(o: org.sireum.lang.ast.IR.Exp.Unary): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpUnary
  }

  def preIntrinsicCopy(o: Intrinsic.Copy): PreResult[Intrinsic.Copy] = {
    return PreResultIntrinsicCopy
  }

  def pre_langastIRExpBinary(o: org.sireum.lang.ast.IR.Exp.Binary): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpBinary
  }

  def preIntrinsicDecl(o: Intrinsic.Decl): PreResult[Intrinsic.Decl] = {
    return PreResultIntrinsicDecl
  }

  def preIntrinsicDeclLocal(o: Intrinsic.Decl.Local): PreResult[Intrinsic.Decl.Local] = {
    return PreResultIntrinsicDeclLocal
  }

  def preIntrinsicRegister(o: Intrinsic.Register): PreResult[Intrinsic.Register] = {
    return PreResultIntrinsicRegister
  }

  def preIntrinsicRegisterAssign(o: Intrinsic.RegisterAssign): PreResult[Intrinsic.RegisterAssign] = {
    return PreResultIntrinsicRegisterAssign
  }

  def pre_langastIRExpIf(o: org.sireum.lang.ast.IR.Exp.If): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpIf
  }

  def preIntrinsicGotoLocal(o: Intrinsic.GotoLocal): PreResult[Intrinsic.GotoLocal] = {
    return PreResultIntrinsicGotoLocal
  }

  def pre_langastIRExpConstruct(o: org.sireum.lang.ast.IR.Exp.Construct): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpConstruct
  }

  def pre_langastIRExpApply(o: org.sireum.lang.ast.IR.Exp.Apply): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpApply
  }

  def pre_langastIRExpIndexing(o: org.sireum.lang.ast.IR.Exp.Indexing): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpIndexing
  }

  def pre_langastIRExpType(o: org.sireum.lang.ast.IR.Exp.Type): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpType
  }

  def pre_langastIRExpIntrinsic(o: org.sireum.lang.ast.IR.Exp.Intrinsic): PreResult[org.sireum.lang.ast.IR.Exp] = {
    return PreResult_langastIRExpIntrinsic
  }

  def pre_langastIRExpIntrinsicType(o: org.sireum.lang.ast.IR.Exp.Intrinsic.Type): PreResult[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = {
    o match {
      case o: Intrinsic.Load =>
        val r: PreResult[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = preIntrinsicLoad(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
        }
        return r
      case o: Intrinsic.Indexing =>
        val r: PreResult[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = preIntrinsicIndexing(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
        }
        return r
      case o: Intrinsic.Register =>
        val r: PreResult[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = preIntrinsicRegister(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Exp.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]())
        }
        return r
    }
  }

  def pre_langastIRStmt(o: org.sireum.lang.ast.IR.Stmt): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.Expr =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtExpr(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignLocal(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignGlobal(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignTemp(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignField(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtAssignIndex(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Decl =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtDecl(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmtIntrinsic(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assertume => return pre_langastIRStmtAssertume(o)
      case o: org.sireum.lang.ast.IR.Stmt.Print => return pre_langastIRStmtPrint(o)
      case o: org.sireum.lang.ast.IR.Stmt.Halt => return pre_langastIRStmtHalt(o)
      case o: org.sireum.lang.ast.IR.Stmt.AssignPattern => return pre_langastIRStmtAssignPattern(o)
      case o: org.sireum.lang.ast.IR.Stmt.Block => return pre_langastIRStmtBlock(o)
      case o: org.sireum.lang.ast.IR.Stmt.If => return pre_langastIRStmtIf(o)
      case o: org.sireum.lang.ast.IR.Stmt.Match => return pre_langastIRStmtMatch(o)
      case o: org.sireum.lang.ast.IR.Stmt.While => return pre_langastIRStmtWhile(o)
      case o: org.sireum.lang.ast.IR.Stmt.For => return pre_langastIRStmtFor(o)
      case o: org.sireum.lang.ast.IR.Stmt.Return => return pre_langastIRStmtReturn(o)
    }
  }

  def pre_langastIRStmtGround(o: org.sireum.lang.ast.IR.Stmt.Ground): PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.Expr => return pre_langastIRStmtExpr(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignLocal(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Ground](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Ground]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignGlobal(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Ground](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Ground]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignTemp(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Ground](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Ground]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignField(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Ground](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Ground]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtAssignIndex(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Ground)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Ground](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Ground]())
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Decl => return pre_langastIRStmtDecl(o)
      case o: org.sireum.lang.ast.IR.Stmt.Intrinsic => return pre_langastIRStmtIntrinsic(o)
    }
  }

  def pre_langastIRStmtExpr(o: org.sireum.lang.ast.IR.Stmt.Expr): PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = {
    return PreResult_langastIRStmtExpr
  }

  def pre_langastIRStmtAssign(o: org.sireum.lang.ast.IR.Stmt.Assign): PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Local => return pre_langastIRStmtAssignLocal(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Global => return pre_langastIRStmtAssignGlobal(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp => return pre_langastIRStmtAssignTemp(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Field => return pre_langastIRStmtAssignField(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Index => return pre_langastIRStmtAssignIndex(o)
    }
  }

  def pre_langastIRStmtAssignLocal(o: org.sireum.lang.ast.IR.Stmt.Assign.Local): PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PreResult_langastIRStmtAssignLocal
  }

  def pre_langastIRStmtAssignGlobal(o: org.sireum.lang.ast.IR.Stmt.Assign.Global): PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PreResult_langastIRStmtAssignGlobal
  }

  def pre_langastIRStmtAssignTemp(o: org.sireum.lang.ast.IR.Stmt.Assign.Temp): PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PreResult_langastIRStmtAssignTemp
  }

  def pre_langastIRStmtAssignField(o: org.sireum.lang.ast.IR.Stmt.Assign.Field): PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PreResult_langastIRStmtAssignField
  }

  def pre_langastIRStmtAssignIndex(o: org.sireum.lang.ast.IR.Stmt.Assign.Index): PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PreResult_langastIRStmtAssignIndex
  }

  def pre_langastIRStmtDecl(o: org.sireum.lang.ast.IR.Stmt.Decl): PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = {
    return PreResult_langastIRStmtDecl
  }

  def pre_langastIRStmtDeclLocal(o: org.sireum.lang.ast.IR.Stmt.Decl.Local): PreResult[org.sireum.lang.ast.IR.Stmt.Decl.Local] = {
    return PreResult_langastIRStmtDeclLocal
  }

  def pre_langastIRStmtIntrinsic(o: org.sireum.lang.ast.IR.Stmt.Intrinsic): PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = {
    return PreResult_langastIRStmtIntrinsic
  }

  def pre_langastIRStmtIntrinsicType(o: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type): PreResult[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = {
    o match {
      case o: Intrinsic.TempLoad =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicTempLoad(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
        }
        return r
      case o: Intrinsic.Store =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicStore(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
        }
        return r
      case o: Intrinsic.Copy =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicCopy(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
        }
        return r
      case o: Intrinsic.Decl =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicDecl(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
        }
        return r
      case o: Intrinsic.RegisterAssign =>
        val r: PreResult[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = preIntrinsicRegisterAssign(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]())
        }
        return r
    }
  }

  def pre_langastIRStmtAssertume(o: org.sireum.lang.ast.IR.Stmt.Assertume): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtAssertume
  }

  def pre_langastIRStmtPrint(o: org.sireum.lang.ast.IR.Stmt.Print): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtPrint
  }

  def pre_langastIRStmtHalt(o: org.sireum.lang.ast.IR.Stmt.Halt): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtHalt
  }

  def pre_langastIRStmtAssignPattern(o: org.sireum.lang.ast.IR.Stmt.AssignPattern): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtAssignPattern
  }

  def pre_langastIRStmtBlock(o: org.sireum.lang.ast.IR.Stmt.Block): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtBlock
  }

  def pre_langastIRStmtIf(o: org.sireum.lang.ast.IR.Stmt.If): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtIf
  }

  def pre_langastIRStmtMatch(o: org.sireum.lang.ast.IR.Stmt.Match): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtMatch
  }

  def pre_langastIRStmtMatchCase(o: org.sireum.lang.ast.IR.Stmt.Match.Case): PreResult[org.sireum.lang.ast.IR.Stmt.Match.Case] = {
    return PreResult_langastIRStmtMatchCase
  }

  def pre_langastIRStmtWhile(o: org.sireum.lang.ast.IR.Stmt.While): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtWhile
  }

  def pre_langastIRStmtFor(o: org.sireum.lang.ast.IR.Stmt.For): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtFor
  }

  def pre_langastIRStmtForRange(o: org.sireum.lang.ast.IR.Stmt.For.Range): PreResult[org.sireum.lang.ast.IR.Stmt.For.Range] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr => return pre_langastIRStmtForRangeExpr(o)
      case o: org.sireum.lang.ast.IR.Stmt.For.Range.Step => return pre_langastIRStmtForRangeStep(o)
    }
  }

  def pre_langastIRStmtForRangeExpr(o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr): PreResult[org.sireum.lang.ast.IR.Stmt.For.Range] = {
    return PreResult_langastIRStmtForRangeExpr
  }

  def pre_langastIRStmtForRangeStep(o: org.sireum.lang.ast.IR.Stmt.For.Range.Step): PreResult[org.sireum.lang.ast.IR.Stmt.For.Range] = {
    return PreResult_langastIRStmtForRangeStep
  }

  def pre_langastIRStmtReturn(o: org.sireum.lang.ast.IR.Stmt.Return): PreResult[org.sireum.lang.ast.IR.Stmt] = {
    return PreResult_langastIRStmtReturn
  }

  def pre_langastIRJump(o: org.sireum.lang.ast.IR.Jump): PreResult[org.sireum.lang.ast.IR.Jump] = {
    o match {
      case o: org.sireum.lang.ast.IR.Jump.Goto => return pre_langastIRJumpGoto(o)
      case o: org.sireum.lang.ast.IR.Jump.If => return pre_langastIRJumpIf(o)
      case o: org.sireum.lang.ast.IR.Jump.Return => return pre_langastIRJumpReturn(o)
      case o: org.sireum.lang.ast.IR.Jump.Switch => return pre_langastIRJumpSwitch(o)
      case o: org.sireum.lang.ast.IR.Jump.Halt => return pre_langastIRJumpHalt(o)
      case o: org.sireum.lang.ast.IR.Jump.Intrinsic => return pre_langastIRJumpIntrinsic(o)
    }
  }

  def pre_langastIRJumpGoto(o: org.sireum.lang.ast.IR.Jump.Goto): PreResult[org.sireum.lang.ast.IR.Jump] = {
    return PreResult_langastIRJumpGoto
  }

  def pre_langastIRJumpIf(o: org.sireum.lang.ast.IR.Jump.If): PreResult[org.sireum.lang.ast.IR.Jump] = {
    return PreResult_langastIRJumpIf
  }

  def pre_langastIRJumpReturn(o: org.sireum.lang.ast.IR.Jump.Return): PreResult[org.sireum.lang.ast.IR.Jump] = {
    return PreResult_langastIRJumpReturn
  }

  def pre_langastIRJumpSwitch(o: org.sireum.lang.ast.IR.Jump.Switch): PreResult[org.sireum.lang.ast.IR.Jump] = {
    return PreResult_langastIRJumpSwitch
  }

  def pre_langastIRJumpSwitchCase(o: org.sireum.lang.ast.IR.Jump.Switch.Case): PreResult[org.sireum.lang.ast.IR.Jump.Switch.Case] = {
    return PreResult_langastIRJumpSwitchCase
  }

  def pre_langastIRJumpHalt(o: org.sireum.lang.ast.IR.Jump.Halt): PreResult[org.sireum.lang.ast.IR.Jump] = {
    return PreResult_langastIRJumpHalt
  }

  def pre_langastIRJumpIntrinsic(o: org.sireum.lang.ast.IR.Jump.Intrinsic): PreResult[org.sireum.lang.ast.IR.Jump] = {
    return PreResult_langastIRJumpIntrinsic
  }

  def pre_langastIRJumpIntrinsicType(o: org.sireum.lang.ast.IR.Jump.Intrinsic.Type): PreResult[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = {
    o match {
      case o: Intrinsic.GotoLocal =>
        val r: PreResult[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = preIntrinsicGotoLocal(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Jump.Intrinsic.Type)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Jump.Intrinsic.Type](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Jump.Intrinsic.Type")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Jump.Intrinsic.Type]())
        }
        return r
    }
  }

  def pre_langastIRExpBlock(o: org.sireum.lang.ast.IR.ExpBlock): PreResult[org.sireum.lang.ast.IR.ExpBlock] = {
    return PreResult_langastIRExpBlock
  }

  def pre_langastIRBasicBlock(o: org.sireum.lang.ast.IR.BasicBlock): PreResult[org.sireum.lang.ast.IR.BasicBlock] = {
    return PreResult_langastIRBasicBlock
  }

  def pre_langastIRBody(o: org.sireum.lang.ast.IR.Body): PreResult[org.sireum.lang.ast.IR.Body] = {
    o match {
      case o: org.sireum.lang.ast.IR.Body.Block => return pre_langastIRBodyBlock(o)
      case o: org.sireum.lang.ast.IR.Body.Basic => return pre_langastIRBodyBasic(o)
    }
  }

  def pre_langastIRBodyBlock(o: org.sireum.lang.ast.IR.Body.Block): PreResult[org.sireum.lang.ast.IR.Body] = {
    return PreResult_langastIRBodyBlock
  }

  def pre_langastIRBodyBasic(o: org.sireum.lang.ast.IR.Body.Basic): PreResult[org.sireum.lang.ast.IR.Body] = {
    return PreResult_langastIRBodyBasic
  }

  def pre_langastIRProcedure(o: org.sireum.lang.ast.IR.Procedure): PreResult[org.sireum.lang.ast.IR.Procedure] = {
    return PreResult_langastIRProcedure
  }

  def pre_langastIRGlobal(o: org.sireum.lang.ast.IR.Global): PreResult[org.sireum.lang.ast.IR.Global] = {
    return PreResult_langastIRGlobal
  }

  def pre_langastIRProgram(o: org.sireum.lang.ast.IR.Program): PreResult[org.sireum.lang.ast.IR.Program] = {
    return PreResult_langastIRProgram
  }

  def pre_langastIRPrinter(o: org.sireum.lang.ast.IR.Printer): PreResult[org.sireum.lang.ast.IR.Printer] = {
    o match {
      case o: org.sireum.lang.ast.IR.Printer.Empty =>
        val r: PreResult[org.sireum.lang.ast.IR.Printer] = pre_langastIRPrinterEmpty(o) match {
         case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Printer)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Printer](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Printer")
         case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Printer]())
        }
        return r
    }
  }

  def pre_langastIRPrinterEmpty(o: org.sireum.lang.ast.IR.Printer.Empty): PreResult[org.sireum.lang.ast.IR.Printer.Empty] = {
    return PreResult_langastIRPrinterEmpty
  }

  def post_langastIRMethodContext(o: org.sireum.lang.ast.IR.MethodContext): MOption[org.sireum.lang.ast.IR.MethodContext] = {
    return PostResult_langastIRMethodContext
  }

  def postIntrinsicTempLoad(o: Intrinsic.TempLoad): MOption[Intrinsic.TempLoad] = {
    return PostResultIntrinsicTempLoad
  }

  def post_langastIRExp(o: org.sireum.lang.ast.IR.Exp): MOption[org.sireum.lang.ast.IR.Exp] = {
    o match {
      case o: org.sireum.lang.ast.IR.Exp.Bool => return post_langastIRExpBool(o)
      case o: org.sireum.lang.ast.IR.Exp.Int => return post_langastIRExpInt(o)
      case o: org.sireum.lang.ast.IR.Exp.F32 => return post_langastIRExpF32(o)
      case o: org.sireum.lang.ast.IR.Exp.F64 => return post_langastIRExpF64(o)
      case o: org.sireum.lang.ast.IR.Exp.R => return post_langastIRExpR(o)
      case o: org.sireum.lang.ast.IR.Exp.String => return post_langastIRExpString(o)
      case o: org.sireum.lang.ast.IR.Exp.Temp => return post_langastIRExpTemp(o)
      case o: org.sireum.lang.ast.IR.Exp.LocalVarRef => return post_langastIRExpLocalVarRef(o)
      case o: org.sireum.lang.ast.IR.Exp.GlobalVarRef => return post_langastIRExpGlobalVarRef(o)
      case o: org.sireum.lang.ast.IR.Exp.EnumElementRef => return post_langastIRExpEnumElementRef(o)
      case o: org.sireum.lang.ast.IR.Exp.FieldVarRef => return post_langastIRExpFieldVarRef(o)
      case o: org.sireum.lang.ast.IR.Exp.Unary => return post_langastIRExpUnary(o)
      case o: org.sireum.lang.ast.IR.Exp.Binary => return post_langastIRExpBinary(o)
      case o: org.sireum.lang.ast.IR.Exp.If => return post_langastIRExpIf(o)
      case o: org.sireum.lang.ast.IR.Exp.Construct => return post_langastIRExpConstruct(o)
      case o: org.sireum.lang.ast.IR.Exp.Apply => return post_langastIRExpApply(o)
      case o: org.sireum.lang.ast.IR.Exp.Indexing => return post_langastIRExpIndexing(o)
      case o: org.sireum.lang.ast.IR.Exp.Type => return post_langastIRExpType(o)
      case o: org.sireum.lang.ast.IR.Exp.Intrinsic => return post_langastIRExpIntrinsic(o)
    }
  }

  def post_langastIRExpBool(o: org.sireum.lang.ast.IR.Exp.Bool): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpBool
  }

  def post_langastIRExpInt(o: org.sireum.lang.ast.IR.Exp.Int): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpInt
  }

  def post_langastIRExpF32(o: org.sireum.lang.ast.IR.Exp.F32): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpF32
  }

  def postIntrinsicLoad(o: Intrinsic.Load): MOption[Intrinsic.Load] = {
    return PostResultIntrinsicLoad
  }

  def post_langastIRExpF64(o: org.sireum.lang.ast.IR.Exp.F64): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpF64
  }

  def post_langastIRExpR(o: org.sireum.lang.ast.IR.Exp.R): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpR
  }

  def post_langastIRExpString(o: org.sireum.lang.ast.IR.Exp.String): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpString
  }

  def postIntrinsicIndexing(o: Intrinsic.Indexing): MOption[Intrinsic.Indexing] = {
    return PostResultIntrinsicIndexing
  }

  def post_langastIRExpTemp(o: org.sireum.lang.ast.IR.Exp.Temp): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpTemp
  }

  def post_langastIRExpLocalVarRef(o: org.sireum.lang.ast.IR.Exp.LocalVarRef): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpLocalVarRef
  }

  def post_langastIRExpGlobalVarRef(o: org.sireum.lang.ast.IR.Exp.GlobalVarRef): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpGlobalVarRef
  }

  def postIntrinsicStore(o: Intrinsic.Store): MOption[Intrinsic.Store] = {
    return PostResultIntrinsicStore
  }

  def post_langastIRExpEnumElementRef(o: org.sireum.lang.ast.IR.Exp.EnumElementRef): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpEnumElementRef
  }

  def post_langastIRExpFieldVarRef(o: org.sireum.lang.ast.IR.Exp.FieldVarRef): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpFieldVarRef
  }

  def post_langastIRExpUnary(o: org.sireum.lang.ast.IR.Exp.Unary): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpUnary
  }

  def postIntrinsicCopy(o: Intrinsic.Copy): MOption[Intrinsic.Copy] = {
    return PostResultIntrinsicCopy
  }

  def post_langastIRExpBinary(o: org.sireum.lang.ast.IR.Exp.Binary): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpBinary
  }

  def postIntrinsicDecl(o: Intrinsic.Decl): MOption[Intrinsic.Decl] = {
    return PostResultIntrinsicDecl
  }

  def postIntrinsicDeclLocal(o: Intrinsic.Decl.Local): MOption[Intrinsic.Decl.Local] = {
    return PostResultIntrinsicDeclLocal
  }

  def postIntrinsicRegister(o: Intrinsic.Register): MOption[Intrinsic.Register] = {
    return PostResultIntrinsicRegister
  }

  def postIntrinsicRegisterAssign(o: Intrinsic.RegisterAssign): MOption[Intrinsic.RegisterAssign] = {
    return PostResultIntrinsicRegisterAssign
  }

  def post_langastIRExpIf(o: org.sireum.lang.ast.IR.Exp.If): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpIf
  }

  def postIntrinsicGotoLocal(o: Intrinsic.GotoLocal): MOption[Intrinsic.GotoLocal] = {
    return PostResultIntrinsicGotoLocal
  }

  def post_langastIRExpConstruct(o: org.sireum.lang.ast.IR.Exp.Construct): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpConstruct
  }

  def post_langastIRExpApply(o: org.sireum.lang.ast.IR.Exp.Apply): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpApply
  }

  def post_langastIRExpIndexing(o: org.sireum.lang.ast.IR.Exp.Indexing): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpIndexing
  }

  def post_langastIRExpType(o: org.sireum.lang.ast.IR.Exp.Type): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpType
  }

  def post_langastIRExpIntrinsic(o: org.sireum.lang.ast.IR.Exp.Intrinsic): MOption[org.sireum.lang.ast.IR.Exp] = {
    return PostResult_langastIRExpIntrinsic
  }

  def post_langastIRExpIntrinsicType(o: org.sireum.lang.ast.IR.Exp.Intrinsic.Type): MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = {
    o match {
      case o: Intrinsic.Load =>
        val r: MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = postIntrinsicLoad(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Exp.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]()
        }
        return r
      case o: Intrinsic.Indexing =>
        val r: MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = postIntrinsicIndexing(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Exp.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]()
        }
        return r
      case o: Intrinsic.Register =>
        val r: MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = postIntrinsicRegister(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Exp.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Exp.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Exp.Intrinsic.Type]()
        }
        return r
    }
  }

  def post_langastIRStmt(o: org.sireum.lang.ast.IR.Stmt): MOption[org.sireum.lang.ast.IR.Stmt] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.Expr =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtExpr(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignLocal(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignGlobal(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignTemp(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignField(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtAssignIndex(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Decl =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtDecl(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmtIntrinsic(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt) => MSome[org.sireum.lang.ast.IR.Stmt](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assertume => return post_langastIRStmtAssertume(o)
      case o: org.sireum.lang.ast.IR.Stmt.Print => return post_langastIRStmtPrint(o)
      case o: org.sireum.lang.ast.IR.Stmt.Halt => return post_langastIRStmtHalt(o)
      case o: org.sireum.lang.ast.IR.Stmt.AssignPattern => return post_langastIRStmtAssignPattern(o)
      case o: org.sireum.lang.ast.IR.Stmt.Block => return post_langastIRStmtBlock(o)
      case o: org.sireum.lang.ast.IR.Stmt.If => return post_langastIRStmtIf(o)
      case o: org.sireum.lang.ast.IR.Stmt.Match => return post_langastIRStmtMatch(o)
      case o: org.sireum.lang.ast.IR.Stmt.While => return post_langastIRStmtWhile(o)
      case o: org.sireum.lang.ast.IR.Stmt.For => return post_langastIRStmtFor(o)
      case o: org.sireum.lang.ast.IR.Stmt.Return => return post_langastIRStmtReturn(o)
    }
  }

  def post_langastIRStmtGround(o: org.sireum.lang.ast.IR.Stmt.Ground): MOption[org.sireum.lang.ast.IR.Stmt.Ground] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.Expr => return post_langastIRStmtExpr(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignLocal(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Ground) => MSome[org.sireum.lang.ast.IR.Stmt.Ground](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Ground]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignGlobal(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Ground) => MSome[org.sireum.lang.ast.IR.Stmt.Ground](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Ground]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignTemp(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Ground) => MSome[org.sireum.lang.ast.IR.Stmt.Ground](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Ground]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignField(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Ground) => MSome[org.sireum.lang.ast.IR.Stmt.Ground](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Ground]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtAssignIndex(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Ground) => MSome[org.sireum.lang.ast.IR.Stmt.Ground](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Ground")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Ground]()
        }
        return r
      case o: org.sireum.lang.ast.IR.Stmt.Decl => return post_langastIRStmtDecl(o)
      case o: org.sireum.lang.ast.IR.Stmt.Intrinsic => return post_langastIRStmtIntrinsic(o)
    }
  }

  def post_langastIRStmtExpr(o: org.sireum.lang.ast.IR.Stmt.Expr): MOption[org.sireum.lang.ast.IR.Stmt.Ground] = {
    return PostResult_langastIRStmtExpr
  }

  def post_langastIRStmtAssign(o: org.sireum.lang.ast.IR.Stmt.Assign): MOption[org.sireum.lang.ast.IR.Stmt.Assign] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Local => return post_langastIRStmtAssignLocal(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Global => return post_langastIRStmtAssignGlobal(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Temp => return post_langastIRStmtAssignTemp(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Field => return post_langastIRStmtAssignField(o)
      case o: org.sireum.lang.ast.IR.Stmt.Assign.Index => return post_langastIRStmtAssignIndex(o)
    }
  }

  def post_langastIRStmtAssignLocal(o: org.sireum.lang.ast.IR.Stmt.Assign.Local): MOption[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PostResult_langastIRStmtAssignLocal
  }

  def post_langastIRStmtAssignGlobal(o: org.sireum.lang.ast.IR.Stmt.Assign.Global): MOption[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PostResult_langastIRStmtAssignGlobal
  }

  def post_langastIRStmtAssignTemp(o: org.sireum.lang.ast.IR.Stmt.Assign.Temp): MOption[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PostResult_langastIRStmtAssignTemp
  }

  def post_langastIRStmtAssignField(o: org.sireum.lang.ast.IR.Stmt.Assign.Field): MOption[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PostResult_langastIRStmtAssignField
  }

  def post_langastIRStmtAssignIndex(o: org.sireum.lang.ast.IR.Stmt.Assign.Index): MOption[org.sireum.lang.ast.IR.Stmt.Assign] = {
    return PostResult_langastIRStmtAssignIndex
  }

  def post_langastIRStmtDecl(o: org.sireum.lang.ast.IR.Stmt.Decl): MOption[org.sireum.lang.ast.IR.Stmt.Ground] = {
    return PostResult_langastIRStmtDecl
  }

  def post_langastIRStmtDeclLocal(o: org.sireum.lang.ast.IR.Stmt.Decl.Local): MOption[org.sireum.lang.ast.IR.Stmt.Decl.Local] = {
    return PostResult_langastIRStmtDeclLocal
  }

  def post_langastIRStmtIntrinsic(o: org.sireum.lang.ast.IR.Stmt.Intrinsic): MOption[org.sireum.lang.ast.IR.Stmt.Ground] = {
    return PostResult_langastIRStmtIntrinsic
  }

  def post_langastIRStmtIntrinsicType(o: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type): MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = {
    o match {
      case o: Intrinsic.TempLoad =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicTempLoad(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]()
        }
        return r
      case o: Intrinsic.Store =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicStore(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]()
        }
        return r
      case o: Intrinsic.Copy =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicCopy(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]()
        }
        return r
      case o: Intrinsic.Decl =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicDecl(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]()
        }
        return r
      case o: Intrinsic.RegisterAssign =>
        val r: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = postIntrinsicRegisterAssign(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type]()
        }
        return r
    }
  }

  def post_langastIRStmtAssertume(o: org.sireum.lang.ast.IR.Stmt.Assertume): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtAssertume
  }

  def post_langastIRStmtPrint(o: org.sireum.lang.ast.IR.Stmt.Print): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtPrint
  }

  def post_langastIRStmtHalt(o: org.sireum.lang.ast.IR.Stmt.Halt): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtHalt
  }

  def post_langastIRStmtAssignPattern(o: org.sireum.lang.ast.IR.Stmt.AssignPattern): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtAssignPattern
  }

  def post_langastIRStmtBlock(o: org.sireum.lang.ast.IR.Stmt.Block): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtBlock
  }

  def post_langastIRStmtIf(o: org.sireum.lang.ast.IR.Stmt.If): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtIf
  }

  def post_langastIRStmtMatch(o: org.sireum.lang.ast.IR.Stmt.Match): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtMatch
  }

  def post_langastIRStmtMatchCase(o: org.sireum.lang.ast.IR.Stmt.Match.Case): MOption[org.sireum.lang.ast.IR.Stmt.Match.Case] = {
    return PostResult_langastIRStmtMatchCase
  }

  def post_langastIRStmtWhile(o: org.sireum.lang.ast.IR.Stmt.While): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtWhile
  }

  def post_langastIRStmtFor(o: org.sireum.lang.ast.IR.Stmt.For): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtFor
  }

  def post_langastIRStmtForRange(o: org.sireum.lang.ast.IR.Stmt.For.Range): MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = {
    o match {
      case o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr => return post_langastIRStmtForRangeExpr(o)
      case o: org.sireum.lang.ast.IR.Stmt.For.Range.Step => return post_langastIRStmtForRangeStep(o)
    }
  }

  def post_langastIRStmtForRangeExpr(o: org.sireum.lang.ast.IR.Stmt.For.Range.Expr): MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = {
    return PostResult_langastIRStmtForRangeExpr
  }

  def post_langastIRStmtForRangeStep(o: org.sireum.lang.ast.IR.Stmt.For.Range.Step): MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = {
    return PostResult_langastIRStmtForRangeStep
  }

  def post_langastIRStmtReturn(o: org.sireum.lang.ast.IR.Stmt.Return): MOption[org.sireum.lang.ast.IR.Stmt] = {
    return PostResult_langastIRStmtReturn
  }

  def post_langastIRJump(o: org.sireum.lang.ast.IR.Jump): MOption[org.sireum.lang.ast.IR.Jump] = {
    o match {
      case o: org.sireum.lang.ast.IR.Jump.Goto => return post_langastIRJumpGoto(o)
      case o: org.sireum.lang.ast.IR.Jump.If => return post_langastIRJumpIf(o)
      case o: org.sireum.lang.ast.IR.Jump.Return => return post_langastIRJumpReturn(o)
      case o: org.sireum.lang.ast.IR.Jump.Switch => return post_langastIRJumpSwitch(o)
      case o: org.sireum.lang.ast.IR.Jump.Halt => return post_langastIRJumpHalt(o)
      case o: org.sireum.lang.ast.IR.Jump.Intrinsic => return post_langastIRJumpIntrinsic(o)
    }
  }

  def post_langastIRJumpGoto(o: org.sireum.lang.ast.IR.Jump.Goto): MOption[org.sireum.lang.ast.IR.Jump] = {
    return PostResult_langastIRJumpGoto
  }

  def post_langastIRJumpIf(o: org.sireum.lang.ast.IR.Jump.If): MOption[org.sireum.lang.ast.IR.Jump] = {
    return PostResult_langastIRJumpIf
  }

  def post_langastIRJumpReturn(o: org.sireum.lang.ast.IR.Jump.Return): MOption[org.sireum.lang.ast.IR.Jump] = {
    return PostResult_langastIRJumpReturn
  }

  def post_langastIRJumpSwitch(o: org.sireum.lang.ast.IR.Jump.Switch): MOption[org.sireum.lang.ast.IR.Jump] = {
    return PostResult_langastIRJumpSwitch
  }

  def post_langastIRJumpSwitchCase(o: org.sireum.lang.ast.IR.Jump.Switch.Case): MOption[org.sireum.lang.ast.IR.Jump.Switch.Case] = {
    return PostResult_langastIRJumpSwitchCase
  }

  def post_langastIRJumpHalt(o: org.sireum.lang.ast.IR.Jump.Halt): MOption[org.sireum.lang.ast.IR.Jump] = {
    return PostResult_langastIRJumpHalt
  }

  def post_langastIRJumpIntrinsic(o: org.sireum.lang.ast.IR.Jump.Intrinsic): MOption[org.sireum.lang.ast.IR.Jump] = {
    return PostResult_langastIRJumpIntrinsic
  }

  def post_langastIRJumpIntrinsicType(o: org.sireum.lang.ast.IR.Jump.Intrinsic.Type): MOption[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = {
    o match {
      case o: Intrinsic.GotoLocal =>
        val r: MOption[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = postIntrinsicGotoLocal(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Jump.Intrinsic.Type) => MSome[org.sireum.lang.ast.IR.Jump.Intrinsic.Type](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Jump.Intrinsic.Type")
         case _ => MNone[org.sireum.lang.ast.IR.Jump.Intrinsic.Type]()
        }
        return r
    }
  }

  def post_langastIRExpBlock(o: org.sireum.lang.ast.IR.ExpBlock): MOption[org.sireum.lang.ast.IR.ExpBlock] = {
    return PostResult_langastIRExpBlock
  }

  def post_langastIRBasicBlock(o: org.sireum.lang.ast.IR.BasicBlock): MOption[org.sireum.lang.ast.IR.BasicBlock] = {
    return PostResult_langastIRBasicBlock
  }

  def post_langastIRBody(o: org.sireum.lang.ast.IR.Body): MOption[org.sireum.lang.ast.IR.Body] = {
    o match {
      case o: org.sireum.lang.ast.IR.Body.Block => return post_langastIRBodyBlock(o)
      case o: org.sireum.lang.ast.IR.Body.Basic => return post_langastIRBodyBasic(o)
    }
  }

  def post_langastIRBodyBlock(o: org.sireum.lang.ast.IR.Body.Block): MOption[org.sireum.lang.ast.IR.Body] = {
    return PostResult_langastIRBodyBlock
  }

  def post_langastIRBodyBasic(o: org.sireum.lang.ast.IR.Body.Basic): MOption[org.sireum.lang.ast.IR.Body] = {
    return PostResult_langastIRBodyBasic
  }

  def post_langastIRProcedure(o: org.sireum.lang.ast.IR.Procedure): MOption[org.sireum.lang.ast.IR.Procedure] = {
    return PostResult_langastIRProcedure
  }

  def post_langastIRGlobal(o: org.sireum.lang.ast.IR.Global): MOption[org.sireum.lang.ast.IR.Global] = {
    return PostResult_langastIRGlobal
  }

  def post_langastIRProgram(o: org.sireum.lang.ast.IR.Program): MOption[org.sireum.lang.ast.IR.Program] = {
    return PostResult_langastIRProgram
  }

  def post_langastIRPrinter(o: org.sireum.lang.ast.IR.Printer): MOption[org.sireum.lang.ast.IR.Printer] = {
    o match {
      case o: org.sireum.lang.ast.IR.Printer.Empty =>
        val r: MOption[org.sireum.lang.ast.IR.Printer] = post_langastIRPrinterEmpty(o) match {
         case MSome(result: org.sireum.lang.ast.IR.Printer) => MSome[org.sireum.lang.ast.IR.Printer](result)
         case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Printer")
         case _ => MNone[org.sireum.lang.ast.IR.Printer]()
        }
        return r
    }
  }

  def post_langastIRPrinterEmpty(o: org.sireum.lang.ast.IR.Printer.Empty): MOption[org.sireum.lang.ast.IR.Printer.Empty] = {
    return PostResult_langastIRPrinterEmpty
  }

  def transform_langastIRMethodContext(o: org.sireum.lang.ast.IR.MethodContext): MOption[org.sireum.lang.ast.IR.MethodContext] = {
    val preR: PreResult[org.sireum.lang.ast.IR.MethodContext] = pre_langastIRMethodContext(o)
    val r: MOption[org.sireum.lang.ast.IR.MethodContext] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.MethodContext = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.MethodContext = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.MethodContext] = post_langastIRMethodContext(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicTempLoad(o: Intrinsic.TempLoad): MOption[Intrinsic.TempLoad] = {
    val preR: PreResult[Intrinsic.TempLoad] = preIntrinsicTempLoad(o)
    val r: MOption[Intrinsic.TempLoad] = if (preR.continu) {
      val o2: Intrinsic.TempLoad = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.base)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(base = r0.getOrElse(o2.base)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.TempLoad = r.getOrElse(o)
    val postR: MOption[Intrinsic.TempLoad] = postIntrinsicTempLoad(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRExp(o: org.sireum.lang.ast.IR.Exp): MOption[org.sireum.lang.ast.IR.Exp] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Exp] = pre_langastIRExp(o)
    val r: MOption[org.sireum.lang.ast.IR.Exp] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Exp = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Exp] = o2 match {
        case o2: org.sireum.lang.ast.IR.Exp.Bool =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Int =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.F32 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.F64 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.R =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.String =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Temp =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.LocalVarRef =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.GlobalVarRef =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.EnumElementRef =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.FieldVarRef =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.receiver)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(receiver = r0.getOrElse(o2.receiver)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Unary =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.exp)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Binary =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.left)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.right)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(left = r0.getOrElse(o2.left), right = r1.getOrElse(o2.right)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.If =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.cond)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.thenExp)
          val r2: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.elseExp)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(cond = r0.getOrElse(o2.cond), thenExp = r1.getOrElse(o2.thenExp), elseExp = r2.getOrElse(o2.elseExp)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Construct =>
          val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(o2.args, transform_langastIRExp _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(args = r0.getOrElse(o2.args)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Apply =>
          val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(o2.args, transform_langastIRExp _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(args = r0.getOrElse(o2.args)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Indexing =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.exp)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp), index = r1.getOrElse(o2.index)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Type =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.exp)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Exp.Intrinsic =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = transform_langastIRExpIntrinsicType(o2.intrinsic)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(intrinsic = r0.getOrElse(o2.intrinsic)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Exp = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Exp] = post_langastIRExp(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicLoad(o: Intrinsic.Load): MOption[Intrinsic.Load] = {
    val preR: PreResult[Intrinsic.Load] = preIntrinsicLoad(o)
    val r: MOption[Intrinsic.Load] = if (preR.continu) {
      val o2: Intrinsic.Load = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.base)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(base = r0.getOrElse(o2.base)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.Load = r.getOrElse(o)
    val postR: MOption[Intrinsic.Load] = postIntrinsicLoad(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicIndexing(o: Intrinsic.Indexing): MOption[Intrinsic.Indexing] = {
    val preR: PreResult[Intrinsic.Indexing] = preIntrinsicIndexing(o)
    val r: MOption[Intrinsic.Indexing] = if (preR.continu) {
      val o2: Intrinsic.Indexing = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.baseOffset)
      val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.index)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty)
        MSome(o2(baseOffset = r0.getOrElse(o2.baseOffset), index = r1.getOrElse(o2.index)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.Indexing = r.getOrElse(o)
    val postR: MOption[Intrinsic.Indexing] = postIntrinsicIndexing(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicStore(o: Intrinsic.Store): MOption[Intrinsic.Store] = {
    val preR: PreResult[Intrinsic.Store] = preIntrinsicStore(o)
    val r: MOption[Intrinsic.Store] = if (preR.continu) {
      val o2: Intrinsic.Store = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.base)
      val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty)
        MSome(o2(base = r0.getOrElse(o2.base), rhs = r1.getOrElse(o2.rhs)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.Store = r.getOrElse(o)
    val postR: MOption[Intrinsic.Store] = postIntrinsicStore(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicCopy(o: Intrinsic.Copy): MOption[Intrinsic.Copy] = {
    val preR: PreResult[Intrinsic.Copy] = preIntrinsicCopy(o)
    val r: MOption[Intrinsic.Copy] = if (preR.continu) {
      val o2: Intrinsic.Copy = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.lbase)
      val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhsBytes)
      val r2: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
        MSome(o2(lbase = r0.getOrElse(o2.lbase), rhsBytes = r1.getOrElse(o2.rhsBytes), rhs = r2.getOrElse(o2.rhs)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.Copy = r.getOrElse(o)
    val postR: MOption[Intrinsic.Copy] = postIntrinsicCopy(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicDecl(o: Intrinsic.Decl): MOption[Intrinsic.Decl] = {
    val preR: PreResult[Intrinsic.Decl] = preIntrinsicDecl(o)
    val r: MOption[Intrinsic.Decl] = if (preR.continu) {
      val o2: Intrinsic.Decl = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[IS[Z, Intrinsic.Decl.Local]] = transformISZ(o2.slots, transformIntrinsicDeclLocal _)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(slots = r0.getOrElse(o2.slots)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.Decl = r.getOrElse(o)
    val postR: MOption[Intrinsic.Decl] = postIntrinsicDecl(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicDeclLocal(o: Intrinsic.Decl.Local): MOption[Intrinsic.Decl.Local] = {
    val preR: PreResult[Intrinsic.Decl.Local] = preIntrinsicDeclLocal(o)
    val r: MOption[Intrinsic.Decl.Local] = if (preR.continu) {
      val o2: Intrinsic.Decl.Local = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.Decl.Local = r.getOrElse(o)
    val postR: MOption[Intrinsic.Decl.Local] = postIntrinsicDeclLocal(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicRegister(o: Intrinsic.Register): MOption[Intrinsic.Register] = {
    val preR: PreResult[Intrinsic.Register] = preIntrinsicRegister(o)
    val r: MOption[Intrinsic.Register] = if (preR.continu) {
      val o2: Intrinsic.Register = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.Register = r.getOrElse(o)
    val postR: MOption[Intrinsic.Register] = postIntrinsicRegister(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicRegisterAssign(o: Intrinsic.RegisterAssign): MOption[Intrinsic.RegisterAssign] = {
    val preR: PreResult[Intrinsic.RegisterAssign] = preIntrinsicRegisterAssign(o)
    val r: MOption[Intrinsic.RegisterAssign] = if (preR.continu) {
      val o2: Intrinsic.RegisterAssign = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.value)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(value = r0.getOrElse(o2.value)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.RegisterAssign = r.getOrElse(o)
    val postR: MOption[Intrinsic.RegisterAssign] = postIntrinsicRegisterAssign(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformIntrinsicGotoLocal(o: Intrinsic.GotoLocal): MOption[Intrinsic.GotoLocal] = {
    val preR: PreResult[Intrinsic.GotoLocal] = preIntrinsicGotoLocal(o)
    val r: MOption[Intrinsic.GotoLocal] = if (preR.continu) {
      val o2: Intrinsic.GotoLocal = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[Option[org.sireum.lang.ast.IR.MethodContext]] = transformOption(o2.contextOpt, transform_langastIRMethodContext _)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(contextOpt = r0.getOrElse(o2.contextOpt)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: Intrinsic.GotoLocal = r.getOrElse(o)
    val postR: MOption[Intrinsic.GotoLocal] = postIntrinsicGotoLocal(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRExpIntrinsicType(o: org.sireum.lang.ast.IR.Exp.Intrinsic.Type): MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = pre_langastIRExpIntrinsicType(o)
    val r: MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Exp.Intrinsic.Type = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = o2 match {
        case o2: Intrinsic.Load =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.base)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(base = r0.getOrElse(o2.base)))
          else
            MNone()
        case o2: Intrinsic.Indexing =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.baseOffset)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(baseOffset = r0.getOrElse(o2.baseOffset), index = r1.getOrElse(o2.index)))
          else
            MNone()
        case o2: Intrinsic.Register =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Exp.Intrinsic.Type = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Exp.Intrinsic.Type] = post_langastIRExpIntrinsicType(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmt(o: org.sireum.lang.ast.IR.Stmt): MOption[org.sireum.lang.ast.IR.Stmt] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt] = pre_langastIRStmt(o)
    val r: MOption[org.sireum.lang.ast.IR.Stmt] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Stmt] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.Expr =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp.Apply] = transform_langastIRExpApply(o2.exp)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(rhs = r0.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(rhs = r0.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.receiver)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(receiver = r0.getOrElse(o2.receiver), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.receiver)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.index)
          val r2: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(receiver = r0.getOrElse(o2.receiver), index = r1.getOrElse(o2.index), rhs = r2.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Decl =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          val r1: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt.Decl.Local]] = transformISZ(o2.locals, transform_langastIRStmtDeclLocal _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context), locals = r1.getOrElse(o2.locals)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
          val r0: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = transform_langastIRStmtIntrinsicType(o2.intrinsic)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(intrinsic = r0.getOrElse(o2.intrinsic)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assertume =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.cond)
          val r1: MOption[Option[org.sireum.lang.ast.IR.ExpBlock]] = transformOption(o2.messageOpt, transform_langastIRExpBlock _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(cond = r0.getOrElse(o2.cond), messageOpt = r1.getOrElse(o2.messageOpt)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Print =>
          val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(o2.args, transform_langastIRExp _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(args = r0.getOrElse(o2.args)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Halt =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.message)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(message = r0.getOrElse(o2.message)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.AssignPattern =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Block =>
          val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt]] = transformISZ(o2.stmts, transform_langastIRStmt _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(stmts = r0.getOrElse(o2.stmts)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.If =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.cond)
          val r1: MOption[org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(o2.thenBlock)
          val r2: MOption[org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(o2.elseBlock)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(cond = r0.getOrElse(o2.cond), thenBlock = r1.getOrElse(o2.thenBlock), elseBlock = r2.getOrElse(o2.elseBlock)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Match =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.exp)
          val r1: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt.Match.Case]] = transformISZ(o2.cases, transform_langastIRStmtMatchCase _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp), cases = r1.getOrElse(o2.cases)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.While =>
          val r0: MOption[org.sireum.lang.ast.IR.ExpBlock] = transform_langastIRExpBlock(o2.cond)
          val r1: MOption[org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(o2.block)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(cond = r0.getOrElse(o2.cond), block = r1.getOrElse(o2.block)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.For =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          val r1: MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = transform_langastIRStmtForRange(o2.range)
          val r2: MOption[Option[org.sireum.lang.ast.IR.ExpBlock]] = transformOption(o2.condOpt, transform_langastIRExpBlock _)
          val r3: MOption[org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(o2.block)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty || r3.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context), range = r1.getOrElse(o2.range), condOpt = r2.getOrElse(o2.condOpt), block = r3.getOrElse(o2.block)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Return =>
          val r0: MOption[Option[org.sireum.lang.ast.IR.Exp]] = transformOption(o2.expOpt, transform_langastIRExp _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(expOpt = r0.getOrElse(o2.expOpt)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt] = post_langastIRStmt(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtGround(o: org.sireum.lang.ast.IR.Stmt.Ground): MOption[org.sireum.lang.ast.IR.Stmt.Ground] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.Ground] = pre_langastIRStmtGround(o)
    val r: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Ground = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.Expr =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp.Apply] = transform_langastIRExpApply(o2.exp)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(rhs = r0.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(rhs = r0.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.receiver)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(receiver = r0.getOrElse(o2.receiver), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.receiver)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.index)
          val r2: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(receiver = r0.getOrElse(o2.receiver), index = r1.getOrElse(o2.index), rhs = r2.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Decl =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          val r1: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt.Decl.Local]] = transformISZ(o2.locals, transform_langastIRStmtDeclLocal _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context), locals = r1.getOrElse(o2.locals)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Intrinsic =>
          val r0: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = transform_langastIRStmtIntrinsicType(o2.intrinsic)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(intrinsic = r0.getOrElse(o2.intrinsic)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Ground = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.Ground] = post_langastIRStmtGround(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtAssign(o: org.sireum.lang.ast.IR.Stmt.Assign): MOption[org.sireum.lang.ast.IR.Stmt.Assign] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.Assign] = pre_langastIRStmtAssign(o)
    val r: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Assign = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Local =>
          val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(context = r0.getOrElse(o2.context), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Global =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(rhs = r0.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Temp =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(rhs = r0.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Field =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.receiver)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(receiver = r0.getOrElse(o2.receiver), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.Assign.Index =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.receiver)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.index)
          val r2: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(receiver = r0.getOrElse(o2.receiver), index = r1.getOrElse(o2.index), rhs = r2.getOrElse(o2.rhs)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Assign = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.Assign] = post_langastIRStmtAssign(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtDeclLocal(o: org.sireum.lang.ast.IR.Stmt.Decl.Local): MOption[org.sireum.lang.ast.IR.Stmt.Decl.Local] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.Decl.Local] = pre_langastIRStmtDeclLocal(o)
    val r: MOption[org.sireum.lang.ast.IR.Stmt.Decl.Local] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Decl.Local = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Decl.Local = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.Decl.Local] = post_langastIRStmtDeclLocal(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtIntrinsicType(o: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type): MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = pre_langastIRStmtIntrinsicType(o)
    val r: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = o2 match {
        case o2: Intrinsic.TempLoad =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.base)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(base = r0.getOrElse(o2.base)))
          else
            MNone()
        case o2: Intrinsic.Store =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.base)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(base = r0.getOrElse(o2.base), rhs = r1.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: Intrinsic.Copy =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.lbase)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhsBytes)
          val r2: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.rhs)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(lbase = r0.getOrElse(o2.lbase), rhsBytes = r1.getOrElse(o2.rhsBytes), rhs = r2.getOrElse(o2.rhs)))
          else
            MNone()
        case o2: Intrinsic.Decl =>
          val r0: MOption[IS[Z, Intrinsic.Decl.Local]] = transformISZ(o2.slots, transformIntrinsicDeclLocal _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(slots = r0.getOrElse(o2.slots)))
          else
            MNone()
        case o2: Intrinsic.RegisterAssign =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.value)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(value = r0.getOrElse(o2.value)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Intrinsic.Type = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.Intrinsic.Type] = post_langastIRStmtIntrinsicType(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtMatchCase(o: org.sireum.lang.ast.IR.Stmt.Match.Case): MOption[org.sireum.lang.ast.IR.Stmt.Match.Case] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.Match.Case] = pre_langastIRStmtMatchCase(o)
    val r: MOption[org.sireum.lang.ast.IR.Stmt.Match.Case] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Match.Case = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Stmt.Decl] = transform_langastIRStmtDecl(o2.decl)
      val r1: MOption[Option[org.sireum.lang.ast.IR.ExpBlock]] = transformOption(o2.condOpt, transform_langastIRExpBlock _)
      val r2: MOption[org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(o2.body)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
        MSome(o2(decl = r0.getOrElse(o2.decl), condOpt = r1.getOrElse(o2.condOpt), body = r2.getOrElse(o2.body)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Match.Case = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.Match.Case] = post_langastIRStmtMatchCase(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtForRange(o: org.sireum.lang.ast.IR.Stmt.For.Range): MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.For.Range] = pre_langastIRStmtForRange(o)
    val r: MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.For.Range = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = o2 match {
        case o2: org.sireum.lang.ast.IR.Stmt.For.Range.Expr =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.exp)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Stmt.For.Range.Step =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.start)
          val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.end)
          val r2: MOption[Option[org.sireum.lang.ast.IR.Exp]] = transformOption(o2.byOpt, transform_langastIRExp _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(start = r0.getOrElse(o2.start), end = r1.getOrElse(o2.end), byOpt = r2.getOrElse(o2.byOpt)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.For.Range = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.For.Range] = post_langastIRStmtForRange(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRJump(o: org.sireum.lang.ast.IR.Jump): MOption[org.sireum.lang.ast.IR.Jump] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Jump] = pre_langastIRJump(o)
    val r: MOption[org.sireum.lang.ast.IR.Jump] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Jump = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Jump] = o2 match {
        case o2: org.sireum.lang.ast.IR.Jump.Goto =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Jump.If =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.cond)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(cond = r0.getOrElse(o2.cond)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Jump.Return =>
          val r0: MOption[Option[org.sireum.lang.ast.IR.Exp]] = transformOption(o2.expOpt, transform_langastIRExp _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(expOpt = r0.getOrElse(o2.expOpt)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Jump.Switch =>
          val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.exp)
          val r1: MOption[IS[Z, org.sireum.lang.ast.IR.Jump.Switch.Case]] = transformISZ(o2.cases, transform_langastIRJumpSwitchCase _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(exp = r0.getOrElse(o2.exp), cases = r1.getOrElse(o2.cases)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Jump.Halt =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Jump.Intrinsic =>
          val r0: MOption[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = transform_langastIRJumpIntrinsicType(o2.intrinsic)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(intrinsic = r0.getOrElse(o2.intrinsic)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Jump = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Jump] = post_langastIRJump(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRJumpSwitchCase(o: org.sireum.lang.ast.IR.Jump.Switch.Case): MOption[org.sireum.lang.ast.IR.Jump.Switch.Case] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Jump.Switch.Case] = pre_langastIRJumpSwitchCase(o)
    val r: MOption[org.sireum.lang.ast.IR.Jump.Switch.Case] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Jump.Switch.Case = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.value)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(value = r0.getOrElse(o2.value)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Jump.Switch.Case = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Jump.Switch.Case] = post_langastIRJumpSwitchCase(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRJumpIntrinsicType(o: org.sireum.lang.ast.IR.Jump.Intrinsic.Type): MOption[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = pre_langastIRJumpIntrinsicType(o)
    val r: MOption[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Jump.Intrinsic.Type = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = o2 match {
        case o2: Intrinsic.GotoLocal =>
          val r0: MOption[Option[org.sireum.lang.ast.IR.MethodContext]] = transformOption(o2.contextOpt, transform_langastIRMethodContext _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(contextOpt = r0.getOrElse(o2.contextOpt)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Jump.Intrinsic.Type = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Jump.Intrinsic.Type] = post_langastIRJumpIntrinsicType(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRExpBlock(o: org.sireum.lang.ast.IR.ExpBlock): MOption[org.sireum.lang.ast.IR.ExpBlock] = {
    val preR: PreResult[org.sireum.lang.ast.IR.ExpBlock] = pre_langastIRExpBlock(o)
    val r: MOption[org.sireum.lang.ast.IR.ExpBlock] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.ExpBlock = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt]] = transformISZ(o2.stmts, transform_langastIRStmt _)
      val r1: MOption[org.sireum.lang.ast.IR.Exp] = transform_langastIRExp(o2.exp)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty)
        MSome(o2(stmts = r0.getOrElse(o2.stmts), exp = r1.getOrElse(o2.exp)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.ExpBlock = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.ExpBlock] = post_langastIRExpBlock(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRBasicBlock(o: org.sireum.lang.ast.IR.BasicBlock): MOption[org.sireum.lang.ast.IR.BasicBlock] = {
    val preR: PreResult[org.sireum.lang.ast.IR.BasicBlock] = pre_langastIRBasicBlock(o)
    val r: MOption[org.sireum.lang.ast.IR.BasicBlock] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.BasicBlock = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt.Ground]] = transformISZ(o2.grounds, transform_langastIRStmtGround _)
      val r1: MOption[org.sireum.lang.ast.IR.Jump] = transform_langastIRJump(o2.jump)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty)
        MSome(o2(grounds = r0.getOrElse(o2.grounds), jump = r1.getOrElse(o2.jump)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.BasicBlock = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.BasicBlock] = post_langastIRBasicBlock(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRBody(o: org.sireum.lang.ast.IR.Body): MOption[org.sireum.lang.ast.IR.Body] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Body] = pre_langastIRBody(o)
    val r: MOption[org.sireum.lang.ast.IR.Body] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Body = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Body] = o2 match {
        case o2: org.sireum.lang.ast.IR.Body.Block =>
          val r0: MOption[org.sireum.lang.ast.IR.Stmt.Block] = transform_langastIRStmtBlock(o2.block)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(block = r0.getOrElse(o2.block)))
          else
            MNone()
        case o2: org.sireum.lang.ast.IR.Body.Basic =>
          val r0: MOption[IS[Z, org.sireum.lang.ast.IR.BasicBlock]] = transformISZ(o2.blocks, transform_langastIRBasicBlock _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(blocks = r0.getOrElse(o2.blocks)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Body = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Body] = post_langastIRBody(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRProcedure(o: org.sireum.lang.ast.IR.Procedure): MOption[org.sireum.lang.ast.IR.Procedure] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Procedure] = pre_langastIRProcedure(o)
    val r: MOption[org.sireum.lang.ast.IR.Procedure] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Procedure = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.Body] = transform_langastIRBody(o2.body)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(body = r0.getOrElse(o2.body)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Procedure = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Procedure] = post_langastIRProcedure(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRGlobal(o: org.sireum.lang.ast.IR.Global): MOption[org.sireum.lang.ast.IR.Global] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Global] = pre_langastIRGlobal(o)
    val r: MOption[org.sireum.lang.ast.IR.Global] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Global = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Global = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Global] = post_langastIRGlobal(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRProgram(o: org.sireum.lang.ast.IR.Program): MOption[org.sireum.lang.ast.IR.Program] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Program] = pre_langastIRProgram(o)
    val r: MOption[org.sireum.lang.ast.IR.Program] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Program = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Global]] = transformISZ(o2.globals, transform_langastIRGlobal _)
      val r1: MOption[IS[Z, org.sireum.lang.ast.IR.Procedure]] = transformISZ(o2.procedures, transform_langastIRProcedure _)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty)
        MSome(o2(globals = r0.getOrElse(o2.globals), procedures = r1.getOrElse(o2.procedures)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Program = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Program] = post_langastIRProgram(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRPrinter(o: org.sireum.lang.ast.IR.Printer): MOption[org.sireum.lang.ast.IR.Printer] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Printer] = pre_langastIRPrinter(o)
    val r: MOption[org.sireum.lang.ast.IR.Printer] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Printer = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[org.sireum.lang.ast.IR.Printer] = o2 match {
        case o2: org.sireum.lang.ast.IR.Printer.Empty =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Printer = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Printer] = post_langastIRPrinter(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRPrinterEmpty(o: org.sireum.lang.ast.IR.Printer.Empty): MOption[org.sireum.lang.ast.IR.Printer.Empty] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Printer.Empty] = pre_langastIRPrinterEmpty(o)
    val r: MOption[org.sireum.lang.ast.IR.Printer.Empty] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Printer.Empty = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Printer.Empty = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Printer.Empty] = post_langastIRPrinterEmpty(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRExpApply(o: org.sireum.lang.ast.IR.Exp.Apply): MOption[org.sireum.lang.ast.IR.Exp.Apply] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Exp.Apply] = pre_langastIRExpApply(o) match {
     case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Exp.Apply)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Exp.Apply](r))
     case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Apply")
     case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Exp.Apply]())
    }
    val r: MOption[org.sireum.lang.ast.IR.Exp.Apply] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Exp.Apply = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Exp]] = transformISZ(o2.args, transform_langastIRExp _)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(args = r0.getOrElse(o2.args)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Exp.Apply = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Exp.Apply] = post_langastIRExpApply(o2) match {
     case MSome(result: org.sireum.lang.ast.IR.Exp.Apply) => MSome[org.sireum.lang.ast.IR.Exp.Apply](result)
     case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Exp.Apply")
     case _ => MNone[org.sireum.lang.ast.IR.Exp.Apply]()
    }
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtBlock(o: org.sireum.lang.ast.IR.Stmt.Block): MOption[org.sireum.lang.ast.IR.Stmt.Block] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.Block] = pre_langastIRStmtBlock(o) match {
     case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Block)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Block](r))
     case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Block")
     case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Block]())
    }
    val r: MOption[org.sireum.lang.ast.IR.Stmt.Block] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Block = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt]] = transformISZ(o2.stmts, transform_langastIRStmt _)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(stmts = r0.getOrElse(o2.stmts)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Block = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.Block] = post_langastIRStmtBlock(o2) match {
     case MSome(result: org.sireum.lang.ast.IR.Stmt.Block) => MSome[org.sireum.lang.ast.IR.Stmt.Block](result)
     case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Block")
     case _ => MNone[org.sireum.lang.ast.IR.Stmt.Block]()
    }
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transform_langastIRStmtDecl(o: org.sireum.lang.ast.IR.Stmt.Decl): MOption[org.sireum.lang.ast.IR.Stmt.Decl] = {
    val preR: PreResult[org.sireum.lang.ast.IR.Stmt.Decl] = pre_langastIRStmtDecl(o) match {
     case PreResult(continu, MSome(r: org.sireum.lang.ast.IR.Stmt.Decl)) => PreResult(continu, MSome[org.sireum.lang.ast.IR.Stmt.Decl](r))
     case PreResult(_, MSome(_)) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Decl")
     case PreResult(continu, _) => PreResult(continu, MNone[org.sireum.lang.ast.IR.Stmt.Decl]())
    }
    val r: MOption[org.sireum.lang.ast.IR.Stmt.Decl] = if (preR.continu) {
      val o2: org.sireum.lang.ast.IR.Stmt.Decl = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[org.sireum.lang.ast.IR.MethodContext] = transform_langastIRMethodContext(o2.context)
      val r1: MOption[IS[Z, org.sireum.lang.ast.IR.Stmt.Decl.Local]] = transformISZ(o2.locals, transform_langastIRStmtDeclLocal _)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty)
        MSome(o2(context = r0.getOrElse(o2.context), locals = r1.getOrElse(o2.locals)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: org.sireum.lang.ast.IR.Stmt.Decl = r.getOrElse(o)
    val postR: MOption[org.sireum.lang.ast.IR.Stmt.Decl] = post_langastIRStmtDecl(o2) match {
     case MSome(result: org.sireum.lang.ast.IR.Stmt.Decl) => MSome[org.sireum.lang.ast.IR.Stmt.Decl](result)
     case MSome(_) => halt("Can only produce object of type org.sireum.lang.ast.IR.Stmt.Decl")
     case _ => MNone[org.sireum.lang.ast.IR.Stmt.Decl]()
    }
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

}