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
import org.sireum.lang.{ast => AST}
import org.sireum.anvil.Printer
import org.sireum.anvil.PrinterIndex.U
import org.sireum.anvil.PrinterIndex.U._
import org.sireum.U8._
import org.sireum.S64._
import org.sireum.U64._

object AnvilSimulator {
  @datatype class State(val memory: IS[U, U8], val CP: U64, val SP: U64, val DP: U64, val temps: IS[Z, U64])

  object State {
    @strictpure def create(memory: Z, temps: Z): State = State(IS.create[U, U8](memory, u8"0"), u64"0", u64"0", u64"0",
      ISZ.create(temps, u64"0"))
  }

  @datatype class Value(val kind: Value.Kind.Type, val value: Z) {
    @strictpure override def string: String = kind match {
      case Value.Kind.U8 => toU8.string
      case Value.Kind.U16 => toU16.string
      case Value.Kind.U32 => toU32.string
      case Value.Kind.U64 => toU64.string
      case Value.Kind.S8 => toS8.string
      case Value.Kind.S16 => toS16.string
      case Value.Kind.S32 => toS32.string
      case Value.Kind.S64 => toS64.string
      case Value.Kind.F32 => toF32.string
      case Value.Kind.F64 => toF64.string
    }
    @strictpure def bytes: Z = kind match {
      case Value.Kind.U8 => 1
      case Value.Kind.U16 => 2
      case Value.Kind.U32 => 4
      case Value.Kind.U64 => 8
      case Value.Kind.S8 => 1
      case Value.Kind.S16 => 2
      case Value.Kind.S32 => 4
      case Value.Kind.S64 => 8
      case Value.Kind.F32 => 4
      case Value.Kind.F64 => 8
    }
    @strictpure def signed: B = kind match {
      case Value.Kind.U8 => F
      case Value.Kind.U16 => F
      case Value.Kind.U32 => F
      case Value.Kind.U64 => F
      case Value.Kind.S8 => T
      case Value.Kind.S16 => T
      case Value.Kind.S32 => T
      case Value.Kind.S64 => T
      case Value.Kind.F32 => T
      case Value.Kind.F64 => T
    }
    @strictpure def +(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 + other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 + other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 + other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 + other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 + other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 + other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 + other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 + other.toS64)
        case Value.Kind.F32 => Value.f32(toF32 + other.toF32)
        case Value.Kind.F64 => Value.f64(toF64 + other.toF64)
      }
    }
    @strictpure def -(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 - other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 - other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 - other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 - other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 - other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 - other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 - other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 - other.toS64)
        case Value.Kind.F32 => Value.f32(toF32 - other.toF32)
        case Value.Kind.F64 => Value.f64(toF64 - other.toF64)
      }
    }
    @strictpure def *(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 * other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 * other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 * other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 * other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 * other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 * other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 * other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 * other.toS64)
        case Value.Kind.F32 => Value.f32(toF32 * other.toF32)
        case Value.Kind.F64 => Value.f64(toF64 * other.toF64)
      }
    }
    @strictpure def /(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 / other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 / other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 / other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 / other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 / other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 / other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 / other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 / other.toS64)
        case Value.Kind.F32 => Value.f32(toF32 / other.toF32)
        case Value.Kind.F64 => Value.f64(toF64 / other.toF64)
      }
    }
    @strictpure def %(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 % other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 % other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 % other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 % other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 % other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 % other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 % other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 % other.toS64)
        case Value.Kind.F32 => Value.f32(toF32 % other.toF32)
        case Value.Kind.F64 => Value.f64(toF64 % other.toF64)
      }
    }
    @strictpure def >>(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 >> other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 >> other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 >> other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 >> other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 >> other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 >> other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 >> other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 >> other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def ~~(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => halt("Infeasible")
        case Value.Kind.U16 => halt("Infeasible")
        case Value.Kind.U32 => halt("Infeasible")
        case Value.Kind.U64 => halt("Infeasible")
        case Value.Kind.S8 => halt("Infeasible")
        case Value.Kind.S16 => halt("Infeasible")
        case Value.Kind.S32 => halt("Infeasible")
        case Value.Kind.S64 => halt("Infeasible")
        case Value.Kind.F32 => Value.b(toF32 ~~ other.toF32)
        case Value.Kind.F64 => Value.b(toF32 ~~ other.toF32)
      }
    }
    @strictpure def !~(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => halt("Infeasible")
        case Value.Kind.U16 => halt("Infeasible")
        case Value.Kind.U32 => halt("Infeasible")
        case Value.Kind.U64 => halt("Infeasible")
        case Value.Kind.S8 => halt("Infeasible")
        case Value.Kind.S16 => halt("Infeasible")
        case Value.Kind.S32 => halt("Infeasible")
        case Value.Kind.S64 => halt("Infeasible")
        case Value.Kind.F32 => Value.b(toF32 !~ other.toF32)
        case Value.Kind.F64 => Value.b(toF32 !~ other.toF32)
      }
    }
    @strictpure def >>>(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 >>> other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 >>> other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 >>> other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 >>> other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 >>> other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 >>> other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 >>> other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 >>> other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def <<(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 << other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 << other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 << other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 << other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 << other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 << other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 << other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 << other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def &(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 & other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 & other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 & other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 & other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 & other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 & other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 & other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 & other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def |(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 | other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 | other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 | other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 | other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 | other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 | other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 | other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 | other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def |^(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.u8(toU8 |^ other.toU8)
        case Value.Kind.U16 => Value.u16(toU16 |^ other.toU16)
        case Value.Kind.U32 => Value.u32(toU32 |^ other.toU32)
        case Value.Kind.U64 => Value.u64(toU64 |^ other.toU64)
        case Value.Kind.S8 => Value.s8(toS8 |^ other.toS8)
        case Value.Kind.S16 => Value.s16(toS16 |^ other.toS16)
        case Value.Kind.S32 => Value.s32(toS32 |^ other.toS32)
        case Value.Kind.S64 => Value.s64(toS64 |^ other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def __>:(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.b(!toB | other.toB)
        case Value.Kind.U16 => halt("Infeasible")
        case Value.Kind.U32 => halt("Infeasible")
        case Value.Kind.U64 => halt("Infeasible")
        case Value.Kind.S8 => halt("Infeasible")
        case Value.Kind.S16 => halt("Infeasible")
        case Value.Kind.S32 => halt("Infeasible")
        case Value.Kind.S64 => halt("Infeasible")
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def <(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.b(toU8 < other.toU8)
        case Value.Kind.U16 => Value.b(toU16 < other.toU16)
        case Value.Kind.U32 => Value.b(toU32 < other.toU32)
        case Value.Kind.U64 => Value.b(toU64 < other.toU64)
        case Value.Kind.S8 => Value.b(toS8 < other.toS8)
        case Value.Kind.S16 => Value.b(toS16 < other.toS16)
        case Value.Kind.S32 => Value.b(toS32 < other.toS32)
        case Value.Kind.S64 => Value.b(toS64 < other.toS64)
        case Value.Kind.F32 => Value.b(toF32 < other.toF32)
        case Value.Kind.F64 => Value.b(toF64 < other.toF64)
      }
    }
    @strictpure def <=(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.b(toU8 <= other.toU8)
        case Value.Kind.U16 => Value.b(toU16 <= other.toU16)
        case Value.Kind.U32 => Value.b(toU32 <= other.toU32)
        case Value.Kind.U64 => Value.b(toU64 <= other.toU64)
        case Value.Kind.S8 => Value.b(toS8 <= other.toS8)
        case Value.Kind.S16 => Value.b(toS16 <= other.toS16)
        case Value.Kind.S32 => Value.b(toS32 <= other.toS32)
        case Value.Kind.S64 => Value.b(toS64 <= other.toS64)
        case Value.Kind.F32 => Value.b(toF32 <= other.toF32)
        case Value.Kind.F64 => Value.b(toF64 <= other.toF64)
      }
    }
    @strictpure def >(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.b(toU8 > other.toU8)
        case Value.Kind.U16 => Value.b(toU16 > other.toU16)
        case Value.Kind.U32 => Value.b(toU32 > other.toU32)
        case Value.Kind.U64 => Value.b(toU64 > other.toU64)
        case Value.Kind.S8 => Value.b(toS8 > other.toS8)
        case Value.Kind.S16 => Value.b(toS16 > other.toS16)
        case Value.Kind.S32 => Value.b(toS32 > other.toS32)
        case Value.Kind.S64 => Value.b(toS64 > other.toS64)
        case Value.Kind.F32 => Value.b(toF32 > other.toF32)
        case Value.Kind.F64 => Value.b(toF64 > other.toF64)
      }
    }
    @strictpure def >=(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.b(toU8 >= other.toU8)
        case Value.Kind.U16 => Value.b(toU16 >= other.toU16)
        case Value.Kind.U32 => Value.b(toU32 >= other.toU32)
        case Value.Kind.U64 => Value.b(toU64 >= other.toU64)
        case Value.Kind.S8 => Value.b(toS8 >= other.toS8)
        case Value.Kind.S16 => Value.b(toS16 >= other.toS16)
        case Value.Kind.S32 => Value.b(toS32 >= other.toS32)
        case Value.Kind.S64 => Value.b(toS64 >= other.toS64)
        case Value.Kind.F32 => Value.b(toF32 >= other.toF32)
        case Value.Kind.F64 => Value.b(toF64 >= other.toF64)
      }
    }
    @strictpure def not : Value = {
      kind match {
        case Value.Kind.U8 => Value.b(!toB)
        case Value.Kind.U16 => halt("Infeasible")
        case Value.Kind.U32 => halt("Infeasible")
        case Value.Kind.U64 => halt("Infeasible")
        case Value.Kind.S8 => halt("Infeasible")
        case Value.Kind.S16 => halt("Infeasible")
        case Value.Kind.S32 => halt("Infeasible")
        case Value.Kind.S64 => halt("Infeasible")
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def complement : Value = {
      kind match {
        case Value.Kind.U8 => Value.u8(~toU8)
        case Value.Kind.U16 => Value.u16(~toU16)
        case Value.Kind.U32 => Value.u32(~toU32)
        case Value.Kind.U64 => Value.u64(~toU64)
        case Value.Kind.S8 => Value.s8(~toS8 )
        case Value.Kind.S16 => Value.s16(~toS16)
        case Value.Kind.S32 => Value.s32(~toS32)
        case Value.Kind.S64 => Value.s64(~toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }
    @strictpure def minus : Value = {
      kind match {
        case Value.Kind.U8 => Value.u8(-toU8)
        case Value.Kind.U16 => Value.u16(-toU16)
        case Value.Kind.U32 => Value.u32(-toU32)
        case Value.Kind.U64 => Value.u64(-toU64)
        case Value.Kind.S8 => Value.s8(-toS8 )
        case Value.Kind.S16 => Value.s16(-toS16)
        case Value.Kind.S32 => Value.s32(-toS32)
        case Value.Kind.S64 => Value.s64(-toS64)
        case Value.Kind.F32 => Value.f32(-toF32)
        case Value.Kind.F64 => Value.f64(-toF64)
      }
    }

    @strictpure def toB: B = value != 0
    @strictpure def toU8: U8 = conversions.Z.toU8(value)
    @strictpure def toU16: U16 = conversions.Z.toU16(value)
    @strictpure def toU32: U32 = conversions.Z.toU32(value)
    @strictpure def toU64: U64 = conversions.Z.toU64(value)
    @strictpure def toS8: S8 = conversions.Z.toS8(value)
    @strictpure def toS16: S16 = conversions.Z.toS16(value)
    @strictpure def toS32: S32 = conversions.Z.toS32(value)
    @strictpure def toS64: S64 = conversions.Z.toS64(value)
    @strictpure def toF32: F32 = conversions.U32.toRawF32(conversions.Z.toU32(value))
    @strictpure def toF64: F64 = conversions.U64.toRawF64(conversions.Z.toU64(value))
    @strictpure def toU: U = anvil.Printer.Ext.z2u(value)
  }

  object Value {
    @enum object Kind {
      "S8"
      "S16"
      "S32"
      "S64"
      "U8"
      "U16"
      "U32"
      "U64"
      "F32"
      "F64"
    }
    @strictpure def b(n: B): Value = Value(Kind.U8, if (n) 0 else 1)
    @strictpure def u8(n: U8): Value = Value(Kind.U8, n.toZ)
    @strictpure def u16(n: U16): Value = Value(Kind.U16, n.toZ)
    @strictpure def u32(n: U32): Value = Value(Kind.U32, n.toZ)
    @strictpure def u64(n: U64): Value = Value(Kind.U64, n.toZ)
    @strictpure def s8(n: S8): Value = Value(Kind.U8, n.toZ)
    @strictpure def s16(n: S16): Value = Value(Kind.S16, n.toZ)
    @strictpure def s32(n: S32): Value = Value(Kind.S32, n.toZ)
    @strictpure def s64(n: S64): Value = Value(Kind.S64, n.toZ)
    @strictpure def f32(n: F32): Value = Value(Kind.F32, conversions.F32.toRawU32(n).toZ)
    @strictpure def f64(n: F64): Value = Value(Kind.F64, conversions.F64.toRawU64(n).toZ)
    @strictpure def z(n: Z, isSigned: B, bytes: Z): Value = (isSigned, bytes) match {
      case (T, z"1") => Value(Value.Kind.S8, n)
      case (T, z"2") => Value(Value.Kind.S16, n)
      case (T, z"4") => Value(Value.Kind.S32, n)
      case (T, z"8") => Value(Value.Kind.S64, n)
      case (F, z"1") => Value(Value.Kind.U8, n)
      case (F, z"2") => Value(Value.Kind.U16, n)
      case (F, z"4") => Value(Value.Kind.U32, n)
      case (F, z"8") => Value(Value.Kind.U64, n)
      case (_, _) => halt(s"Infeasible: $n, $isSigned, $bytes")
    }
    @strictpure def u(n: U): Value = Value(Kind.U64, n.toZ)
  }
}

import AnvilSimulator._

@datatype class AnvilSimulator(val anvil: Anvil) {
  @pure def evalExp(state: State, exp: AST.IR.Exp): Value = {
    exp match {
      case exp: AST.IR.Exp.Bool => return Value.b(exp.value)
      case exp: AST.IR.Exp.Int => return Value.z(exp.value, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe))
      case exp: AST.IR.Exp.F32 => return Value.f32(exp.value)
      case exp: AST.IR.Exp.F64 => return Value.f64(exp.value)
      case exp: AST.IR.Exp.Temp => return Value.u64(state.temps(exp.n))
      case exp: AST.IR.Exp.Binary =>
        val left = evalExp(state, exp.left)
        val right = evalExp(state, exp.right)
        exp.op match {
          case AST.IR.Exp.Binary.Op.Add => return left + right
          case AST.IR.Exp.Binary.Op.Sub => return left - right
          case AST.IR.Exp.Binary.Op.Mul => return left * right
          case AST.IR.Exp.Binary.Op.Div => return left / right
          case AST.IR.Exp.Binary.Op.Rem => return left % right
          case AST.IR.Exp.Binary.Op.Shr => return left >> right
          case AST.IR.Exp.Binary.Op.Shl => return left << right
          case AST.IR.Exp.Binary.Op.Ushr => return left >>> right
          case AST.IR.Exp.Binary.Op.Lt => return left < right
          case AST.IR.Exp.Binary.Op.Le => return left <= right
          case AST.IR.Exp.Binary.Op.Gt => return left > right
          case AST.IR.Exp.Binary.Op.Ge => return left >= right
          case AST.IR.Exp.Binary.Op.Eq => return Value.b(left == right)
          case AST.IR.Exp.Binary.Op.Ne => return Value.b(left != right)
          case AST.IR.Exp.Binary.Op.FpEq => return left ~~ right
          case AST.IR.Exp.Binary.Op.FpNe => return left !~ right
          case AST.IR.Exp.Binary.Op.And => return left & right
          case AST.IR.Exp.Binary.Op.Or => return left | right
          case AST.IR.Exp.Binary.Op.Xor => return left |^ right
          case AST.IR.Exp.Binary.Op.Imply => return left __>: right
          case AST.IR.Exp.Binary.Op.CondAnd => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.CondOr => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.CondImply => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.Append => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.AppendAll => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.Prepend => halt(s"Infeasible: $exp")
        }
      case exp: AST.IR.Exp.Unary =>
        val v = evalExp(state, exp.exp)
        exp.op match {
          case AST.Exp.UnaryOp.Not => return v.not
          case AST.Exp.UnaryOp.Complement => return v.complement
          case AST.Exp.UnaryOp.Plus => return v
          case AST.Exp.UnaryOp.Minus => return v.minus
        }
      case exp: AST.IR.Exp.Type =>
        val v = evalExp(state, exp.exp)
        return Value.z(v.value, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe))
      case exp: AST.IR.Exp.Intrinsic =>
        exp.intrinsic match {
          case in: Intrinsic.Load =>
            val offset = evalExp(state, in.rhsOffset)
            val n = Printer.load(state.memory.toMS, offset.toU, Printer.Ext.z2u(in.bytes))
            return Value.z(n.toZ, in.isSigned, in.bytes)
          case in: Intrinsic.Register => halt(s"TODO: ${exp.prettyST}")
        }
      case exp: AST.IR.Exp.R => halt(s"TODO: ${exp.prettyST}")
      case exp: AST.IR.Exp.Construct => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.String => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.Indexing => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.LocalVarRef => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.GlobalVarRef => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.FieldVarRef => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.EnumElementRef => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.If => halt(s"Infeasible: ${exp.prettyST}")
      case _: AST.IR.Exp.Apply => halt(s"Infeasible: ${exp.prettyST}")
    }
  }

  @pure def evalStmt(state: State, stmt: AST.IR.Stmt.Ground): State => State = {
    stmt match {
      case stmt: AST.IR.Stmt.Assign.Temp =>
        val rhs = evalExp(state, stmt.rhs)
        assert(rhs.kind == Value.Kind.U64)
        val temps = state.temps(stmt.lhs ~> conversions.Z.toU64(rhs.value))
        return (s: State) => s(temps = temps)
      case stmt: AST.IR.Stmt.Intrinsic =>
        stmt.intrinsic match {
          case in: Intrinsic.TempLoad =>
            val offset = evalExp(state, in.rhsOffset)
            val n = Printer.load(state.memory.toMS, offset.toU, Printer.Ext.z2u(in.bytes)).toZ
            val v: U64 = if (anvil.isSigned(in.tipe)) {
              in.bytes match {
                case z"1" => anvil.signExtend(n, u64"56")
                case z"2" => anvil.signExtend(n, u64"48")
                case z"4" => anvil.signExtend(n, u64"32")
                case z"8" => conversions.Z.toU64(n)
                case _ => halt(s"Infeasible: $in")
              }
            } else {
              conversions.Z.toU64(n)
            }
            val temps = state.temps(in.temp ~> v)
            return (s: State) => s(temps = temps)
          case in: Intrinsic.Store =>
            val n: U = {
              val v = evalExp(state, in.rhs).value
              if (in.isSigned) {
                val bits: U64 = in.bytes match {
                  case z"1" => u64"56"
                  case z"2" => u64"48"
                  case z"4" => u64"32"
                  case z"8" => u64"0"
                  case _ => halt(s"Infeasible: $in")
                }
                Printer.Ext.z2u(anvil.signExtend(v, bits).toZ)
              } else {
                Printer.Ext.z2u(v)
              }
            }
            val offset = evalExp(state, in.lhsOffset)
            val memory = state.memory.toMS
            Printer.store(memory, Printer.Ext.z2u(offset.value), Printer.Ext.z2u(anvil.typeByteSize(in.tipe)), n)
            val mem = memory.toIS[U8]
            return (s: State) => s(memory = mem)
          case in: Intrinsic.Copy =>
            val lhsOffset = Printer.Ext.z2u(evalExp(state, in.lhsOffset).value)
            val rhsOffset = Printer.Ext.z2u(evalExp(state, in.rhs).value)
            val size = Printer.Ext.z2u(evalExp(state, in.rhsBytes).value)
            val memory = state.memory.toMS
            for (i <- u"0" until size) {
              memory(lhsOffset + i) = memory(rhsOffset + i)
            }
            val mem = memory.toIS[U8]
            return (s: State) => s(memory = mem)
          case in: Intrinsic.RegisterAssign =>
            val v = evalExp(state, in.value).value
            var memory = state.memory
            if (in.isSP) {
              val sp: U64 = conversions.Z.toU64(if (in.isInc) conversions.U64.toZ(state.SP) + v else v)
              if (anvil.config.erase) {
                val (lo, hi): (U64, U64) = if (sp < state.SP) (sp, state.SP) else (state.SP, sp)
                val mem = memory.toMS
                for (i <- Printer.Ext.z2u(lo.toZ) until Printer.Ext.z2u(hi.toZ)) {
                  mem(i) = u8"0"
                }
                memory = mem.toIS[U8]
              }
              return (s: State) => s(SP = sp, memory = memory)
            } else {
              assert(v > 0)
              val dp: U64 = conversions.Z.toU64(if (in.isInc) conversions.U64.toZ(state.DP) + v else v)
              return (s: State) => s(DP = dp)
            }
          case _: Intrinsic.Decl => return (s: State) => s
        }
      case _: AST.IR.Stmt.Expr => halt(s"Infeasible: ${stmt.prettyST}")
      case _: AST.IR.Stmt.Decl => halt(s"Infeasible: ${stmt.prettyST}")
      case _: AST.IR.Stmt.Assign => halt(s"Infeasible: ${stmt.prettyST}")
    }
  }

  @pure def evalJump(state: State, jump: AST.IR.Jump): State => State = {
    jump match {
      case jump: AST.IR.Jump.Goto =>
        val cp = conversions.Z.toU64(jump.label)
        return (s: State) => s(CP = cp)
      case jump: AST.IR.Jump.If =>
        val label: Z = if (evalExp(state, jump.cond).toB) jump.thenLabel else jump.elseLabel
        val cp = conversions.Z.toU64(label)
        return (s: State) => s(CP = cp)
      case jump: AST.IR.Jump.Switch =>
        val v = evalExp(state, jump.exp).value
        var label: Z = 1
        var found = F
        for (c <- jump.cases if !found) {
          if (v == evalExp(state, c.value).value) {
            found = T
            label = c.label
          }
        }
        if (!found) {
          jump.defaultLabelOpt match {
            case Some(l) =>
              found = T
              label = l
            case _ =>
          }
        }
        assert(found)
        val cp = conversions.Z.toU64(label)
        return (s: State) => s(CP = cp)
      case jump: AST.IR.Jump.Intrinsic =>
        jump.intrinsic match {
          case in: Intrinsic.GotoLocal =>
            val offset = Printer.Ext.z2u(state.SP.toZ + in.offset)
            val cp = conversions.Z.toU64(Printer.load(state.memory.toMS, offset,
              Printer.Ext.z2u(anvil.spTypeByteSize)).toZ)
            return (s: State) => s(CP = cp)
        }
      case _: AST.IR.Jump.Return => halt(s"Infeasible: ${jump.prettyST}")
      case _: AST.IR.Jump.Halt => halt(s"Infeasible: ${jump.prettyST}")
    }
  }

  @pure def evalBlock(state: State, b: AST.IR.BasicBlock): State = {
    @pure def evalStmtH(g: AST.IR.Stmt.Ground): State => State = {
      return evalStmt(state, g)
    }
    var s = state
    for (f <- ops.ISZOps(b.grounds).parMap(evalStmtH _) :+ evalJump(s, b.jump)) {
      s = f(s)
    }
    return s
  }

  @pure def evalProcedure(state: State, p: AST.IR.Procedure): State = {
    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val blockMap: HashMap[U64, AST.IR.BasicBlock] = HashMap ++
      (for (b <- body.blocks) yield (conversions.Z.toU64(b.label), b))
    var s = state(CP = conversions.Z.toU64(body.blocks(0).label))
    while (s.CP != u64"0" && s.CP != u64"1") {
      s = evalBlock(s, blockMap.get(s.CP).get)
    }
    return s
  }
}