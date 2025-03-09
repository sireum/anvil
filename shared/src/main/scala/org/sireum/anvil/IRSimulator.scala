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
import org.sireum.U8._
import org.sireum.U64._

object IRSimulator {
  @record @unclonable class State(val memory: MSZ[U8], val temps: MSZ[U64]) {
    def cpIndex: Z = {
      return temps.size - 3
    }

    def spIndex: Z = {
      return temps.size - 2
    }

    def dpIndex: Z = {
      return temps.size - 1
    }

    def CP: U64 = {
      return temps(cpIndex)
    }

    def upCP(cp: U64): Unit = {
      temps(cpIndex) = cp
    }

    def SP: U64 = {
      return temps(spIndex)
    }

    def upSP(sp: U64): Unit = {
      temps(spIndex) = sp
    }

    def DP: U64 = {
      return temps(dpIndex)
    }

    def upDP(dp: U64): Unit = {
      temps(dpIndex) = dp
    }

    @pure override def string: String = {
      return s"CP = ${temps(temps.size - 3).toZ}, SP = ${SP.toZ}, DP = ${DP.toZ}, temps = ${for (i <- 0 until temps.size - 3) yield temps(i).toZ}"
    }
  }

  object State {
    type Undo = Edit

    @datatype trait Edit {
      def update(state: State): Undo
    }

    object Edit {
      @datatype class Idem extends Edit {
        def update(state: State): Undo = {
          return this
        }
      }

      @datatype class CP(val cp: U64) extends Edit {
        def update(state: State): Undo = {
          val r = CP(state.CP)
          state.upCP(cp)
          return r
        }
      }

      @datatype class SP(val sp: U64) extends Edit {
        def update(state: State): Undo = {
          val r = SP(state.SP)
          state.upSP(sp)
          return r
        }
      }

      @datatype class DP(val dp: U64) extends Edit {
        def update(state: State): Undo = {
          val r = DP(state.DP)
          state.upDP(dp)
          return r
        }
      }

      @datatype class Temp(val temp: Z, val value: U64) extends Edit {
        def update(state: State): Undo = {
          val r = Temp(temp, state.temps(temp))
          state.temps(temp) = value
          return r
        }
      }

      @datatype class Memory(val offset: Z, val values: ISZ[U8]) extends Edit {
        def update(state: State): Undo = {
          val r = Memory(offset, for (i <- values.indices) yield state.memory(offset + i))
          for (i <- values.indices) {
            state.memory(offset + i) = values(i)
          }
          return r
        }
      }
    }

    @strictpure def create(memory: Z, temps: Z): State = State(MSZ.create(memory, u8"0"), MSZ.create(temps + 3, u64"0"))

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
        case Value.Kind.U8 => Value.fromU8(toU8 + other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 + other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 + other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 + other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 + other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 + other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 + other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 + other.toS64)
        case Value.Kind.F32 => Value.fromF32(toF32 + other.toF32)
        case Value.Kind.F64 => Value.fromF64(toF64 + other.toF64)
      }
    }

    @strictpure def -(other: Value): Value = {
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 - other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 - other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 - other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 - other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 - other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 - other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 - other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 - other.toS64)
        case Value.Kind.F32 => Value.fromF32(toF32 - other.toF32)
        case Value.Kind.F64 => Value.fromF64(toF64 - other.toF64)
      }
    }

    @strictpure def *(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 * other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 * other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 * other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 * other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 * other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 * other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 * other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 * other.toS64)
        case Value.Kind.F32 => Value.fromF32(toF32 * other.toF32)
        case Value.Kind.F64 => Value.fromF64(toF64 * other.toF64)
      }
    }

    @strictpure def /(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 / other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 / other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 / other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 / other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 / other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 / other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 / other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 / other.toS64)
        case Value.Kind.F32 => Value.fromF32(toF32 / other.toF32)
        case Value.Kind.F64 => Value.fromF64(toF64 / other.toF64)
      }
    }

    @strictpure def %(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 % other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 % other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 % other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 % other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 % other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 % other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 % other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 % other.toS64)
        case Value.Kind.F32 => Value.fromF32(toF32 % other.toF32)
        case Value.Kind.F64 => Value.fromF64(toF64 % other.toF64)
      }
    }

    @strictpure def >>(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 >> other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 >> other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 >> other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 >> other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 >> other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 >> other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 >> other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 >> other.toS64)
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
        case Value.Kind.F32 => Value.fromB(toF32 ~~ other.toF32)
        case Value.Kind.F64 => Value.fromB(toF32 ~~ other.toF32)
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
        case Value.Kind.F32 => Value.fromB(toF32 !~ other.toF32)
        case Value.Kind.F64 => Value.fromB(toF32 !~ other.toF32)
      }
    }

    @strictpure def >>>(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 >>> other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 >>> other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 >>> other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 >>> other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 >>> other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 >>> other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 >>> other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 >>> other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }

    @strictpure def <<(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 << other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 << other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 << other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 << other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 << other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 << other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 << other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 << other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }

    @strictpure def &(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 & other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 & other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 & other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 & other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 & other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 & other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 & other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 & other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }

    @strictpure def |(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 | other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 | other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 | other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 | other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 | other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 | other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 | other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 | other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }

    @strictpure def |^(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromU8(toU8 |^ other.toU8)
        case Value.Kind.U16 => Value.fromU16(toU16 |^ other.toU16)
        case Value.Kind.U32 => Value.fromU32(toU32 |^ other.toU32)
        case Value.Kind.U64 => Value.fromU64(toU64 |^ other.toU64)
        case Value.Kind.S8 => Value.fromS8(toS8 |^ other.toS8)
        case Value.Kind.S16 => Value.fromS16(toS16 |^ other.toS16)
        case Value.Kind.S32 => Value.fromS32(toS32 |^ other.toS32)
        case Value.Kind.S64 => Value.fromS64(toS64 |^ other.toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }

    @strictpure def __>:(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromB(!toB | other.toB)
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
        case Value.Kind.U8 => Value.fromB(toU8 < other.toU8)
        case Value.Kind.U16 => Value.fromB(toU16 < other.toU16)
        case Value.Kind.U32 => Value.fromB(toU32 < other.toU32)
        case Value.Kind.U64 => Value.fromB(toU64 < other.toU64)
        case Value.Kind.S8 => Value.fromB(toS8 < other.toS8)
        case Value.Kind.S16 => Value.fromB(toS16 < other.toS16)
        case Value.Kind.S32 => Value.fromB(toS32 < other.toS32)
        case Value.Kind.S64 => Value.fromB(toS64 < other.toS64)
        case Value.Kind.F32 => Value.fromB(toF32 < other.toF32)
        case Value.Kind.F64 => Value.fromB(toF64 < other.toF64)
      }
    }

    @strictpure def <=(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromB(toU8 <= other.toU8)
        case Value.Kind.U16 => Value.fromB(toU16 <= other.toU16)
        case Value.Kind.U32 => Value.fromB(toU32 <= other.toU32)
        case Value.Kind.U64 => Value.fromB(toU64 <= other.toU64)
        case Value.Kind.S8 => Value.fromB(toS8 <= other.toS8)
        case Value.Kind.S16 => Value.fromB(toS16 <= other.toS16)
        case Value.Kind.S32 => Value.fromB(toS32 <= other.toS32)
        case Value.Kind.S64 => Value.fromB(toS64 <= other.toS64)
        case Value.Kind.F32 => Value.fromB(toF32 <= other.toF32)
        case Value.Kind.F64 => Value.fromB(toF64 <= other.toF64)
      }
    }

    @strictpure def >(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromB(toU8 > other.toU8)
        case Value.Kind.U16 => Value.fromB(toU16 > other.toU16)
        case Value.Kind.U32 => Value.fromB(toU32 > other.toU32)
        case Value.Kind.U64 => Value.fromB(toU64 > other.toU64)
        case Value.Kind.S8 => Value.fromB(toS8 > other.toS8)
        case Value.Kind.S16 => Value.fromB(toS16 > other.toS16)
        case Value.Kind.S32 => Value.fromB(toS32 > other.toS32)
        case Value.Kind.S64 => Value.fromB(toS64 > other.toS64)
        case Value.Kind.F32 => Value.fromB(toF32 > other.toF32)
        case Value.Kind.F64 => Value.fromB(toF64 > other.toF64)
      }
    }

    @strictpure def >=(other: Value): Value = {
      assert(kind == other.kind)
      kind match {
        case Value.Kind.U8 => Value.fromB(toU8 >= other.toU8)
        case Value.Kind.U16 => Value.fromB(toU16 >= other.toU16)
        case Value.Kind.U32 => Value.fromB(toU32 >= other.toU32)
        case Value.Kind.U64 => Value.fromB(toU64 >= other.toU64)
        case Value.Kind.S8 => Value.fromB(toS8 >= other.toS8)
        case Value.Kind.S16 => Value.fromB(toS16 >= other.toS16)
        case Value.Kind.S32 => Value.fromB(toS32 >= other.toS32)
        case Value.Kind.S64 => Value.fromB(toS64 >= other.toS64)
        case Value.Kind.F32 => Value.fromB(toF32 >= other.toF32)
        case Value.Kind.F64 => Value.fromB(toF64 >= other.toF64)
      }
    }

    @strictpure def not: Value = {
      kind match {
        case Value.Kind.U8 => Value.fromB(!toB)
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

    @strictpure def complement: Value = {
      kind match {
        case Value.Kind.U8 => Value.fromU8(~toU8)
        case Value.Kind.U16 => Value.fromU16(~toU16)
        case Value.Kind.U32 => Value.fromU32(~toU32)
        case Value.Kind.U64 => Value.fromU64(~toU64)
        case Value.Kind.S8 => Value.fromS8(~toS8)
        case Value.Kind.S16 => Value.fromS16(~toS16)
        case Value.Kind.S32 => Value.fromS32(~toS32)
        case Value.Kind.S64 => Value.fromS64(~toS64)
        case Value.Kind.F32 => halt("Infeasible")
        case Value.Kind.F64 => halt("Infeasible")
      }
    }

    @strictpure def minus: Value = {
      kind match {
        case Value.Kind.U8 => Value.fromU8(-toU8)
        case Value.Kind.U16 => Value.fromU16(-toU16)
        case Value.Kind.U32 => Value.fromU32(-toU32)
        case Value.Kind.U64 => Value.fromU64(-toU64)
        case Value.Kind.S8 => Value.fromS8(-toS8)
        case Value.Kind.S16 => Value.fromS16(-toS16)
        case Value.Kind.S32 => Value.fromS32(-toS32)
        case Value.Kind.S64 => Value.fromS64(-toS64)
        case Value.Kind.F32 => Value.fromF32(-toF32)
        case Value.Kind.F64 => Value.fromF64(-toF64)
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

    @strictpure def fromB(n: B): Value = Value(Kind.U8, if (n) 1 else 0)

    @strictpure def fromU8(n: U8): Value = Value(Kind.U8, n.toZ)

    @strictpure def fromU16(n: U16): Value = Value(Kind.U16, n.toZ)

    @strictpure def fromU32(n: U32): Value = Value(Kind.U32, n.toZ)

    @strictpure def fromU64(n: U64): Value = Value(Kind.U64, n.toZ)

    @strictpure def fromS8(n: S8): Value = Value(Kind.S8, n.toZ)

    @strictpure def fromS16(n: S16): Value = Value(Kind.S16, n.toZ)

    @strictpure def fromS32(n: S32): Value = Value(Kind.S32, n.toZ)

    @strictpure def fromS64(n: S64): Value = Value(Kind.S64, n.toZ)

    @strictpure def fromF32(n: F32): Value = Value(Kind.F32, conversions.F32.toRawU32(n).toZ)

    @strictpure def fromF64(n: F64): Value = Value(Kind.F64, conversions.F64.toRawU64(n).toZ)

    @strictpure def fromZ(n: Z, isSigned: B, bytes: Z): Value =
      if (isSigned) {
        if (bytes == 1) {
          Value(Value.Kind.S8, n)
        } else if (bytes == 2) {
          Value(Value.Kind.S16, n)
        } else if (bytes <= 4) {
          Value(Value.Kind.S32, n)
        } else if (bytes <= 8) {
          Value(Value.Kind.S64, n)
        } else {
          halt(s"Infeasible: $n, $isSigned, $bytes")
        }
      } else {
        if (bytes == 1) {
          Value(Value.Kind.U8, n)
        } else if (bytes == 2) {
          Value(Value.Kind.U16, n)
        } else if (bytes <= 4) {
          Value(Value.Kind.U32, n)
        } else if (bytes <= 8) {
          Value(Value.Kind.U64, n)
        } else {
          halt(s"Infeasible: $n, $isSigned, $bytes")
        }
      }

    @strictpure def fromRawU64(n: U64, isSigned: B, bytes: Z): Value = if (isSigned) {
      if (bytes == 1) {
        fromS8(conversions.U8.toRawS8(conversions.U64.toU8(n & u64"0xFF")))
      } else if (bytes == 2) {
        fromS16(conversions.U16.toRawS16(conversions.U64.toU16(n & u64"0xFFFF")))
      } else if (bytes <= 4) {
        fromS32(conversions.U32.toRawS32(conversions.U64.toU32(n & u64"0xFFFFFFFF")))
      } else if (bytes <= 8) {
        fromS64(conversions.U64.toRawS64(n))
      } else {
        halt(s"Infeasible: $bytes")
      }
    } else {
      if (bytes == 1) {
        fromU8(conversions.U64.toU8(n))
      } else if (bytes == 2) {
        fromU16(conversions.U64.toU16(n))
      } else if (bytes <= 4) {
        fromU32(conversions.U64.toU32(n))
      } else if (bytes <= 8) {
        fromU64(n)
      } else {
        halt(s"Infeasible: $bytes")
      }
    }
  }
}

import IRSimulator._

@datatype class IRSimulator(val anvil: Anvil) {

  @pure def evalExp(state: State, exp: AST.IR.Exp): Value = {
    exp match {
      case exp: AST.IR.Exp.Bool => return Value.fromB(exp.value)
      case exp: AST.IR.Exp.Int => return Value.fromZ(exp.value, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe))
      case exp: AST.IR.Exp.F32 => return Value.fromF32(exp.value)
      case exp: AST.IR.Exp.F64 => return Value.fromF64(exp.value)
      case exp: AST.IR.Exp.Temp =>
        val v = state.temps(exp.n)
        if (anvil.isScalar(exp.tipe)) {
          return Value.fromRawU64(v, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe))
        } else {
          return Value.fromRawU64(v, anvil.isSigned(anvil.spType), anvil.typeByteSize(anvil.spType))
        }
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
          case AST.IR.Exp.Binary.Op.Eq => return Value.fromB(left == right)
          case AST.IR.Exp.Binary.Op.Ne => return Value.fromB(left != right)
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
        val n: U64 =
          if (anvil.isSigned(exp.t)) conversions.S64.toRawU64(conversions.Z.toS64(v.value))
          else conversions.Z.toU64(v.value)
        return Value.fromRawU64(n, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe))
      case exp: AST.IR.Exp.Intrinsic =>
        exp.intrinsic match {
          case in: Intrinsic.Load =>
            val offset = evalExp(state, in.rhsOffset)
            val n = load(state.memory, offset.value, in.bytes)
            return Value.fromRawU64(conversions.Z.toU64(n.toZ), in.isSigned, in.bytes)
          case in: Intrinsic.Register =>
            if (in.isSP) {
              return Value.fromRawU64(state.SP, anvil.isSigned(in.tipe), anvil.typeByteSize(in.tipe))
            } else {
              return Value.fromU64(state.DP)
            }
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

  @pure def evalStmt(state: State, stmt: AST.IR.Stmt.Ground): State.Edit = {
    stmt match {
      case stmt: AST.IR.Stmt.Assign.Temp =>
        val rhs = evalExp(state, stmt.rhs)
        val n: U64 =
          if (anvil.isSigned(stmt.rhs.tipe)) conversions.S64.toRawU64(conversions.Z.toS64(rhs.value))
          else conversions.Z.toU64(rhs.value)
        return State.Edit.Temp(stmt.lhs, n)
      case stmt: AST.IR.Stmt.Intrinsic =>
        stmt.intrinsic match {
          case in: Intrinsic.TempLoad =>
            val offset = evalExp(state, in.rhsOffset)
            val v = Value.fromRawU64(load(state.memory, offset.value, in.bytes), in.isSigned, in.bytes)
            val n: U64 =
              if (in.isSigned) conversions.S64.toRawU64(conversions.Z.toS64(v.value))
              else conversions.Z.toU64(v.value)
            return State.Edit.Temp(in.temp, n)
          case in: Intrinsic.Store =>
            val n: U64 = {
              val v = evalExp(state, in.rhs)
              if (in.isSigned) conversions.S64.toRawU64(conversions.Z.toS64(v.value)) else v.toU64
            }
            val offset = evalExp(state, in.lhsOffset)
            return store(offset.value, anvil.typeByteSize(in.tipe), n)
          case in: Intrinsic.Copy =>
            val lhsOffset = evalExp(state, in.lhsOffset).value
            val rhsOffset = evalExp(state, in.rhs).value
            val size = evalExp(state, in.rhsBytes).value
            var bs = ISZ[U8]()
            for (i <- 0 until size) {
              bs = bs :+ state.memory(rhsOffset + i)
            }
            return State.Edit.Memory(lhsOffset, bs)
          case in: Intrinsic.RegisterAssign =>
            val v = evalExp(state, in.value).value
            if (in.isSP) {
              val sp: U64 = conversions.Z.toU64(if (in.isInc) conversions.U64.toZ(state.SP) + v else v)
              return State.Edit.SP(sp)
            } else {
              assert(v >= 0)
              val dp: U64 = conversions.Z.toU64(if (in.isInc) conversions.U64.toZ(state.DP) + v else v)
              return State.Edit.DP(dp)
            }
          case _: Intrinsic.Decl => return State.Edit.Idem()
        }
      case _: AST.IR.Stmt.Expr => halt(s"Infeasible: ${stmt.prettyST}")
      case _: AST.IR.Stmt.Decl => halt(s"Infeasible: ${stmt.prettyST}")
      case _: AST.IR.Stmt.Assign => halt(s"Infeasible: ${stmt.prettyST}")
    }
  }

  @pure def evalJump(state: State, jump: AST.IR.Jump): State.Edit.CP = {
    jump match {
      case jump: AST.IR.Jump.Goto =>
        val cp = conversions.Z.toU64(jump.label)
        return State.Edit.CP(cp)
      case jump: AST.IR.Jump.If =>
        val label: Z = if (evalExp(state, jump.cond).toB) jump.thenLabel else jump.elseLabel
        val cp = conversions.Z.toU64(label)
        return State.Edit.CP(cp)
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
        return State.Edit.CP(cp)
      case jump: AST.IR.Jump.Intrinsic =>
        jump.intrinsic match {
          case in: Intrinsic.GotoLocal =>
            val offset = state.SP.toZ + in.offset
            val cp = load(state.memory, offset, anvil.cpTypeByteSize)
            return State.Edit.CP(cp)
        }
      case _: AST.IR.Jump.Return => halt(s"Infeasible: ${jump.prettyST}")
      case _: AST.IR.Jump.Halt => halt(s"Infeasible: ${jump.prettyST}")
    }
  }

  @strictpure def evalGroundOrJump(e: Either[AST.IR.Stmt.Ground, AST.IR.Jump]): State => State.Edit = (s: State) => {
    e match {
      case Either.Left(g) => evalStmt(s, g)
      case Either.Right(j) => evalJump(s, j)
    }
  }

  @pure def evalBlock(state: State, b: AST.IR.BasicBlock): ISZ[State.Edit] = {
    return ops.ISZOps((for (g <- b.grounds) yield evalGroundOrJump(Either.Left(g))) :+
      evalGroundOrJump(Either.Right(b.jump))).parMapUnordered((f: State => State.Edit) => f(state))
  }

  def evalProcedure(state: State, p: AST.IR.Procedure): Unit = {
    def log(title: String, b: AST.IR.BasicBlock): Unit = {
      val pos: message.Position = if (b.grounds.nonEmpty) b.grounds(0).pos else b.jump.pos
      var file = pos.uriOpt.get
      val i = ops.StringOps(file).lastIndexOf('/')
      if (i >= 0) {
        file = ops.StringOps(file).substring(i + 1, file.size)
      }
      println(s"$title block ${b.label}: $state")
    }

    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val blockMap: HashMap[U64, AST.IR.BasicBlock] = HashMap ++
      (for (b <- body.blocks) yield (conversions.Z.toU64(b.label), b))

    state.upCP(conversions.Z.toU64(body.blocks(0).label))

    while (state.CP != u64"0" && state.CP != u64"1") {
      val b = blockMap.get(state.CP).get
      log("Evaluating", b)
      val edits = evalBlock(state, b)
      var i = 0
      while (i < edits.size) {
        edits(i).update(state)
        i = i + 1
      }
    }

    println(s"End state: $state")
  }

  @pure def load(memory: MSZ[U8], offset: Z, size: Z): U64 = {
    var r = u64"0"
    var i: Z = 0
    while (i < size) {
      val b = conversions.U8.toU64(memory(offset + i))
      r = r | (b << conversions.Z.toU64((size - i - 1) * 8))
      i = i + 1
    }
    return r
  }

  @pure def store(offset: Z, size: Z, value: U64): State.Edit.Memory = {
    var bs = ISZ[U8]()
    for (i <- 0 until size) {
      val b = conversions.U64.toU8((value >> conversions.Z.toU64((size - i - 1) * 8)) & u64"0xFF")
      bs = bs :+ b
    }
    return State.Edit.Memory(offset, bs)
  }
}