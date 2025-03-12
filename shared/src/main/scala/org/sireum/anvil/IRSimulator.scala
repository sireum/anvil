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
import org.sireum.lang.symbol.Resolver.QName

object IRSimulator {
  val DEBUG: B = T
  var DEBUG_EDIT: B = T
  var DEBUG_GLOBAL: B = T
  var DEBUG_LOCAL: B = T

  @record @unclonable class State(val globalMap: HashSMap[QName, Anvil.VarInfo],
                                  val memory: MSZ[U8], val temps: MSZ[U64],
                                  var callFrames: Stack[HashSMap[String, Intrinsic.Decl.Local]]) {
    @pure def cpIndex: Z = {
      return temps.size - 3
    }

    @pure def spIndex: Z = {
      return temps.size - 2
    }

    @pure def dpIndex: Z = {
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

    @strictpure def tempST(temp: Z): ST =
      if (temp == spIndex) st"SP"
      else if (temp == cpIndex) st"CP"
      else if (temp == dpIndex) st"DP"
      else st"$$$temp"

    @strictpure def tempsST(temps: ISZ[Z]): ST = st"${(for (t <- temps) yield tempST(t), ", ")}"

    @pure def prettyST(sim: IRSimulator): ST = {
      val globalSTOpt: Option[ST] = if (DEBUG_GLOBAL) {
        var globalSTs = ISZ[ST]()
        for (entry <- globalMap.entries) {
          val (name, info) = entry
          if (info.isScalar) {
            val v = sim.load(memory, info.offset, info.size)._1
            globalSTs = globalSTs :+ st"${(name, ".")}@[${shortenHexString(conversions.Z.toU64(info.offset))} (${info.offset}), ${info.size}] = ${shortenHexString(v)} (${v.toZ})"
          } else {
            globalSTs = globalSTs :+ st"${(name, ".")}@[${shortenHexString(conversions.Z.toU64(info.offset))} (${info.offset}), ${info.size}] = ..."
          }
        }
        Some(
          st""", globals = {
              |  ${(globalSTs, ",\n")}
              |}""")
      } else {
        None()
      }
      var localSTOpt: Option[ST] = if (DEBUG_LOCAL) {
        var localSTs = ISZ[ST]()
        for (entry <- callFrames.peek.get.entries) {
          val (id, info) = entry
          val offset = SP.toZ + info.offset
          if (sim.anvil.isScalar(info.tipe)) {
            val v = sim.load(memory, offset, info.size)._1
            localSTs = localSTs :+ st"$id@[${shortenHexString(conversions.Z.toU64(offset))} ($offset), ${info.size}] = ${shortenHexString(v)} (${v.toZ})"
          } else if (id == Util.sfDescId) {
            val size = Z(info.tipe.asInstanceOf[AST.Typed.Name].args(0).string).get
            val descOffset = offset + sim.anvil.typeShaSize + sim.anvil.typeByteSize(AST.Typed.z)
            val desc = conversions.String.fromU8ms(ops.MSZOps(memory).slice(descOffset, descOffset + size))
            val sz = sim.load(memory, offset + sim.anvil.typeShaSize, sim.anvil.typeByteSize(AST.Typed.z))._1
            val index = st"[${shortenHexString(conversions.Z.toU64(offset))} ($offset), ${info.size}; .size = ${shortenHexString(sz)} (${sz.toZ})]"
            //val t = sim.load(memory, offset, sim.anvil.typeShaSize)._1
            //localSTs = localSTs :+ st"$id@$index.type = ${shortenHexString(t)} (${t.toZ})"
            localSTs = localSTs :+ st"$id@$index = \"${ops.StringOps(desc).escapeST}\""
          } else {
            localSTs = localSTs :+ st"$id@[${shortenHexString(conversions.Z.toU64(offset))} ($offset), ${info.size}] = ..."
          }
        }
        Some(
          st""", locals = {
              |  ${(localSTs, ",\n")}
              |}""")
      } else {
        None()
      }
      val r =
        st"""CP = ${shortenHexString(CP)} (${CP.toZ}), SP = ${shortenHexString(SP)} (${SP.toZ}), DP = ${shortenHexString(DP)} (${DP.toZ}),
            |temps = [${(for (i <- 0 until temps.size - 3) yield shortenHexString(temps(i)), ", ")}]$globalSTOpt$localSTOpt"""
      return r
    }

  }

  @pure def shortenHexString(n: U64): String = {
    val r = conversions.String.toCis(n.string)
    var i: Z = 0
    while (i < r.size && r(i) == '0') {
      i = i + 1
    }
    return if (i == r.size) "0" else ops.StringOps.substring(r, i, r.size)
  }

  object State {
    type Undo = Edit

    @datatype trait Edit {
      @pure def reads: Accesses
      @pure def writes: Accesses
      def update(state: State): Undo
    }

    object Edit {

      @datatype class CallFrame(val isPush: B) extends Edit {
        @strictpure def reads: Accesses = Accesses.empty
        @strictpure def writes: Accesses = Accesses.empty
        def update(state: State): Undo = {
          if (isPush) {
            if (DEBUG_EDIT) {
              println(s"* Push a new call frame")
            }
            state.callFrames = state.callFrames.push(HashSMap.empty)
          } else {
            if (DEBUG_EDIT) {
              println(s"* Pop a call frame")
            }
            state.callFrames = state.callFrames.pop.get._2
          }
          return CallFrame(!isPush)
        }
      }

      @datatype class Decl(val decl: Intrinsic.Decl) extends Edit {
        @strictpure def reads: Accesses = Accesses.empty
        @strictpure def writes: Accesses = Accesses.empty
        def update(state: State): Undo = {
          var top = state.callFrames.peek.get
          if (DEBUG_EDIT) {
            val slotSTs: ISZ[ST] = for (slot <- decl.slots) yield st"${slot.id}@[${shortenHexString(state.SP + conversions.Z.toU64(slot.offset))}, ${slot.size}]: ${slot.tipe}"
            println(st"* ${if (decl.isAlloc) if (decl.undecl) "unalloc" else "alloc" else if (decl.undecl) "undecl" else "decl"} ${(slotSTs, ", ")}".render)
          }
          if (decl.undecl) {
            top = top -- (for (l <- decl.slots) yield l.id)
            state.callFrames = state.callFrames.pop.get._2.push(top)
            return Decl(decl(undecl = F))
          } else {
            top = top ++ (for (l <- decl.slots) yield (l.id, l))
            state.callFrames = state.callFrames.pop.get._2.push(top)
            return Decl(decl(undecl = T))
          }
        }
      }

      @datatype class Temp(val kind: Temp.Kind.Type, val temp: Z, val value: U64, val reads: Accesses) extends Edit {
        @strictpure def writes: Accesses = Accesses.empty.addTemp(temp, value)
        def update(state: State): Undo = {
          val r = Temp(kind, temp, state.temps(temp), Accesses(reads.temps -- ISZ(temp), reads.memory).
            addTemp(temp, value))
          if (DEBUG_EDIT) {
            val tempString: String = kind match {
              case Temp.Kind.CP => "CP"
              case Temp.Kind.SP => "SP"
              case Temp.Kind.DP => "DP"
              case Temp.Kind.Register => s"$$$temp"
            }
            println(s"* $tempString = ${shortenHexString(value)} (old: ${shortenHexString(r.value)})")
          }
          state.temps(temp) = value
          return r
        }
      }

      object Temp {
        @enum object Kind {
          "CP"
          "SP"
          "DP"
          "Register"
        }
      }

      @datatype class Memory(val offset: Z, val values: ISZ[U8], val reads: Accesses) extends Edit {
        @strictpure def writes: Accesses = Accesses.empty.addMemory(offset, values)
        def update(state: State): Undo = {
          val r = Memory(offset, for (i <- values.indices) yield state.memory(offset + i),
            Accesses(reads.temps, reads.memory -- (for (i <- values.indices) yield offset + i)).
              addMemory(offset, values))
          if (DEBUG_EDIT) {
            if (values.size == 1) {
              println(s"* memory(${shortenHexString(conversions.Z.toU64(offset))} ($offset)) = ${values(0)}  (old ${r.values(0)})")
            } else {
              println(s"* memory(${shortenHexString(conversions.Z.toU64(offset))} ($offset), ...) <- $values  (old ${r.values})")
            }
          }
          for (i <- values.indices) {
            state.memory(offset + i) = values(i)
          }
          return r
        }
      }
    }

    @datatype class Accesses(val temps: HashSMap[Z, U64], val memory: HashSMap[Z, U8]) {

      @pure def addTemp(temp: Z, readValue: U64): Accesses = {
        assert(temps.get(temp).getOrElse(readValue) == readValue)
        return Accesses(temps + temp ~> readValue, memory)
      }

      @pure def addMemory(offset: Z, readValues: ISZ[U8]): Accesses = {
        for (i <- readValues.indices) {
          assert(memory.get(offset + i).getOrElse(readValues(i)) == readValues(i))
        }
        return Accesses(temps, memory ++ (for (i <- 0 until readValues.size) yield (offset + i, readValues(i))))
      }

      @pure def +(other: Accesses): Accesses = {
        var r = this
        for (entry <- other.temps.entries) {
          r = r.addTemp(entry._1, entry._2)
        }
        for (entry <- other.memory.entries) {
          r = r.addMemory(entry._1, IS(entry._2))
        }
        return r
      }
    }

    object Accesses {
      @strictpure def empty: Accesses = Accesses(HashSMap.empty, HashSMap.empty)
    }

    @strictpure def create(memory: Z, temps: Z, globalMap: HashSMap[QName, Anvil.VarInfo]): State =
      State(globalMap, MSZ.create(memory, u8"0"), MSZ.create(temps + 3, u64"0"), Stack(ISZ(HashSMap.empty)))

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
      assert(kind == other.kind, s"$kind != ${other.kind}")
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
      } else if (bytes == 4) {
        fromS32(conversions.U32.toRawS32(conversions.U64.toU32(n & u64"0xFFFFFFFF")))
      } else if (bytes == 8) {
        fromS64(conversions.U64.toRawS64(n))
      } else {
        halt(s"Infeasible: $bytes")
      }
    } else {
      bytes match {
        case z"1" => fromU8(conversions.U64.toU8(n & u64"0xFF"))
        case z"2" => fromU16(conversions.U64.toU16(n & u64"0xFFFF"))
        case z"3" => fromU32(conversions.U64.toU32(n & u64"0xFFFFFF"))
        case z"4" => fromU32(conversions.U64.toU32(n & u64"0xFFFFFFFF"))
        case z"5" => fromU64(n & u64"0xFFFFFFFFFF")
        case z"6" => fromU64(n & u64"0xFFFFFFFFFFFF")
        case z"7" => fromU64(n & u64"0xFFFFFFFFFFFFFF")
        case z"8" => fromU64(n)
        case _ => halt(s"Infeasible: $bytes")
      }
    }
  }
}

import IRSimulator._

@datatype class IRSimulator(val anvil: Anvil) {

  @pure def evalExp(state: State, exp: AST.IR.Exp): (Value, State.Accesses) = {
    exp match {
      case exp: AST.IR.Exp.Bool => return (Value.fromB(exp.value), State.Accesses.empty)
      case exp: AST.IR.Exp.Int =>
        return (Value.fromZ(exp.value, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe)), State.Accesses.empty)
      case exp: AST.IR.Exp.F32 => return (Value.fromF32(exp.value), State.Accesses.empty)
      case exp: AST.IR.Exp.F64 => return (Value.fromF64(exp.value), State.Accesses.empty)
      case exp: AST.IR.Exp.Temp =>
        val v = state.temps(exp.n)
        val acs = State.Accesses.empty.addTemp(exp.n, v)
        if (anvil.isScalar(exp.tipe)) {
          return (Value.fromRawU64(v, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe)), acs)
        } else {
          return (Value.fromRawU64(v, anvil.isSigned(anvil.spType), anvil.typeByteSize(anvil.spType)), acs)
        }
      case exp: AST.IR.Exp.Binary =>
        val (left, lacs) = evalExp(state, exp.left)
        val (right, racs) = evalExp(state, exp.right)
        val acs = lacs + racs
        exp.op match {
          case AST.IR.Exp.Binary.Op.Add => return (left + right, acs)
          case AST.IR.Exp.Binary.Op.Sub => return (left - right, acs)
          case AST.IR.Exp.Binary.Op.Mul => return (left * right, acs)
          case AST.IR.Exp.Binary.Op.Div => return (left / right, acs)
          case AST.IR.Exp.Binary.Op.Rem => return (left % right, acs)
          case AST.IR.Exp.Binary.Op.Shr => return (left >> right, acs)
          case AST.IR.Exp.Binary.Op.Shl => return (left << right, acs)
          case AST.IR.Exp.Binary.Op.Ushr => return (left >>> right, acs)
          case AST.IR.Exp.Binary.Op.Lt => return (left < right, acs)
          case AST.IR.Exp.Binary.Op.Le => return (left <= right, acs)
          case AST.IR.Exp.Binary.Op.Gt => return (left > right, acs)
          case AST.IR.Exp.Binary.Op.Ge => return (left >= right, acs)
          case AST.IR.Exp.Binary.Op.Eq => return (Value.fromB(left == right), acs)
          case AST.IR.Exp.Binary.Op.Ne => return (Value.fromB(left != right), acs)
          case AST.IR.Exp.Binary.Op.FpEq => return (left ~~ right, acs)
          case AST.IR.Exp.Binary.Op.FpNe => return (left !~ right, acs)
          case AST.IR.Exp.Binary.Op.And => return (left & right, acs)
          case AST.IR.Exp.Binary.Op.Or => return (left | right, acs)
          case AST.IR.Exp.Binary.Op.Xor => return (left |^ right, acs)
          case AST.IR.Exp.Binary.Op.Imply => return (left __>: right, acs)
          case AST.IR.Exp.Binary.Op.CondAnd => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.CondOr => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.CondImply => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.Append => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.AppendAll => halt(s"Infeasible: $exp")
          case AST.IR.Exp.Binary.Op.Prepend => halt(s"Infeasible: $exp")
        }
      case exp: AST.IR.Exp.Unary =>
        val (v, acs) = evalExp(state, exp.exp)
        exp.op match {
          case AST.Exp.UnaryOp.Not => return (v.not, acs)
          case AST.Exp.UnaryOp.Complement => return (v.complement, acs)
          case AST.Exp.UnaryOp.Plus => return (v, acs)
          case AST.Exp.UnaryOp.Minus => return (v.minus, acs)
        }
      case exp: AST.IR.Exp.Type =>
        val (v, acs) = evalExp(state, exp.exp)
        val n: U64 =
          if (anvil.isSigned(exp.exp.tipe)) conversions.S64.toRawU64(conversions.Z.toS64(v.value))
          else conversions.Z.toU64(v.value)
        return (Value.fromRawU64(n, anvil.isSigned(exp.tipe), anvil.typeByteSize(exp.tipe)), acs)
      case exp: AST.IR.Exp.Intrinsic =>
        exp.intrinsic match {
          case in: Intrinsic.Load =>
            val (offset, eacs) = evalExp(state, in.rhsOffset)
            val (n, lacs) = load(state.memory, offset.value, in.bytes)
            val acs = eacs + lacs
            return (Value.fromRawU64(conversions.Z.toU64(n.toZ), in.isSigned, in.bytes), acs)
          case in: Intrinsic.Register =>
            if (in.isSP) {
              val acs = State.Accesses.empty.addTemp(state.spIndex, state.SP)
              return (Value.fromRawU64(state.SP, anvil.isSigned(in.tipe), anvil.typeByteSize(in.tipe)), acs)
            } else {
              val acs = State.Accesses.empty.addTemp(state.dpIndex, state.DP)
              return (Value.fromU64(state.DP), acs)
            }
        }
      case exp: AST.IR.Exp.R => halt(s"TODO: ${exp.prettyST.render}")
      case exp: AST.IR.Exp.Construct => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.String => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.Indexing => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.LocalVarRef => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.GlobalVarRef => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.FieldVarRef => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.EnumElementRef => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.If => halt(s"Infeasible: ${exp.prettyST.render}")
      case _: AST.IR.Exp.Apply => halt(s"Infeasible: ${exp.prettyST.render}")
    }
  }

  @pure def evalStmt(state: State, stmt: AST.IR.Stmt.Ground): State.Edit = {
    stmt match {
      case stmt: AST.IR.Stmt.Assign.Temp =>
        val (rhs, acs) = evalExp(state, stmt.rhs)
        val n: U64 =
          if (anvil.isSigned(stmt.rhs.tipe)) conversions.S64.toRawU64(conversions.Z.toS64(rhs.value))
          else conversions.Z.toU64(rhs.value)
        return State.Edit.Temp(State.Edit.Temp.Kind.Register, stmt.lhs, n, acs)
      case stmt: AST.IR.Stmt.Intrinsic =>
        stmt.intrinsic match {
          case in: Intrinsic.TempLoad =>
            val (offset, eacs) = evalExp(state, in.rhsOffset)
            val (m, lacs) = load(state.memory, offset.value, in.bytes)
            val acs = eacs + lacs
            val v = Value.fromRawU64(m, in.isSigned, in.bytes)
            val n: U64 =
              if (in.isSigned) conversions.S64.toRawU64(conversions.Z.toS64(v.value))
              else conversions.Z.toU64(v.value)
            return State.Edit.Temp(State.Edit.Temp.Kind.Register, in.temp, n, acs)
          case in: Intrinsic.Store =>
            val (v, eacs) = evalExp(state, in.rhs)
            val n: U64 = if (anvil.isSigned(in.rhs.tipe)) conversions.S64.toRawU64(conversions.Z.toS64(v.value)) else v.toU64
            val (offset, oacs) = evalExp(state, in.lhsOffset)
            val acs = eacs + oacs
            return store(offset.value, anvil.typeByteSize(in.tipe), n, acs)
          case in: Intrinsic.Copy =>
            val (lhsOffset, lacs) = evalExp(state, in.lhsOffset)
            val (rhsOffset, racs) = evalExp(state, in.rhs)
            val (size, sacs) = evalExp(state, in.rhsBytes)
            val acs = lacs + racs + sacs
            var bs = ISZ[U8]()
            for (i <- 0 until size.value) {
              bs = bs :+ state.memory(rhsOffset.value + i)
            }
            return State.Edit.Memory(lhsOffset.value, bs, acs)
          case in: Intrinsic.RegisterAssign =>
            val (v, acs) = evalExp(state, in.value)
            if (in.isSP) {
              val sp: U64 = conversions.Z.toU64(if (in.isInc) conversions.U64.toZ(state.SP) + v.value else v.value)
              return State.Edit.Temp(State.Edit.Temp.Kind.SP, state.spIndex, sp, acs)
            } else {
              assert(v.value >= 0)
              val dp: U64 = conversions.Z.toU64(if (in.isInc) conversions.U64.toZ(state.DP) + v.value else v.value)
              return State.Edit.Temp(State.Edit.Temp.Kind.DP, state.dpIndex, dp, acs)
            }
          case stmt: Intrinsic.Decl => return State.Edit.Decl(stmt)
        }
      case _: AST.IR.Stmt.Expr => halt(s"Infeasible: ${stmt.prettyST.render}")
      case _: AST.IR.Stmt.Decl => halt(s"Infeasible: ${stmt.prettyST.render}")
      case _: AST.IR.Stmt.Assign => halt(s"Infeasible: ${stmt.prettyST.render}")
    }
  }

  @pure def evalJump(state: State, jump: AST.IR.Jump): State.Edit.Temp = {
    jump match {
      case jump: AST.IR.Jump.Goto =>
        val cp = conversions.Z.toU64(jump.label)
        return State.Edit.Temp(State.Edit.Temp.Kind.CP, state.cpIndex, cp, State.Accesses.empty)
      case jump: AST.IR.Jump.If =>
        val (cond, acs) = evalExp(state, jump.cond)
        val label: Z = if (cond.toB) jump.thenLabel else jump.elseLabel
        val cp = conversions.Z.toU64(label)
        return State.Edit.Temp(State.Edit.Temp.Kind.CP, state.cpIndex, cp, acs)
      case jump: AST.IR.Jump.Switch =>
        val (v, cacs) = evalExp(state, jump.exp)
        var label: Z = 1
        var found = F
        var acs = cacs
        for (c <- jump.cases if !found) {
          val (cv, casacs) = evalExp(state, c.value)
          if (v == cv) {
            acs = acs + casacs
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
        return State.Edit.Temp(State.Edit.Temp.Kind.CP, state.cpIndex, cp, acs)
      case jump: AST.IR.Jump.Intrinsic =>
        jump.intrinsic match {
          case in: Intrinsic.GotoLocal =>
            val offset = state.SP.toZ + in.offset
            val (cp, acs) = load(state.memory, offset, anvil.cpTypeByteSize)
            return State.Edit.Temp(State.Edit.Temp.Kind.CP, state.cpIndex, cp, acs)
        }
      case _: AST.IR.Jump.Return => halt(s"Infeasible: ${jump.prettyST}")
      case _: AST.IR.Jump.Halt => halt(s"Infeasible: ${jump.prettyST}")
    }
  }

  @pure def checkRAW(label: Z, edits: ISZ[State.Edit], index: Z, tsf: ISZ[Z] => ST): Unit = {
    for (i <- edits.indices if i != index) {
      if (edits(index).writes.temps.keySet.intersect(edits(i).reads.temps.keySet).nonEmpty) {
        halt(
          st"""Detected temp RAW hazard in block .$label
              |* Temp Writes = ${tsf(edits(index).writes.temps.keySet.elements)}
              |* Temp Reads = ${tsf(edits(i).reads.temps.keySet.elements)}""".render)
      }
      if (edits(index).writes.memory.keySet.intersect(edits(i).reads.memory.keySet).nonEmpty) {
        halt(
          st"""Detected memory RAW hazard in block .$label
              |* Memory Writes = ${(edits(index).writes.memory.keySet.elements, ", ")}
              |* Memory Reads =  ${(edits(i).reads.memory.keySet.elements, ", ")}""".render)
      }
    }
  }

  @pure def checkWrites(label: Z, edits: ISZ[State.Edit], index: Z, tsf: ISZ[Z] => ST): Unit = {
    for (i <- index + 1 until edits.size) {
      val tempSet = edits(index).writes.temps.keySet.intersect(edits(i).reads.temps.keySet)
      if (tempSet.nonEmpty) {
        halt(st"Detected same multiple temp writes hazard in block .$label (${tsf(tempSet.elements)})".render)
      }
      val memSet = edits(index).writes.memory.keySet.intersect(edits(i).reads.memory.keySet)
      if (memSet.nonEmpty) {
        halt(st"Detected same multiple memory cell writes hazard in block .$label (${(memSet.elements, ", ")})".render)
      }
    }
  }

  @pure def checkAccesses(state: State, label: Z, edits: ISZ[State.Edit]): Unit = {
    ops.ISZOps(for (i <- edits.indices) yield i).parMap((i: Z) => {
      checkRAW(label, edits, i, state.tempsST _)
      checkWrites(label, edits, i, state.tempsST _)
    })
  }

  @pure def evalBlock(state: State, b: AST.IR.BasicBlock): ISZ[State.Edit] = {
    @strictpure def spInc(g: AST.IR.Stmt.Ground): Z = g match {
      case AST.IR.Stmt.Intrinsic(Intrinsic.RegisterAssign(isSP, isInc, n: AST.IR.Exp.Int, _)) if isSP && isInc => n.value
      case _ => 0
    }
    @pure def spIncBlock: Z = {
      var r: Z = 0
      for (g <- b.grounds) {
        val n = spInc(g)
        if (n != 0) {
          r = n
        }
      }
      return r
    }
    var r = ISZ[State.Edit]()
    val n = spIncBlock
    if (n != 0) {
      r = r :+ State.Edit.CallFrame(n > 0)
    }
    for (g <- b.grounds) {
      r = r :+ evalStmt(state, g)
    }
    r = r :+ evalJump(state, b.jump)
    return r
  }

  def executeBlock(state: State, b: AST.IR.BasicBlock): ISZ[State.Undo] = {
    var r = ISZ[State.Undo]()
    val edits = evalBlock(state, b)
    var i: Z = 0
    while (i < edits.size) {
      r = r :+ edits(i).update(state)
      i = i + 1
    }
    checkAccesses(state, b.label, r)
    return r
  }

  def evalProcedure(state: State, p: AST.IR.Procedure): Unit = {
    def log(title: String, b: AST.IR.BasicBlock): Unit = {
      val pos: message.Position = if (b.grounds.nonEmpty) b.grounds(0).pos else b.jump.pos
      var file = pos.uriOpt.get
      val i = ops.StringOps(file).lastIndexOf('/')
      if (i >= 0) {
        file = ops.StringOps(file).substring(i + 1, file.size)
      }
      println(
        st"""$title block .${b.label}:
            |  ${state.prettyST(this)}""".render)
    }

    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val blockMap: HashMap[U64, AST.IR.BasicBlock] = HashMap ++
      (for (b <- body.blocks) yield (conversions.Z.toU64(b.label), b))

    State.Edit.Temp(State.Edit.Temp.Kind.CP, state.cpIndex, conversions.Z.toU64(body.blocks(0).label),
      State.Accesses.empty).update(state)
    if (DEBUG_EDIT) {
      println()
    }

    while (state.CP != u64"0" && state.CP != u64"1") {
      val b = blockMap.get(state.CP).get
      if (DEBUG) {
        log("Evaluating", b)
      }
      executeBlock(state, b)
      if (DEBUG && DEBUG_EDIT) {
        println()
      }
    }

    if (DEBUG) {
      println(
        st"""End state:
            |  ${state.prettyST(this)}""".render)
    }
  }

  @pure def load(memory: MSZ[U8], offset: Z, size: Z): (U64, State.Accesses) = {
    var r = u64"0"
    var i: Z = 0
    var bs = ISZ[U8]()
    while (i < size) {
      val b = memory(offset + i)
      bs = bs :+ b
      val b64 = conversions.U8.toU64(b)
      r = r | (b64 << conversions.Z.toU64(i * 8))
      i = i + 1
    }
    val acs = State.Accesses.empty.addMemory(offset, bs)
    return (r, acs)
  }

  @pure def store(offset: Z, size: Z, value: U64, acs: State.Accesses): State.Edit.Memory = {
    var bs = ISZ[U8]()
    for (i <- 0 until size) {
      val b = conversions.U64.toU8((value >> conversions.Z.toU64(i * 8)) & u64"0xFF")
      bs = bs :+ b
    }
    return State.Edit.Memory(offset, bs, acs)
  }
}