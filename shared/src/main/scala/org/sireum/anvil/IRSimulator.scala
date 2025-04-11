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
import org.sireum.U16._
import org.sireum.U32._
import org.sireum.U64._
import org.sireum.S8._
import org.sireum.S16._
import org.sireum.S32._
import org.sireum.S64._
import org.sireum.anvil.Util.IndexingCounter
import org.sireum.lang.symbol.Resolver.QName

object IRSimulator {
  var DEBUG: B = T
  var DEBUG_TEMP: B = T
  var DEBUG_EDIT: B = T
  var DEBUG_GLOBAL: B = T
  var DEBUG_LOCAL: B = T

  @record @unclonable class State(val globalMap: HashSMap[QName, Anvil.VarInfo],
                                  var CP: Value,
                                  var SP: Value,
                                  var DP: U64,
                                  val memory: MSZ[U8],
                                  val temps1: MSZ[B],
                                  val tempsU8: MSZ[U8],
                                  val tempsU16: MSZ[U16],
                                  val tempsU32: MSZ[U32],
                                  val tempsU64: MSZ[U64],
                                  val tempsS8: MSZ[S8],
                                  val tempsS16: MSZ[S16],
                                  val tempsS32: MSZ[S32],
                                  val tempsS64: MSZ[S64],
                                  val tempsF32: MSZ[F32],
                                  val tempsF64: MSZ[F64],
                                  var callFrames: Stack[HashSMap[String, Intrinsic.Decl.Local]]) {
    @pure def prettyST(sim: IRSimulator): ST = {
      val globalSTOpt: Option[ST] = if (DEBUG_GLOBAL) {
        var globalSTs = ISZ[ST]()
        for (entry <- globalMap.entries) {
          val (name, info) = entry
          if (info.isScalar) {
            val v = sim.load(memory, info.loc, info.size)._1
            globalSTs = globalSTs :+ st"${(name, ".")}@[${shortenHexString(conversions.Z.toU64(info.loc))} (${info.loc}), ${info.size}] = ${shortenHexString(v)} (${v.toZ})"
          } else {
            globalSTs = globalSTs :+ st"${(name, ".")}@[${shortenHexString(conversions.Z.toU64(info.loc))} (${info.loc}), ${info.size}] = ..."
          }
        }
        Some(
          st""", globals = {
              |  ${(globalSTs, ",\n")}
              |}""")
      } else {
        None()
      }
      val localSTOpt: Option[ST] = if (DEBUG_LOCAL) {
        var localSTs = ISZ[ST]()
        for (entry <- callFrames.peek.get.entries) {
          val (id, info) = entry
          val offset = SP.value + info.loc
          if (sim.anvil.isScalar(info.tipe) || info.size == 0) {
            if (info.size == 0) {
              val t: AST.Typed =
                if (sim.anvil.config.splitTempSizes) if (sim.anvil.isScalar(info.tipe)) info.tipe else sim.anvil.spType
                else AST.Typed.u64
              val value: Value = t match {
                case AST.Typed.f32 => Value.fromF32(tempsF32(info.loc))
                case AST.Typed.f64 => Value.fromF64(tempsF64(info.loc))
                case _ =>
                  val bitSize = sim.anvil.typeBitSize(t)
                  if (sim.anvil.isSigned(t)) {
                    bitSize match {
                      case z"8" => Value.fromS8(tempsS8(info.loc))
                      case z"16" => Value.fromS16(tempsS16(info.loc))
                      case z"32" => Value.fromS32(tempsS32(info.loc))
                      case z"64" => Value.fromS64(tempsS64(info.loc))
                      case _ => halt(s"Infeasible: $bitSize")
                    }
                  } else {
                    if (bitSize == 1) Value.fromB(temps1(info.loc))
                    else if (bitSize <= 8) Value.fromU8(tempsU8(info.loc))
                    else if (bitSize <= 16) Value.fromU16(tempsU16(info.loc))
                    else if (bitSize <= 32) Value.fromU32(tempsU32(info.loc))
                    else Value.fromU64(tempsU64(info.loc))
                  }
              }
              if (sim.anvil.isScalar(info.tipe)) {
                localSTs = localSTs :+ st"$id[${Util.tempST(sim.anvil, info.tipe, info.loc)}] = ${value.debugST}"
              } else {
                localSTs = localSTs :+ st"$id@[${value.debugST}, ${sim.anvil.typeByteSize(info.tipe)}] = ..."
              }
            } else {
              val v = sim.load(memory, offset, info.size)._1
              val vh = shortenHexString(v)
              val value: String = info.tipe match {
                case AST.Typed.f32 => conversions.U32.toRawF32(conversions.U64.toU32(v & u64"0xFFFFFFFFFFFFFFFF")).string
                case AST.Typed.f64 => conversions.U64.toRawF64(v).string
                case _ if sim.anvil.isBitVector(info.tipe) && !sim.anvil.isSigned(info.tipe) => vh
                case _ => v.toZ.string
              }
              localSTs = localSTs :+ st"$id@[${shortenHexString(conversions.Z.toU64(offset))} ($offset), ${info.size}] = $vh ($value)"
            }
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
      var tempsSTs = ISZ[ST]()
      if (DEBUG_TEMP) {
        if (tempsU64.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$64U. = [${(for (t <- tempsU64) yield st"${shortenHexString(t)} (${t.toZ})", ", ")}]"
        }
        if (tempsS64.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$64S. = [${(for (t <- tempsS64) yield st"${shortenHexString(conversions.S64.toRawU64(t))} (${t.toZ})", ", ")}]"
        }
        if (tempsF64.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$64F. = [${(for (t <- tempsF64) yield st"${shortenHexString(conversions.F64.toRawU64(t))} ($t)", ", ")}]"
        }
        if (tempsU32.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$32U. = [${(for (t <- tempsU32) yield st"${shortenHexString(conversions.U32.toU64(t))} (${t.toZ})", ", ")}]"
        }
        if (tempsS32.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$32S. = [${(for (t <- tempsS32) yield st"${shortenHexString(conversions.U32.toU64(conversions.S32.toRawU32(t)))} (${t.toZ})", ", ")}]"
        }
        if (tempsF32.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$32F. = [${(for (t <- tempsF32) yield st"${shortenHexString(conversions.U32.toU64(conversions.F32.toRawU32(t)))} ($t)", ", ")}]"
        }
        if (tempsU16.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$16U. = [${(for (t <- tempsU16) yield st"${shortenHexString(conversions.U16.toU64(t))} (${t.toZ})", ", ")}]"
        }
        if (tempsS16.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$16S. = [${(for (t <- tempsS16) yield st"${shortenHexString(conversions.U16.toU64(conversions.S16.toRawU16(t)))} (${t.toZ})", ", ")}]"
        }
        if (tempsU8.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$8U. = [${(for (t <- tempsU8) yield st"${shortenHexString(conversions.U8.toU64(t))} (${t.toZ})", ", ")}]"
        }
        if (tempsS8.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$8S. = [${(for (t <- tempsS8) yield st"${shortenHexString(conversions.U8.toU64(conversions.S8.toRawU8(t)))} (${t.toZ})", ", ")}]"
        }
        if (temps1.nonEmpty) {
          tempsSTs = tempsSTs :+ st"$$1. = [${(for (t <- temps1) yield if (t) "1" else "0", ", ")}]"
        }
      }
      val r =
        st"""CP = ${shortenHexString(conversions.Z.toU64(CP.value))} (${CP.value}), SP = ${shortenHexString(conversions.Z.toU64(SP.value))} (${SP.value}), DP = ${shortenHexString(DP)} (${DP.toZ}),
            |${(tempsSTs, ",\n")}$globalSTOpt$localSTOpt"""
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
      @strictpure def approxCycles(config: Anvil.Config): Z = 1
      @pure def maxMemoryOffset: Z = {
        var r: Z = 0
        for (offset <- reads.memory.keys ++ writes.memory.keys) {
          if (r < offset) {
            r = offset
          }
        }
        return r
      }
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
            val slotSTs: ISZ[ST] = for (slot <- decl.slots) yield st"${slot.id}@[${shortenHexString(conversions.Z.toU64(state.SP.value + slot.loc))}, ${slot.size}]: ${slot.tipe}"
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

      @datatype class Temp(val kind: Temp.Kind.Type, val isFP: B, val isSigned: B, val bitSize: Z, val temp: Z, val value: Value, val reads: Accesses) extends Edit {
        @strictpure def id: Accesses.TempId = Accesses.TempId(kind, isFP, isSigned, bitSize, temp)
        @strictpure def writes: Accesses = Accesses.empty.addTemp(kind, isFP, isSigned, bitSize, temp, value)
        def update(state: State): Undo = {
          val oldValue: Value = kind match {
            case Temp.Kind.CP =>
              val r = state.CP
              state.CP = value
              r
            case Temp.Kind.SP =>
              val r = state.SP
              state.SP = value
              r
            case Temp.Kind.DP =>
              val r = Value.fromU64(state.DP)
              assert(value.kind == Value.Kind.U64)
              state.DP = value.toU64
              r
            case Temp.Kind.Register =>
              if (isFP) {
                bitSize match {
                  case z"32" =>
                    val r = Value.fromF32(state.tempsF32(temp))
                    assert(value.kind == Value.Kind.F32)
                    state.tempsF32(temp) = value.toF32
                    r
                  case z"64" =>
                    val r = Value.fromF64(state.tempsF64(temp))
                    assert(value.kind == Value.Kind.F64)
                    state.tempsF64(temp) = value.toF64
                    r
                  case _ => halt("Infeasible")
                }
              } else if (isSigned) {
                bitSize match {
                  case z"8" =>
                    val r = Value.fromS8(state.tempsS8(temp))
                    assert(value.kind == Value.Kind.S8)
                    state.tempsS8(temp) = value.toS8
                    r
                  case z"16" =>
                    val r = Value.fromS16(state.tempsS16(temp))
                    assert(value.kind == Value.Kind.S16)
                    state.tempsS16(temp) = value.toS16
                    r
                  case z"32" =>
                    val r = Value.fromS32(state.tempsS32(temp))
                    assert(value.kind == Value.Kind.S32)
                    state.tempsS32(temp) = value.toS32
                    r
                  case z"64" =>
                    val r = Value.fromS64(state.tempsS64(temp))
                    assert(value.kind == Value.Kind.S64)
                    state.tempsS64(temp) = value.toS64
                    r
                  case _ => halt("Infeasible")
                }
              } else {
                bitSize match {
                  case z"1" =>
                    val r = Value.fromB(state.temps1(temp))
                    assert(value.kind == Value.Kind.B)
                    state.temps1(temp) = value.toB
                    r
                  case z"8" =>
                    val r = Value.fromU8(state.tempsU8(temp))
                    assert(value.kind == Value.Kind.U8)
                    state.tempsU8(temp) = value.toU8
                    r
                  case z"16" =>
                    val r = Value.fromU16(state.tempsU16(temp))
                    assert(value.kind == Value.Kind.U16)
                    state.tempsU16(temp) = value.toU16
                    r
                  case z"32" =>
                    val r = Value.fromU32(state.tempsU32(temp))
                    assert(value.kind == Value.Kind.U32)
                    state.tempsU32(temp) = value.toU32
                    r
                  case z"64" =>
                    val r = Value.fromU64(state.tempsU64(temp))
                    assert(value.kind == Value.Kind.U64)
                    state.tempsU64(temp) = value.toU64
                    r
                  case _ => halt(s"Infeasible: $kind, $isSigned, $bitSize, $temp, $value")
                }
              }
          }
          val r = Temp(kind, isFP, isSigned, bitSize, temp, oldValue, Accesses(reads.temps -- ISZ(id), reads.memory).
            addTemp(kind, isFP, isSigned, bitSize, temp, value))
          if (DEBUG_EDIT) {
            val tempST: ST = kind match {
              case Temp.Kind.CP => st"CP"
              case Temp.Kind.SP => st"SP"
              case Temp.Kind.DP => st"DP"
              case Temp.Kind.Register => Util.tempST2(isFP, isSigned, bitSize, temp)
            }
            println(st"* $tempST = ${value.debugST} [old: ${r.value.debugST}]".render)
          }
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

      @datatype class Memory(val offset: Z, val values: ISZ[U8], val reads: Accesses, val cycles: Z) extends Edit {
        @strictpure override def approxCycles(config: Anvil.Config): Z = (cycles / config.copySize) + (cycles % config.copySize)
        @strictpure def writes: Accesses = Accesses.empty.addMemory(offset, values)
        def update(state: State): Undo = {
          val r = Memory(offset, for (i <- values.indices) yield state.memory(offset + i),
            Accesses(reads.temps, reads.memory -- (for (i <- values.indices) yield offset + i)).
              addMemory(offset, values), cycles)
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

    @datatype class Accesses(val temps: HashSMap[Accesses.TempId, Value], val memory: HashSMap[Z, U8]) {

      @pure def addTemp(kind: State.Edit.Temp.Kind.Type, isFP: B, isSigned: B, bitSize: Z, temp: Z, value: Value): Accesses = {
        val id = Accesses.TempId(kind, isFP, isSigned, bitSize, temp)
        return addTempId(id, value)
      }

      @pure def addTempId(id: Accesses.TempId, value: Value): Accesses = {
        assert(temps.get(id).getOrElse(value) == value)
        return Accesses(temps + id ~> value, memory)
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
          r = r.addTempId(entry._1, entry._2)
        }
        for (entry <- other.memory.entries) {
          r = r.addMemory(entry._1, IS(entry._2))
        }
        return r
      }
    }

    object Accesses {
      @datatype class TempId(val kind: State.Edit.Temp.Kind.Type, val isFP: B, val isSigned: B, val bitSize: Z, val n: Z) {
        @strictpure override def hash: Z = string.hash
        @strictpure def isEqual(other: TempId): B = string == other.string
        @strictpure override def string: String = kind match {
          case State.Edit.Temp.Kind.CP => "CP"
          case State.Edit.Temp.Kind.SP => "SP"
          case State.Edit.Temp.Kind.DP => "DP"
          case State.Edit.Temp.Kind.Register => s"$$$bitSize${if (isFP) "F" else if (isSigned) "S" else "U"}.$n"
        }
      }
      @strictpure def empty: Accesses = Accesses(HashSMap.empty, HashSMap.empty)
    }

    @strictpure def create(splitTemps: B,
                           memory: Z,
                           temps: Util.TempVector,
                           globalMap: HashSMap[QName, Anvil.VarInfo]): State =
      State(
        globalMap,
        Value.fromU64(u64"0"),
        Value.fromU64(u64"0"),
        u64"0",
        MSZ.create(memory, u8"0"),
        MSZ.create(if (splitTemps) temps.unsignedCount(1) else 0, F),
        MSZ.create(if (splitTemps) temps.unsignedCount(8) else 0, u8"0"),
        MSZ.create(if (splitTemps) temps.unsignedCount(16) else 0, u16"0"),
        MSZ.create(if (splitTemps) temps.unsignedCount(32) else 0, u32"0"),
        MSZ.create(if (splitTemps) temps.unsignedCount(64) else temps.maxCount, u64"0"),
        MSZ.create(if (splitTemps) temps.signedCount(8) else 0, s8"0"),
        MSZ.create(if (splitTemps) temps.signedCount(16) else 0, s16"0"),
        MSZ.create(if (splitTemps) temps.signedCount(32) else 0, s32"0"),
        MSZ.create(if (splitTemps) temps.signedCount(64) else 0, s64"0"),
        MSZ.create(if (splitTemps) temps.fp32Count else 0, 0f),
        MSZ.create(if (splitTemps) temps.fp64Count else 0, 0d),
        Stack(ISZ(HashSMap.empty)))

  }

  @datatype class Value(val kind: Value.Kind.Type, val value: Z) {
    @strictpure def debugST: ST = kind match {
      case Value.Kind.B => st"$toB"
      case Value.Kind.U8 => st"${shortenHexString(toU64)} ($value)"
      case Value.Kind.U16 => st"${shortenHexString(toU64)} ($value)"
      case Value.Kind.U32 => st"${shortenHexString(toU64)} ($value)"
      case Value.Kind.U64 => st"${shortenHexString(toU64)} ($value)"
      case Value.Kind.S8 => st"${shortenHexString(conversions.S64.toRawU64(toS64))} ($value)"
      case Value.Kind.S16 => st"${shortenHexString(conversions.S64.toRawU64(toS64))} ($value)"
      case Value.Kind.S32 => st"${shortenHexString(conversions.S64.toRawU64(toS64))} ($value)"
      case Value.Kind.S64 => st"${shortenHexString(conversions.S64.toRawU64(toS64))} ($value)"
      case Value.Kind.F32 => st"${shortenHexString(conversions.S64.toRawU64(toS64))} ($value)"
      case Value.Kind.F64 => st"${shortenHexString(conversions.S64.toRawU64(toS64))} ($value)"
    }

    @strictpure override def string: String = kind match {
      case Value.Kind.B => toB.string
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

    @strictpure def bits: Z = kind match {
      case Value.Kind.B => 1
      case Value.Kind.U8 => 8
      case Value.Kind.U16 => 16
      case Value.Kind.U32 => 32
      case Value.Kind.U64 => 64
      case Value.Kind.S8 => 8
      case Value.Kind.S16 => 16
      case Value.Kind.S32 => 32
      case Value.Kind.S64 => 64
      case Value.Kind.F32 => 32
      case Value.Kind.F64 => 64
    }

    @strictpure def signed: B = kind match {
      case Value.Kind.B => F
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
        case Value.Kind.B => halt(s"Infeasible")
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
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => Value.fromB(toB & other.toB)
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => Value.fromB(toB | other.toB)
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => Value.fromB(toB |^ other.toB)
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => Value.fromB(!toB | other.toB)
        case Value.Kind.U8 => halt("Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
      assert(kind == other.kind, s"$kind != ${other.kind}")
      kind match {
        case Value.Kind.B => halt(s"Infeasible")
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
        case Value.Kind.B => Value.fromB(!toB)
        case Value.Kind.U8 => halt(s"Infeasible")
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
        case Value.Kind.B => Value.fromB(~toB)
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
        case Value.Kind.B => halt(s"Infeasible")
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

    @strictpure def toRawU64: U64 = kind match {
      case Value.Kind.B => if (value == 0) u64"0" else u64"1"
      case Value.Kind.U8 => conversions.Z.toU64(value)
      case Value.Kind.U16 => conversions.Z.toU64(value)
      case Value.Kind.U32 => conversions.Z.toU64(value)
      case Value.Kind.U64 => conversions.Z.toU64(value)
      case Value.Kind.S8 => conversions.S64.toRawU64(conversions.Z.toS64(value))
      case Value.Kind.S16 => conversions.S64.toRawU64(conversions.Z.toS64(value))
      case Value.Kind.S32 => conversions.S64.toRawU64(conversions.Z.toS64(value))
      case Value.Kind.S64 => conversions.S64.toRawU64(conversions.Z.toS64(value))
      case Value.Kind.F32 => conversions.Z.toU64(value)
      case Value.Kind.F64 => conversions.Z.toU64(value)
    }
  }

  object Value {
    @enum object Kind {
      "B"
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

    @strictpure def fromB(n: B): Value = Value(Kind.B, if (n) 1 else 0)

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

    @strictpure def fromZ(n: Z, bits: Z, isSigned: B): Value =
      if (isSigned) {
        if (bits == 8) {
          Value(Value.Kind.S8, n)
        } else if (bits == 16) {
          Value(Value.Kind.S16, n)
        } else if (bits <= 32) {
          Value(Value.Kind.S32, n)
        } else if (bits <= 64) {
          Value(Value.Kind.S64, n)
        } else {
          halt(s"Infeasible: $n, $isSigned, $bits")
        }
      } else {
        if (bits == 1) {
          Value(Value.Kind.B, n)
        } else if (bits == 8) {
          Value(Value.Kind.U8, n)
        } else if (bits == 16) {
          Value(Value.Kind.U16, n)
        } else if (bits <= 32) {
          Value(Value.Kind.U32, n)
        } else if (bits <= 64) {
          Value(Value.Kind.U64, n)
        } else {
          halt(s"Infeasible: $n, $isSigned, $bits")
        }
      }

    @strictpure def fromRawU64(anvil: Anvil, n: U64, t: AST.Typed): Value = t match {
      case AST.Typed.f32 => fromF32(conversions.U32.toRawF32(conversions.U64.toU32(n & u64"0xFFFFFFFF")))
      case AST.Typed.f64 => fromF64(conversions.U64.toRawF64(n))
      case _ =>
        val isSigned = anvil.isSigned(t)
        val bits = anvil.typeBitSize(t)
        if (isSigned) {
          if (bits == 8) {
            fromS8(conversions.U8.toRawS8(conversions.U64.toU8(n & u64"0xFF")))
          } else if (bits == 16) {
            fromS16(conversions.U16.toRawS16(conversions.U64.toU16(n & u64"0xFFFF")))
          } else if (bits == 32) {
            fromS32(conversions.U32.toRawS32(conversions.U64.toU32(n & u64"0xFFFFFFFF")))
          } else if (bits == 64) {
            fromS64(conversions.U64.toRawS64(n))
          } else {
            halt(s"Infeasible: $bits")
          }
        } else {
          bits match {
            case z"1" => fromB(conversions.U64.toB(n & u64"0x1"))
            case z"8" => fromU8(conversions.U64.toU8(n & u64"0xFF"))
            case z"16" => fromU16(conversions.U64.toU16(n & u64"0xFFFF"))
            case z"24" => fromU32(conversions.U64.toU32(n & u64"0xFFFFFF"))
            case z"32" => fromU32(conversions.U64.toU32(n & u64"0xFFFFFFFF"))
            case z"40" => fromU64(n & u64"0xFFFFFFFFFF")
            case z"48" => fromU64(n & u64"0xFFFFFFFFFFFF")
            case z"56" => fromU64(n & u64"0xFFFFFFFFFFFFFF")
            case z"64" => fromU64(n)
            case _ => halt(s"Infeasible: $bits")
          }
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
        return (Value.fromZ(exp.value, anvil.typeBitSize(exp.tipe), anvil.isSigned(exp.tipe)), State.Accesses.empty)
      case exp: AST.IR.Exp.F32 => return (Value.fromF32(exp.value), State.Accesses.empty)
      case exp: AST.IR.Exp.F64 => return (Value.fromF64(exp.value), State.Accesses.empty)
      case exp: AST.IR.Exp.Temp =>
        val t: AST.Typed = if (anvil.isScalar(exp.tipe)) exp.tipe else anvil.spType
        val isSigned = anvil.isSigned(t)
        val bitSize = anvil.typeBitSize(t)
        val isFP = anvil.isFP(t)
        if (anvil.config.splitTempSizes) {
          val v: Value = t match {
            case AST.Typed.f32 => Value.fromF32(state.tempsF32(exp.n))
            case AST.Typed.f64 => Value.fromF64(state.tempsF64(exp.n))
            case _ =>
              if (isSigned) {
                bitSize match {
                  case z"8" => Value.fromS8(state.tempsS8(exp.n))
                  case z"16" => Value.fromS16(state.tempsS16(exp.n))
                  case z"32" => Value.fromS32(state.tempsS32(exp.n))
                  case z"64" => Value.fromS64(state.tempsS64(exp.n))
                  case _ => halt(s"Infeasible: $bitSize, ${exp.tipe}")
                }
              } else {
                bitSize match {
                  case z"1" => Value.fromB(state.temps1(exp.n))
                  case z"8" => Value.fromU8(state.tempsU8(exp.n))
                  case z"16" => Value.fromU16(state.tempsU16(exp.n))
                  case z"32" => Value.fromU32(state.tempsU32(exp.n))
                  case z"64" => Value.fromU64(state.tempsU64(exp.n))
                  case _ => halt(s"Infeasible: $bitSize, ${exp.tipe}")
                }
              }
          }
          val acs = State.Accesses.empty.addTemp(State.Edit.Temp.Kind.Register, isFP, isSigned, bitSize, exp.n, v)
          return (v, acs)
        } else {
          val v = Value.fromRawU64(anvil, state.tempsU64(exp.n), t)
          val acs = State.Accesses.empty.addTemp(State.Edit.Temp.Kind.Register, F, F, 64, exp.n, v)
          return (v, acs)
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
        return (Value.fromRawU64(anvil, n, exp.tipe), acs)
      case exp: AST.IR.Exp.Intrinsic =>
        exp.intrinsic match {
          case in: Intrinsic.Load =>
            val (offset, eacs) = evalExp(state, in.rhsOffset)
            val (n, lacs) = load(state.memory, offset.value, in.bytes)
            val acs = eacs + lacs
            return (Value.fromRawU64(anvil, conversions.Z.toU64(n.toZ), in.tipe), acs)
          case in: Intrinsic.Register =>
            if (in.isSP) {
              val acs = State.Accesses.empty.addTemp(State.Edit.Temp.Kind.SP, anvil.isFP(anvil.spType),
                anvil.isSigned(anvil.spType), anvil.spTypeByteSize * 8, 0, state.SP)
              return (state.SP, acs)
            } else {
              val v = Value.fromU64(state.DP)
              val acs = State.Accesses.empty.addTemp(State.Edit.Temp.Kind.DP, anvil.isFP(anvil.dpType),
                anvil.isSigned(anvil.dpType), anvil.dpTypeByteSize * 8, 0, v)
              return (v, acs)
            }
          case in: Intrinsic.Indexing =>
            val (base, bacs) = evalExp(state, in.baseOffset)
            val (index, iacs): (Value, State.Accesses) = in.maskOpt match {
              case Some(mask) => evalExp(state, AST.IR.Exp.Binary(in.index.tipe, in.index, AST.IR.Exp.Binary.Op.And,
                AST.IR.Exp.Int(in.index.tipe, mask, in.pos), in.pos))
              case _ => evalExp(state, in.index)
            }
            val t: AST.Typed = if (anvil.isScalar(in.tipe)) in.tipe else anvil.spType
            val v = Value.fromZ(base.value + in.dataOffset + index.value * in.elementSize, anvil.typeBitSize(t),
              anvil.isSigned(t))
            return (v, bacs + iacs)
        }
      case exp: AST.IR.Exp.R => halt(s"TODO: ${exp.prettyST(anvil.printer).render}")
      case exp: AST.IR.Exp.Construct => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.String => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.Indexing => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.LocalVarRef => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.GlobalVarRef => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.FieldVarRef => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.EnumElementRef => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.If => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
      case _: AST.IR.Exp.Apply => halt(s"Infeasible: ${exp.prettyST(anvil.printer).render}")
    }
  }

  @pure def evalStmt(state: State, stmt: AST.IR.Stmt.Ground): State.Edit = {
    stmt match {
      case stmt: AST.IR.Stmt.Assign.Temp =>
        val (rhs, acs) = evalExp(state, stmt.rhs)
        if (anvil.config.splitTempSizes) {
          val t: AST.Typed = if (anvil.isScalar(stmt.rhs.tipe)) stmt.rhs.tipe else anvil.spType
          return State.Edit.Temp(State.Edit.Temp.Kind.Register, anvil.isFP(t), anvil.isSigned(t),
            anvil.typeBitSize(t), stmt.lhs, rhs, acs)
        } else {
          val t = AST.Typed.u64
          return State.Edit.Temp(State.Edit.Temp.Kind.Register, anvil.isFP(t), anvil.isSigned(t),
            anvil.typeBitSize(t), stmt.lhs, Value.fromU64(rhs.toRawU64), acs)
        }
      case stmt: AST.IR.Stmt.Intrinsic =>
        stmt.intrinsic match {
          case in: Intrinsic.TempLoad =>
            val (offset, eacs) = evalExp(state, in.rhsOffset)
            val (m, lacs) = load(state.memory, offset.value, in.bytes)
            val acs = eacs + lacs
            if (anvil.config.splitTempSizes) {
              val t: AST.Typed = if (anvil.isScalar(in.tipe)) in.tipe else anvil.spType
              val v = Value.fromRawU64(anvil, m, t)
              return State.Edit.Temp(State.Edit.Temp.Kind.Register, anvil.isFP(t), anvil.isSigned(t),
                anvil.typeBitSize(t), in.temp, v, acs)
            } else {
              val t = AST.Typed.u64
              val v = Value.fromU64(m)
              return State.Edit.Temp(State.Edit.Temp.Kind.Register, anvil.isFP(t), anvil.isSigned(t),
                anvil.typeBitSize(t), in.temp, v, acs)
            }
          case in: Intrinsic.Store =>
            val (v, eacs) = evalExp(state, in.rhs)
            val n: U64 =
              if (anvil.isSigned(in.rhs.tipe)) conversions.S64.toRawU64(conversions.Z.toS64(v.value)) else v.toU64
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
            return State.Edit.Memory(lhsOffset.value, bs, acs,
              if (in.rhsBytes.isInstanceOf[AST.IR.Exp.Int]) 1 else size.value)
          case in: Intrinsic.RegisterAssign =>
            val (v, acs) = evalExp(state, in.value)
            if (in.isSP) {
              val sp: Value = if (in.isInc) Value.fromZ(state.SP.value + v.value, anvil.typeBitSize(anvil.spType),
                anvil.isSigned(anvil.spType)) else v
              return State.Edit.Temp(State.Edit.Temp.Kind.SP, anvil.isFP(anvil.spType), anvil.isSigned(anvil.spType),
                anvil.typeBitSize(anvil.spType), 0, sp, acs)
            } else {
              assert(v.value >= 0)
              val dp: Value = if (in.isInc) Value.fromU64(state.DP) + v else v
              return State.Edit.Temp(State.Edit.Temp.Kind.DP, anvil.isFP(anvil.spType), anvil.isSigned(anvil.dpType),
                anvil.typeBitSize(anvil.dpType), 0, dp, acs)
            }
          case stmt: Intrinsic.Decl => return State.Edit.Decl(stmt)
        }
      case _: AST.IR.Stmt.Expr => halt(s"Infeasible: ${stmt.prettyST(anvil.printer).render}")
      case _: AST.IR.Stmt.Decl => halt(s"Infeasible: ${stmt.prettyST(anvil.printer).render}")
      case _: AST.IR.Stmt.Assign => halt(s"Infeasible: ${stmt.prettyST(anvil.printer).render}")
    }
  }

  @pure def evalJump(state: State, jump: AST.IR.Jump): State.Edit.Temp = {
    val isSigned = anvil.isSigned(anvil.cpType)
    val bitSize = anvil.typeBitSize(anvil.cpType)
    val isFP = anvil.isFP(anvil.cpType)
    jump match {
      case jump: AST.IR.Jump.Goto =>
        val cp = Value.fromZ(jump.label, bitSize, isSigned)
        return State.Edit.Temp(State.Edit.Temp.Kind.CP, isFP, isSigned, bitSize, 0, cp, State.Accesses.empty)
      case jump: AST.IR.Jump.If =>
        val (cond, acs) = evalExp(state, jump.cond)
        val label: Z = if (cond.toB) jump.thenLabel else jump.elseLabel
        val cp = Value.fromZ(label, bitSize, isSigned)
        return State.Edit.Temp(State.Edit.Temp.Kind.CP, isFP, isSigned, bitSize, 0, cp, acs)
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
        val cp = Value.fromZ(label, bitSize, isSigned)
        return State.Edit.Temp(State.Edit.Temp.Kind.CP, isFP, isSigned, bitSize, 0, cp, acs)
      case jump: AST.IR.Jump.Intrinsic =>
        jump.intrinsic match {
          case in: Intrinsic.GotoLocal =>
            if (anvil.config.tempLocal) {
              val (cp, acs) = evalExp(state, AST.IR.Exp.Temp(in.loc, anvil.cpType, in.pos))
              return State.Edit.Temp(State.Edit.Temp.Kind.CP, isFP, isSigned, bitSize, 0, cp, acs)
            } else {
              val offset = state.SP.value + in.loc
              val (cp, acs) = load(state.memory, offset, anvil.cpTypeByteSize)
              return State.Edit.Temp(State.Edit.Temp.Kind.CP, isFP, isSigned, bitSize, 0,
                Value.fromRawU64(anvil, cp, anvil.cpType), acs)
            }
        }
      case _: AST.IR.Jump.Return => halt(s"Infeasible: ${jump.prettyST(anvil.printer)}")
      case _: AST.IR.Jump.Halt => halt(s"Infeasible: ${jump.prettyST(anvil.printer)}")
    }
  }

  @pure def checkRAW(label: Z, edits: ISZ[State.Edit], index: Z): Unit = {
    for (i <- edits.indices if i != index) {
      if (edits(index).writes.temps.keySet.intersect(edits(i).reads.temps.keySet).nonEmpty) {
        halt(
          st"""Detected temp RAW hazard in block .$label
              |* Temp Writes = ${(edits(index).writes.temps.keySet.elements, ", ")}
              |* Temp Reads = ${(edits(i).reads.temps.keySet.elements, ", ")}""".render)
      }
      if (edits(index).writes.memory.keySet.intersect(edits(i).reads.memory.keySet).nonEmpty) {
        halt(
          st"""Detected memory RAW hazard in block .$label
              |* Memory Writes = ${(edits(index).writes.memory.keySet.elements, ", ")}
              |* Memory Reads =  ${(edits(i).reads.memory.keySet.elements, ", ")}""".render)
      }
    }
  }

  @pure def checkWrites(label: Z, edits: ISZ[State.Edit], index: Z): Unit = {
    for (i <- index + 1 until edits.size) {
      val tempSet = edits(index).writes.temps.keySet.intersect(edits(i).reads.temps.keySet)
      if (tempSet.nonEmpty) {
        halt(st"Detected same multiple temp writes hazard in block .$label (${(tempSet.elements, ", ")})".render)
      }
      val memSet = edits(index).writes.memory.keySet.intersect(edits(i).reads.memory.keySet)
      if (memSet.nonEmpty) {
        halt(st"Detected same multiple memory cell writes hazard in block .$label (${(memSet.elements, ", ")})".render)
      }
    }
  }

  @pure def checkAccesses(state: State, label: Z, edits: ISZ[State.Edit]): Unit = {
    ops.ISZOps(for (i <- edits.indices) yield i).parMap((i: Z) => {
      checkRAW(label, edits, i)
      checkWrites(label, edits, i)
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

  def executeBlock(state: State, b: AST.IR.BasicBlock, blockCycles: MBox[Z], maxMemory: MBox[Z]): ISZ[State.Undo] = {
    var r = ISZ[State.Undo]()
    val edits = evalBlock(state, b)
    var i: Z = 0
    var cycles: Z = 1
    while (i < edits.size) {
      val ec = edits(i).approxCycles(anvil.config)
      if (ec > cycles) {
        cycles = ec
      }
      val offset = edits(i).maxMemoryOffset
      if (offset > maxMemory.value) {
        maxMemory.value = offset
      }
      r = r :+ edits(i).update(state)
      i = i + 1
    }
    @strictpure def isDivRem(op: AST.IR.Exp.Binary.Op.Type): B =
      op == AST.IR.Exp.Binary.Op.Div || op == AST.IR.Exp.Binary.Op.Rem
    @pure def hasIndexing: B = {
      val ic = IndexingCounter(0)
      ic.transform_langastIRBasicBlock(b)
      return ic.count > 0
    }

    if (anvil.config.customDivRem) {
      b.grounds match {
        case ISZ(AST.IR.Stmt.Assign.Temp(_, rhs: AST.IR.Exp.Binary, _)) if isDivRem(rhs.op) =>
          if (anvil.typeByteSize(rhs.tipe) <= 32) {
            cycles = 33
          } else {
            cycles = 65
          }
          cycles = cycles + 2
        case _ =>
      }
    } else if (anvil.config.indexing && hasIndexing) {
      if (cycles < 4) {
        cycles = 4
      } else {
        cycles = cycles + 4
      }
    }
    checkAccesses(state, b.label, r)
    blockCycles.value = cycles
    return r
  }

  def evalProcedure(state: State, p: AST.IR.Procedure): Unit = {
    var approxCycles: Z = 0

    def log(title: String, b: AST.IR.BasicBlock): Unit = {
      val pos: message.Position = if (b.grounds.nonEmpty) b.grounds(0).pos else b.jump.pos
      var file = pos.uriOpt.get
      val i = ops.StringOps(file).lastIndexOf('/')
      if (i >= 0) {
        file = ops.StringOps(file).substring(i + 1, file.size)
      }
      println(
        st"""$title block .${b.label} (approx. cycles = $approxCycles):
            |  ${state.prettyST(this)}""".render)
    }

    val body = p.body.asInstanceOf[AST.IR.Body.Basic]
    val blockMap: HashMap[Z, AST.IR.BasicBlock] = HashMap ++
      (for (b <- body.blocks) yield (b.label, b))

    State.Edit.Temp(State.Edit.Temp.Kind.CP, anvil.isFP(anvil.cpType), anvil.isSigned(anvil.cpType),
      anvil.typeBitSize(anvil.cpType), 0, Value.fromZ(body.blocks(0).label, anvil.typeBitSize(anvil.cpType),
        anvil.isSigned(anvil.cpType)), State.Accesses.empty).update(state)
    if (DEBUG_EDIT) {
      println()
    }

    val blockCyclesBox = MBox[Z](0)
    val maxMemoryBox = MBox[Z](0)
    while (state.CP.value != 0 && state.CP.value != 1) {
      val b = blockMap.get(state.CP.value).get
      if (DEBUG) {
        log("Evaluating", b)
      }
      executeBlock(state, b, blockCyclesBox, maxMemoryBox)
      approxCycles = approxCycles + blockCyclesBox.value
      if (DEBUG && DEBUG_EDIT) {
        println()
      }
    }

    if (DEBUG) {
      println(
        st"""End state (approx. cycles = $approxCycles, max memory offset touched: ${maxMemoryBox.value}):
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
    return State.Edit.Memory(offset, bs, acs, 1)
  }
}