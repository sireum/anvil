// #Sireum
import org.sireum._
import org.sireum.S64._
import org.sireum.U64._

@anvil.hls def shiftU64(m: U64, n: U64): U64 = {
  println(m)
  var i = m >>> n
  println(i)
  i = i << n
  return i
}

@anvil.hls def shiftS64(m: S64, n: S64): S64 = {
  println(m)
  var i = m >> n
  println(i)
  i = i << n
  return i
}

@anvil.test def test0(): Unit = {
  val r0 = shiftU64(u64"0x8000000000000000", u64"60")
  println(r0)
  assert(r0 == u64"0x8000000000000000")
  val r1 = shiftS64(s64"0x4000000000000000", s64"60")
  println(r1)
  assert(r1 == s64"0x4000000000000000")
}