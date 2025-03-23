// #Sireum
import org.sireum._
import org.sireum.S64._

@anvil.hls def shiftS64(m: S64, n: S64): S64 = {
  println(m)
  var i = m >> n
  println(i)
  i = i << n
  return i
}

@anvil.test def test0(): Unit = {
  val r0 = shiftS64(s64"0x4000000000000000", s64"60")
  println(r0)
  assert(r0 == s64"0x4000000000000000")
}