// #Sireum
import org.sireum._
import org.sireum.S64._
import org.sireum.U64._

@anvil.hls def shiftU64(): Unit = {
  val n = u64"60"
  val m = u64"0x8000000000000000"
  println(m)
  var i = m >>> n
  println(i)
  i = i << n
  println(i)
}

@anvil.hls def shiftS64(): Unit = {
  val n = s64"60"
  val m = s64"0x4000000000000000"
  println(m)
  var i = m >> n
  println(i)
  i = i << n
  println(i)
}

@anvil.test def test0(): Unit = {
  shiftU64()
  shiftS64()
}

test0()