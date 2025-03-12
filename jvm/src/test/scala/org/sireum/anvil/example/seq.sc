// #Sireum
import org.sireum._

@range(min = 0, max = 5, index = T) class I0_5

import I0_5._
import org.sireum.U64._

@anvil.hls def square(seq: MS[I0_5, U64]): Unit = {
  var i = i0_5"0"
  while (i < i0_5"5") {
    seq(i) = seq(i) * seq(i)
    i = i + i0_5"1"
  }
  seq(i0_5"5") = seq(i0_5"5") * seq(i0_5"5")
}

@anvil.test def test0(): Unit = {
  val a = MS[I0_5, U64](u64"0", u64"1", u64"2", u64"3", u64"4", u64"5")
  square(a)
  println(a(i0_5"0") + a(i0_5"1") + a(i0_5"2") + a(i0_5"3") + a(i0_5"4") + a(i0_5"5")) // 0x37
}