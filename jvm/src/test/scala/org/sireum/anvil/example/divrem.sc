// #Sireum

import org.sireum._
import org.sireum.S32._
import org.sireum.U64._

@anvil.hls def div(n: S32, m: S32): S32 = {
  return n / m
}

@anvil.hls def rem(n: U64, m: U64): U64 = {
  return n % m
}

@anvil.test def test0(): Unit = {
  println(div(s32"3233", s32"2"))
  println(rem(u64"0xFF", u64"16"))
}
