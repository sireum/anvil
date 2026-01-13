// #Sireum
import org.sireum._
import org.sireum.U32._

//f1 → f2, no circle, no recursive
@anvil.hls def f1(n: U32): U32 = {
  return f2(n) + u32"10"
}

@anvil.hls def f2(n: U32): U32 = {
  return n + u32"1"
}

@anvil.test def testf1(): Unit = {
  println(f1(u32"3"))
}
