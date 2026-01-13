// #Sireum
import org.sireum._
import org.sireum.U32._

//f1 ↔ f2, there is on circle between f1 and f2, no recursive
@anvil.hls def f1(n: U32): U32 = {
  if(n <= u32"0") {
    return u32"1"
  }
  val r = f2(n - u32"1")
  return r + u32"1"
}

@anvil.hls def f2(n: U32): U32 = {
  if(n <= u32"0") {
    return u32"2"
  }
  val r = f1(n - u32"1")
  return r + u32"2"
}

@anvil.test def testf1(): Unit = {
  println(f1(u32"5"))
}
