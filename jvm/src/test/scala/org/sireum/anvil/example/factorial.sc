// #Sireum
import org.sireum._
import org.sireum.U32._

@anvil.hls def factorial(n: U32): U32 = {
  if (n <= u32"1") {
    return u32"1"
  }
  return n * factorial(n - u32"1")
}

@anvil.test def test0(): Unit = {
  println(factorial(u32"1"))
}

@anvil.test def test1(): Unit = {
  println(factorial(u32"3"))
}

@anvil.test def test2(): Unit = {
  println(factorial(u32"10"))
}