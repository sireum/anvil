// #Sireum
import org.sireum._
import org.sireum.U64._

@anvil.hls def printlnU64(n: U64): Unit = {
  println(n)
}

@anvil.test def test0(): Unit = {
  printlnU64(u64"12357")
}

@anvil.test def test1(): Unit = {
  printlnU64(u64"16")
}

@anvil.test def test2(): Unit = {
  printlnU64(u64"3")
}