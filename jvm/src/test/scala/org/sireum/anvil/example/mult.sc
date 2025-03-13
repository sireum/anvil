// #Sireum
import org.sireum._
import org.sireum.U64._

@anvil.hls def mult(x: U64, y: U64): U64 = {
  var r: U64 = u64"0"
  var i: U64 = u64"0"
  while (i < x) {
    r = r + y
    i = i + u64"1"
  }
  return r
}

@anvil.test def test0(): Unit = {
  println(mult(u64"2", u64"2"))
}

@anvil.test def test1(): Unit = {
  println(mult(u64"3", u64"5"))
}

@anvil.test def test2(): Unit = {
  println(mult(u64"12349", u64"0"))
}