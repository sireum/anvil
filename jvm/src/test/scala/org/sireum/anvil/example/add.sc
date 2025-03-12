// #Sireum
import org.sireum._
import org.sireum.U16._

@anvil.hls def add(x: U16, y: U16): U16 = {
  return x + y
}

@anvil.test def testAdd1(): Unit = {
  println(add(u16"3", u16"5"))
}

@anvil.test def testAdd2(): Unit = {
  println(add(u16"1403437", u16"5"))
}