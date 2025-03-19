// #Sireum
import org.sireum._

@anvil.hls def printTest(): Unit = {
  println("Hello world!")
  val x = 5
  val c = '≡'
  val s = "abc"
  println("x = ", x, ", c = ", c, ", s = ", s)
}

@anvil.test def test0(): Unit = {
  printTest()
}
