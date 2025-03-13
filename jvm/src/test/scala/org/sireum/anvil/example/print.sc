// #Sireum
import org.sireum._

@anvil.hls def printTest(): Unit = {
  println("Hello world!")
  val x = 5
  val c = '≡'
  val f32 = 0.2f
  val f64 = 0.4d
  val s = "abc"
  println("x = ", x, ", c = ", c, ", f32 = ", f32, ", f64 = ", f64, ", s = ", s)
}

@anvil.test def test0(): Unit = {
  printTest()
}
