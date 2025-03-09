// #Sireum
import org.sireum._

@anvil.hls def printTest(): Unit = {
  println("Hello world!")
  val x = 5
  val c = '≡'
  val f32 = 0.1f
  val f64 = 0.3d
  val s = "abc"
  println("x = ", x, ", c = ", c, ", f32 = ", f32, ", f64 = ", f64, ", s = ", s)
}