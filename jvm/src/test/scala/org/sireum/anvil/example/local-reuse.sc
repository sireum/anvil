// #Sireum
import org.sireum._

@anvil.hls def localReuse(): Unit = {
  val x = 3
  val y = 4
  println(x)
  val z = 1
  println(z)
  println(y)
}

@anvil.test def test0(): Unit = {
  localReuse()
}