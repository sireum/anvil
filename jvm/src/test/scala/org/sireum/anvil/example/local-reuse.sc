// #Sireum
import org.sireum._

@anvil.hls def localReuse(): Unit = {
  {
    val x = 3
    println(x)
  }
  {
    val y = 1
    println(y)
  }
}

@anvil.test def test0(): Unit = {
  localReuse()
}