// #Sireum
import org.sireum._

object Foo {
  var x: Z = 2 * 4
}

@anvil.hls def global(): Z = {
  return Foo.x
}

@anvil.test def test0(): Unit = {
  println(global())
}