// #Sireum

import org.sireum._

@anvil.hls def bar(x: Z, y: Z): Unit = {
  assert(x == y, "x is not equal to y")
}

@anvil.test def foo(): Unit = {
  bar(3, 5)
}