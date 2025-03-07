// #Sireum

import org.sireum._

def bar(x: Z, y: Z): Unit = {
  assert(x == y, "x is not equal to y")
}

def foo(): Unit = {
  bar(3, 5)
}