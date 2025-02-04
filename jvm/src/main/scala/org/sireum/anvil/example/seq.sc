// #Sireum
import org.sireum._

@range(min = 0, max = 5, index = T) class I0_5

import I0_5._

def foo(seq: MS[I0_5, U64]): Unit = {
  var i = i0_5"0"
  while (i <= i0_5"5") {
    seq(i) = seq(i) * seq(i)
    i = i + i0_5"1"
  }
}