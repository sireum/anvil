// #Sireum
import org.sireum._

def swap(a: MSZ[U8], i: Z, j: Z): Unit = {
  val t = a(i)
  a(i) = a(j)
  a(j) = t
}

def bubble(a: MSZ[U8]): Unit = {
  var i: Z = 0
  while (i < a.size) {
    var j: Z = i + 1
    while (j < a.size) {
      if (a(i) > a(j)) {
        swap(a, i, j)
      }
      j = j + 1
    }
    i = i + 1
  }
}