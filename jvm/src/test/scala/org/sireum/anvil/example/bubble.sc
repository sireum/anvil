// #Sireum
import org.sireum._
import org.sireum.S16._

def swap(a: MSZ[S16], i: Z, j: Z): Unit = {
  val t = a(i)
  a(i) = a(j)
  a(j) = t
}

@anvil.hls def bubble(a: MSZ[S16]): Unit = {
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

def printMSZ16(a: MSZ[S16]): Unit = {
  print('[')
  val size = a.size
  if (size > 0) {
    print(a(0))
    var i: Z = 1
    while (i < size) {
      print(", ")
      print(a(i))
      i = i + 1
    }
  }
  print("]\n")
}

@anvil.test def test0(): Unit = {
  val a = MSZ(s16"-4")
  bubble(a)
  printMSZ16(a)
}

@anvil.test def test1(): Unit = {
  val a = MSZ(s16"1", s16"-2", s16"3")
  bubble(a)
  printMSZ16(a)
}