// #Sireum
import org.sireum._

@anvil.hls def zfill(n: Z): Z = {
  val a = MSZ.create(n, z"0")
  a(2) = 7
  var acc = z"0"
  var i = 0
  while (i < n) {
    acc = acc + a(i)
    i = i + 1
  }
  return acc
}

@anvil.test def test0(): Unit = {
  println(zfill(4)) // expect 7 (zero-filled array plus a(2)=7)
}
