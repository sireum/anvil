// #Sireum
import org.sireum._

@datatype class Foo(val x: Z)

@anvil.hls def indexingObj(a: MSZ[Foo], b: MSZ[Foo], i: Z, j: Z): Unit = {
  a(i) = b(j)
}

@anvil.test def test0(): Unit = {
  val a = MSZ(Foo(4))
  val b = MSZ(Foo(9))
  indexingObj(a, b, 0, 0)
  println(a(0).x)
}
