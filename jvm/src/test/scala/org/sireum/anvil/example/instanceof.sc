// #Sireum
import org.sireum._

@datatype trait A
@datatype class B(x: Z) extends A
@datatype class C(y: Z) extends A

@anvil.hls def instanceof(a: A): Z = {
  if (a.isInstanceOf[B]) {
    return a.asInstanceOf[B].x
  }
  return 0
}

@anvil.test def test0(): Unit = {
  println(instanceof(B(3)))
}