// #Sireum
import org.sireum._

@datatype trait A
@datatype class B(x: Z) extends A
@datatype class C(y: Z) extends A

def instanceof(a: A): Z = {
  if (a.isInstanceOf[B]) {
    return a.asInstanceOf[B].x
  }
  return 0
}