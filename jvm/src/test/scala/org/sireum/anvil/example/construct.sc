// #Sireum
import org.sireum._

@anvil.hls def mkIS(x: Z, y: Z, z: Z): ISZ[Z] = {
  return ISZ(x, y, z)
}

@anvil.test def test0(): Unit = {
  val a = mkIS(1, 2, 3)
  println('[', a(0), ", ", a(1), ", ", a(2), ']')
}
