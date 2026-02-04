// #Sireum
import org.sireum._

@anvil.test def test0() {
  val opt: Option[Z] = Some(4)
  println(opt.get)
}