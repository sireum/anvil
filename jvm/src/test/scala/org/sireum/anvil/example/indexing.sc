// #Sireum
import org.sireum._
import org.sireum.U8._
import org.sireum.U16._

@anvil.hls def indexing(a: ISZ[U16], b: ISZ[U8], i: Z, j: Z): U16 = {
  return a(i) + conversions.U8.toU16(b(j))
}

@anvil.test def test0(): Unit = {
  println(indexing(ISZ(u16"3", u16"2"), ISZ(u8"1", u8"4"), 1, 1))
}
