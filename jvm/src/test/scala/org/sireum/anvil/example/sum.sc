// #Sireum
import org.sireum._

@anvil.hls def sum(a: ISZ[Z], i: Z, acc: Z): Z = {
  if (i < a.size) {
    return sum(a, i + 1, acc + a(i))
  } else {
    return acc
  }
}