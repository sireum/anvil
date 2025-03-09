// #Sireum
import org.sireum._
import org.sireum.U32._

@anvil.hls def factorial(n: U32): U32 = {
  if (n == u32"0") {
    return u32"1"
  }
  return n * factorial(n - u32"1")
}