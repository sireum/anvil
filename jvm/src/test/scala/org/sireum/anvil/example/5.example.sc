// #Sireum
import org.sireum._
import org.sireum.U32._

// f1 → f2, f1 is recursive, f2 is recursive, no circle
@anvil.hls def f1(n: U32): U32 = {
  if(n > u32"2") {
    return f1(n - u32"1")
  } else {
    return f2(n)
  }
}

@anvil.hls def f2(n: U32): U32 = {
  if(n > u32"1") {
    return f2(n - u32"1")
  }
  return u32"7"
}

@anvil.test def testf1(): Unit = {
  println(f1(u32"8"))
}
