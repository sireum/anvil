// #Sireum
import org.sireum._
import org.sireum.U32._

// f1 ↔ f2, f1 is recursive, f2 is recursive, there is circle between f1 and f2
@anvil.hls def f1(n: U32): U32 = {
  if(n <= u32"1") {
    return u32"1"
  }
  if(n % u32"2" == u32"0") {
    val r = f2(n - u32"1")
    return r + u32"1"
  } else {
    return f1(n - u32"1")
  }
}

@anvil.hls def f2(n: U32): U32 = {
  if(n <= u32"1") {
    return u32"1"
  }
  if(n % u32"2" == u32"1") {
    val r = f1(n - u32"1")
    return r + u32"1"
  } else {
    return f2(n - u32"1")
  }
}

@anvil.test def testf1(): Unit = {
  println(f1(u32"9"))
}
