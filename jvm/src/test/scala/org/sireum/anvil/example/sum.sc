// #Sireum
import org.sireum._

@anvil.hls def sum(a: ISZ[Z], i: Z, acc: Z): Z = {
  if (i < a.size) {
    return sum(a, i + 1, acc + a(i))
  } else {
    return acc
  }
}

@anvil.test def test0(): Unit = {
  println(sum(ISZ(), 0, 0))
}

@anvil.test def test1(): Unit = {
  println(sum(ISZ(1, 2), 0, 0))
}

@anvil.test def test2(): Unit = {
  println(sum(ISZ(1, 2, 3), 1, 0))
}