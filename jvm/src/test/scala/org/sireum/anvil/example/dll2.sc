// #Sireum
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

// List trait with some basic list functionality implemented.
@datatype trait List[T] {

  @strictpure def length: Z = this match {
    case List.Cons(_, next) => 1 + next.length
    case _ => 0
  }

  @strictpure def length_acc(acc: Z): Z = this match {
    case List.Cons(_, next) => next.length_acc(1 + acc)
    case _ => acc
  }

  @abs def hd: T = this match {
    case List.Cons(value, _) => value
    case _ => halt("hd")
  }

  @abs def tl: List[T] = this match {
    case List.Cons(_, next) => next
    case _ => List.empty
  }

  @abs def nth(n: Z): T = this match {
    case List.Cons(_, next) if n > 0 => next.nth(n - 1)
    case List.Cons(value, next) if n == 0 => value
    case _ => halt("nth")
  }

  @abs def ++(l2: List[T]): List[T] = this match {
    case List.Cons(value, next) => List.Cons(value, next ++ l2)
    case _ => l2
  }

  @abs def drop(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(_, next) => next.drop(n - 1)
      case _ => List.empty
    }
  } else {
    this
  }

  @abs def take(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(value, next) => List.Cons(value, next.take(n - 1))
      case _ => List.empty
    }
  } else {
    List.empty
  }

  // Implementation of "reverse" using ++ to avoid introducing
  // an accumulator argument.
  @strictpure def rev: List[T] = this match {
    case List.Cons(value, next) => next.rev ++ List.make(value)
    case _ => this
  }
}

object List {

  @datatype class Nil[T] extends List[T]

  @datatype class Cons[T](val value: T, val next: List[T]) extends List[T]

  @pure def distinctNilCons[T](list: List[T], value: T, next: List[T]): Unit = {
    Contract(
      Requires(list == Nil[T]()),
      Ensures(list != Cons[T](value, next))
    )
  }

  @pure def hd_notempty[T](value: T, next: List[T]): Unit = {
    Contract(
      Ensures(Cons[T](value, next).hd === value)
    )
  }

  @pure def nth_base[T](value: T, next: List[T]): Unit = {
    Contract(
      Ensures(Cons[T](value, next).nth(0) === value)
    )
  }

  @pure def nth_step[T](value: T, next: List[T], n: Z): Unit = {
    Contract(
      Requires(n > 0),
      Ensures(Cons[T](value, next).nth(n) === next.nth(n - 1))
    )
  }

  @pure def length_Nil[T](): Unit = {
    Contract(
      Ensures(Nil[T]().length == 0)
    )
  }

  @pure def length_cons[T](value: T, next: List[T]): Unit = {
    Contract(
      Ensures(Cons(value, next).length == 1 + next.length)
    )
  }

  @pure def length_acc_Nil[T](acc: Z): Unit = {
    Contract(
      Ensures(Nil[T]().length_acc(acc) == acc)
    )
  }

  @pure def length_acc_cons[T](value: T, next: List[T], acc: Z): Unit = {
    Contract(
      Ensures(Cons(value, next).length_acc(acc) == next.length_acc(1 + acc))
    )
  }

  @pure def length_bound[T](list: List[T]): Unit = {
    Contract(
      Ensures(list.length >= 0)
    )
    (list: @induct) match {
      case Nil() =>
      case Cons(value, next) =>
    }
  }

  @pure def length_decr_tl[T](list: List[T]): Unit = {
    Contract(
      Requires(list.length > 0),
      Ensures(list.tl.length == list.length - 1)
    )
  }

  @pure def distinctConsNil[T](list: List[T], value: T, next: List[T]): Unit = {
    Contract(
      Requires(list == Cons[T](value, next)),
      Ensures(list != Nil[T]())
    )
  }

  @pure def drop_1_tl[T](list: List[T]): Unit = {
    Contract(
      Ensures(list.tl === list.drop(1))
    )
  }

  @pure def drop_alltl[T](l: List[T]): Unit = {
    Contract(
      Ensures(All{ n: Z => n >= 0 ___>: l.tl.drop(n) == l.drop(n + 1) })
    )
    (l: @induct) match {
      case Nil() =>
      case Cons(value, next) =>
        Deduce(
          1 (All{ n: Z => n >= 0 ___>: next.tl.drop(n) == next.drop(n + 1) }) by Premise,
          2 Let((k: Z) => SubProof(
            3 (l ≡ Cons(value, next)) by Premise,
            4 (k > 0 ___>: next.tl.drop(k - 1) == next.drop(k)) by Auto and 1,
            5 (k > 0 ___>: l.tl.drop(k) == next.tl.drop(k - 1)) by Auto,
            6 (k >= 0 ___>: l.drop(k + 1) == l.tl.drop(k)) by Auto,
            7 (k >= 0 ___>: l.tl.drop(k) == l.drop(k + 1)) by Auto
          )),
          8 (All{ n: Z => n >= 0 ___>: l.tl.drop(n) == l.drop(n + 1) }) by AllI[Z](2)
        )
    }
  }

  @pure def drop_additive_all[T](list: List[T], n: Z): Unit = {
    Contract(
      Requires(n >= 0),
      Ensures(All { m: Z => m >= 0 ___>: list.drop(m).drop(n) === list.drop(m + n) })
    )
    (list: @induct) match {
      case Nil() => Deduce(|- (All { m: Z => m >= 0 ___>: list.drop(m).drop(n) === list.drop(m + n) }))
      case Cons(value, next) =>
        Deduce(
          1 (All { m: Z => m >= 0 ___>: next.drop(m).drop(n) === next.drop(m + n) }) by Premise,
          2 Let((k: Z) => SubProof(
            3 (list ≡ Cons(value, next)) by Premise,
            4 (k > 0 ___>: next.drop(k - 1).drop(n) === next.drop(k - 1 + n)) by Auto and 1,
            5 (k > 0 ___>: list.drop(k).drop(n) === list.drop(k - 1 + 1 + n)) by Auto,
            6 (k > 0 ___>: list.drop(k).drop(n) === list.drop(k + n)) by Auto,
            7 (list.drop(0) === list) by Auto,
            8 (list.drop(0).drop(n) === list.drop(n)) by Simpl and 7,
            9 (k >= 0 ___>: list.drop(k).drop(n) === list.drop(k + n)) by Auto
          )),
          10 (All { m: Z => m >= 0 ___>: list.drop(m).drop(n) === list.drop(m + n) }) by AllI[Z](2)
        )
    }
  }

  @pure def drop_additive[T](list: List[T], m: Z, n: Z): Unit = {
    Contract(
      Requires(m >= 0, n >= 0),
      Ensures(list.drop(m).drop(n) === list.drop(m + n))
    )
    drop_additive_all(list, n)
  }

  @pure def drop_tl_swap[T](list: List[T], n: Z): Unit = {
    Contract(
      Requires(n >= 0),
      Ensures(list.tl.drop(n) === list.drop(n).tl)
    )
    (list: @induct) match {
      case Nil() => Deduce(|- (list.tl.drop(n) == list.drop(n).tl))
      case Cons(value, next) =>
        drop_1_tl(list)
        Deduce(
          1 (list.tl === list.drop(1)) by drop_1_tl(list),
          2 (list.tl.drop(n) === list.drop(1).drop(n)) by Simpl,
          3 (list.drop(n).tl === list.drop(n).drop(1)) by drop_1_tl(list.drop(n)),
          4 (1 >= 0) by Algebra,
          5 (n >= 0) by Premise,
          6 (list.drop(1).drop(n) === list.drop(1 + n)) by drop_additive(list, 1, n),
          7 (list.drop(n).drop(1) === list.drop(n + 1)) by drop_additive(list, n, 1),
          8 (list.drop(1 + n) === list.drop(n + 1)) by Auto,
          9 (list.tl.drop(n) === list.drop(n).tl) by Auto
        )
    }
  }

  @pure def drop_tl[T](list: List[T], n: Z): Unit = {
    Contract(
      Requires(n >= 0),
      Ensures(list.tl.drop(n) == list.drop(n + 1))
    )
    drop_alltl(list)
  }

  @pure def drop_tl_other[T](l: List[T], m: List[T], n: Z): Unit = {
    Contract(
      Requires(l === m.drop(n), n >= 0),
      Ensures(l.tl === m.drop(n + 1))
    )
    Deduce(
      1 (l.tl === m.drop(n).tl) by Auto,
      2 (n >= 0) by Premise,
      3 (m.tl.drop(n) === m.drop(n).tl) by drop_tl_swap(m, n)
    )
  }

  @pure def drop_hd_nth_all[T](l: List[T]): Unit = {
    Contract(
      Ensures(All { n: Z => n >= 0 & n < l.length ___>: l.drop(n).hd == l.nth(n) })
    )
    (l: @induct) match {
      case Nil() =>
        //Deduce(|- )
        Deduce(|- (All { n: Z => n >= 0 & n < l.length ___>: l.drop(n).hd == l.nth(n) }))
      case Cons(value, next) =>
        Deduce(|- (All { n: Z => n >= 0 & n < l.length ___>: l.drop(n).hd == l.nth(n) }))
    }
  }

  @pure def drop_hd_nth[T](l: List[T], n: Z): Unit = {
    Contract(
      Requires(n >= 0, n < l.length),
      Ensures(l.drop(n).hd == l.nth(n))
    )
    drop_hd_nth_all(l)
  }

//  @pure def drop_tl_hd_nth[T](l: List[T], n: Z): Unit = {
//    Contract(
//      Requires(n >= 0, n < l.length, l.drop(n).hd == l.nth(n)),
//      Ensures(l.tl.drop(n).hd == l.nth(n + 1))
//    )
//    drop_hd_nth_all(l)
//  }

  @strictpure def make[T](value: T): List[T] = Cons(value, Nil())

  @strictpure def empty[T]: List[T] = Nil()

  @pure def length_impl_with_acc[T](l: List[T]): Unit = {
    Contract(
      Ensures(All{ (acc: Z) => acc + l.length == l.length_acc(acc)})
    )
    (l: @induct) match {
      case Cons(value, next) =>
        length_cons(value, next)
        Deduce(
          1 (All{ (acc: Z) => acc + next.length == next.length_acc(acc) })
            by Premise,
          2 (Cons(value, next).length == 1 + next.length)
            by Premise,
          3 Let((acc: Z) => SubProof(
            4 (Cons(value, next).length_acc(acc) == next.length_acc(1 + acc))
              by Simpl,
            5 (1 + acc + next.length == next.length_acc(1 + acc))
              by Auto and (1, 4),
            6 (1 + acc + next.length == acc + Cons(value, next).length)
              by Auto and (2, 5),
            7 (acc + Cons(value, next).length == Cons(value, next).length_acc(acc))
              by Simpl
          ))
        )
        return
      case Nil() =>
        return
    }
  }

  @pure def length_impl_with_acc_sum[T](l: List[T]): Unit = {
    Contract(
      Ensures(All{ (acc: Z) => All{ (bcc: Z) => bcc + l.length_acc(acc) == l.length_acc(bcc + acc)}})
    )
    (l: @induct) match {
      case Cons(value, next) =>
        Deduce(
          1 (All{ (acc: Z) => All{ (bcc: Z) => bcc + next.length_acc(acc) == next.length_acc(bcc + acc) }}) by Premise,
          2 (Cons(value, next).length == 1 + next.length) by Simpl,
          3 Let((acc: Z) => SubProof(
            4 Let((bcc: Z) => SubProof(
              5 (Cons(value, next).length_acc(bcc + acc) == next.length_acc(1 + (bcc + acc))) by Simpl,
              6 (All{ (bcc: Z) => bcc + next.length_acc(1 + acc) == next.length_acc(bcc + (1 + acc))}) by AllE[Z](1),
              7 (bcc + next.length_acc(1 + acc) == next.length_acc(bcc + (1 + acc))) by AllE[Z](6),
              8 (bcc + Cons(value, next).length_acc(acc) == bcc + next.length_acc(1 + acc)) by Simpl,
              9 (bcc + Cons(value, next).length_acc(acc) == Cons(value, next).length_acc(bcc + acc)) by Auto,
              10 (bcc + l.length_acc(acc) == l.length_acc(bcc + acc)) by Auto
            )),
            11 (All{ (bcc: Z) => bcc + l.length_acc(acc) == l.length_acc(bcc + acc)}) by AllI[Z](4)
          )),
          12 (All{ (acc: Z) => All{ (bcc: Z) => bcc + l.length_acc(acc) == l.length_acc(bcc + acc)}}) by AllI[Z](3)
        )
        return
      case Nil() =>
        return
    }
  }

  @pure def length_tl[T](l: List[T]): Unit = {
    Contract(
      Requires(l != Nil[T]()),
      Ensures(All { (acc: Z) => l.length_acc(acc) == l.tl.length_acc(1 + acc) })
    )
  }

  @pure def cons_tl[T](l: List[T], value: T, next: List[T]): Unit = {
    Contract(
      Requires(l == Cons(value, next)),
      Ensures(l.tl == next)
    )
  }
}

import List._

@datatype class Node[E](elem: E,
                        used: B,
                        left: DLLPool.PoolPtr,
                        right: DLLPool.PoolPtr);

object DLLPool {
  type PoolPtr = Z
  type PoolMem[E] = MSZ[Node[E]]
  val Null: PoolPtr = -1

  @abs def isPointer[E](pool: PoolMem[E], p: PoolPtr): B = {
    p == Null || pool.isInBound(p)
  }

  @abs def isValidPointer[E](pool: PoolMem[E], p: PoolPtr): B = {
    pool.isInBound(p)
  }

  @pure def isLeaf(p: PoolPtr): B = {
    Contract(
      Ensures(Res == (p == Null))
    )
    return p == Null
  }

  @pure def nonLeafIsValidPointer[E](pool: PoolMem[E], p: PoolPtr): Unit = {
    Contract(
      Requires(isPointer(pool, p), !isLeaf(p)),
      Ensures(isValidPointer(pool, p))
    )
  }

  @strictpure def reach[E](pool: PoolMem[E], p: PoolPtr, q: PoolPtr): B =
    if (isValidPointer(pool, p)) {
      if (pool(p).right == q) {
        true
      } else {
        reach(pool, pool(p).right, q)
      }
    } else {
      false
    }

  @abs def acyclic[E](pool: PoolMem[E], p: PoolPtr): B = {
    All(pool.indices)(q => reach(pool, p, q) ___>: p != q)
  }

  @strictpure def reach_valid[E](pool: PoolMem[E], p: PoolPtr, q: PoolPtr): B =
    reach(pool, p, q) ___>: isValidPointer(pool, q)

  @strictpure def reach_used[E](pool: PoolMem[E], p: PoolPtr, q: PoolPtr): B =
    reach(pool, p, q) & reach_valid(pool, p, q) ___>: pool(q).used == true

  @strictpure def count_free_rec[E](pool: PoolMem[E], p: PoolPtr): Z =
    if (isValidPointer(pool, p)) {
      if (pool(p).used) {
        count_free_rec(pool, p + 1)
      } else {
        1 + count_free_rec(pool, p + 1)
      }
    } else {
      0
    }

  @abs def count_free[E](pool: PoolMem[E]): Z =
    count_free_rec(pool, 0)


  @strictpure def count_free_until[E](pool: PoolMem[E], p: PoolPtr, q: PoolPtr): Z =
    if (isValidPointer(pool, p) & p < q) {
      if (pool(p).used) {
        count_free_until(pool, p + 1, q)
      } else {
        1 + count_free_until(pool, p + 1, q)
      }
    } else {
      0
    }

  @pure def count_free_until_size[E](pool: PoolMem[E], p: PoolPtr): Unit = {
    Contract(
      Ensures(count_free_rec(pool, p) == count_free_until(pool, p, pool.size))
    )
    if (p > pool.size) {
      return
    }
    var q: PoolPtr = pool.size
    while (p < q) {
      Invariant(
        Modifies(q),
        p <= q, q <= pool.size,
        count_free_rec(pool, q) == count_free_until(pool, q, pool.size)
      )
      q = q - 1
    }
  }

  @pure def count_free_until_same[E](pool: PoolMem[E], p: PoolPtr): Unit = {
    Contract(
      Ensures(count_free_until(pool, p, p) == 0)
    )
  }

  @pure def count_free_until_step[E](pool: PoolMem[E], p: PoolPtr): Unit = {
    Contract(
      Requires(isValidPointer(pool, p), !pool(p).used),
      Ensures(count_free_until(pool, p, p + 1) == 1)
    )
  }

  @pure def count_free_until_limit[E](pool: PoolMem[E], r: PoolPtr, p: PoolPtr, q: PoolPtr): Unit = {
    Contract(
      Requires(r <= p, r <= q, pool.size <= p, pool.size <= q),
      Ensures(count_free_until(pool, r, p) == count_free_until(pool, r, q))
    )
    if (p == q) {
      return
    } else if (p < q) {
      var k = p;
      var v = count_free_until(pool, k, p);
      var w = count_free_until(pool, k, q);
      while (r < k) {
        Invariant(
          Modifies(k, v, w),
          r <= k,
          v == count_free_until(pool, k, p),
          w == count_free_until(pool, k, q),
          v == w
        )
        k = k - 1
        v = count_free_until(pool, k, p);
        w = count_free_until(pool, k, q);
      }
    } else {
      var k = q;
      var v = count_free_until(pool, k, p);
      var w = count_free_until(pool, k, q);
      while (r < k) {
        Invariant(
          Modifies(k, v, w),
          r <= k,
          v == count_free_until(pool, k, p),
          w == count_free_until(pool, k, q),
          v == w
        )
        k = k - 1
        v = count_free_until(pool, k, p);
        w = count_free_until(pool, k, q);
      }
    }
  }

  @pure def count_free_until_inc1[E](pool: PoolMem[E], p: PoolPtr, q: PoolPtr): Unit = {
    Contract(
      Requires(p <= q, isValidPointer(pool, p), 0 <= q),
      Ensures(count_free_until(pool, p, q + 1) == count_free_until(pool, p, q) + count_free_until(pool, q, q + 1))
    )
    var k = q
    while (p < k) {
      Invariant(
        Modifies(k),
        p <= k,
        count_free_until(pool, k, q + 1) == count_free_until(pool, k, q) + count_free_until(pool, q, q + 1)
      )
      k = k - 1
    }
  }

  @pure def count_free_until_split[E](pool: PoolMem[E], p: PoolPtr, q: PoolPtr, n: PoolPtr): Unit = {
    Contract(
      Requires(0 <= p, p <= q, q <= n, n >= 0),
      Ensures(count_free_until(pool, p, n) == count_free_until(pool, p, q) + count_free_until(pool, q, n))
    )
    var m = q
    while (m < n) {
      Invariant(
        Modifies(m),
        q <= m, m <= n,
        count_free_until(pool, p, m) == count_free_until(pool, p, q) + count_free_until(pool, q, m)
      )
      if (isValidPointer(pool, p)) {
        if (isValidPointer(pool, q)) {
          count_free_until_inc1(pool, p, m)
          count_free_until_inc1(pool, q, m)
        } else {
          count_free_until_limit(pool, p, m + 1, q)
        }
      }
      m = m + 1
    }
  }

  @pure def count_free_bounds[E](pool: PoolMem[E]): Unit = {
    Contract(
      Ensures(count_free(pool) >= 0, count_free(pool) <= pool.size)
    )
    var p: PoolPtr = pool.size
    var s: Z = count_free_rec(pool, p)
    while (p > 0) {
      Invariant(
        Modifies(p, s),
        0 <= s, s <= pool.size - p,
        0 <= p, p <= pool.size,
        s == count_free_rec(pool, p)
      )
      p = p - 1
      if (isValidPointer(pool, p)) {
        if (pool(p).used) {
          s = s
        } else {
          s = 1 + s
        }
      } else {
        s = 0
      }
    }
  }

  @pure def count_free_indices[E](pool: PoolMem[E], p: PoolPtr): Unit = {
    Contract(
      Requires(pool.isInBound(p), count_free_rec(pool, p) == pool.size - p),
      Ensures(All(p until pool.size)(k => !pool(k).used))
    )
    var q: PoolPtr = pool.size
    var s: Z = count_free_rec(pool, q)
    while (q > p) {
      Invariant(
        Modifies(q, s),
        0 <= s, s <= pool.size - q,
        p <= q, q <= pool.size,
        s == count_free_rec(pool, q),
        s == pool.size - q ___>: All(q until pool.size)(k => !pool(k).used)
      )
      q = q - 1
      if (isValidPointer(pool, q)) {
        if (pool(q).used) {
          s = s
        } else {
          s = 1 + s
        }
      } else {
        s = 0
      }
    }
  }

  @pure def count_free_space[E](pool: PoolMem[E]): Unit = {
    Contract(
      Requires(count_free(pool) > 0),
      Ensures(Exists(pool.indices)(k => !pool(k).used))
    )
    var k: PoolPtr = 0
    val f: Z = count_free(pool)
    while (true) {
      Invariant(
        Modifies(k),
        k < pool.size,
        count_free_rec(pool, k) == f
      )
      if (isValidPointer(pool, k)) {
        if (pool(k).used) {
        } else {
          return
        }
      } else {
      }
      k = k + 1
    }
  }

  @pure def count_free_on_alloc[E](pool: PoolMem[E], qool: PoolMem[E], p: PoolPtr): Unit = {
    Contract(
      Requires(
        pool.isInBound(p),
        pool.size == qool.size,
        All(pool.indices)(q => q != p ___>: pool(q) == qool(q)),
        !pool(p).used,
        qool(p).used
      ),
      Ensures(count_free(pool) == count_free(qool) + 1)
    )
    var k = p
    while (0 < k) {
      Invariant(
        Modifies(k),
        0 <= k, k <= p,
        count_free_until(pool, k, p) == count_free_until(qool, k, p)
      )
      k = k - 1
    }
    var l: PoolPtr = pool.size
    while (p + 1 < l) {
      Invariant(
        Modifies(l),
        p + 1 <= l, l <= pool.size,
        count_free_until(pool, l, pool.size) == count_free_until(qool, l, pool.size)
      )
      l = l - 1
    }
    Deduce( // Stock keeping:
      1 (count_free_until(pool, 0, p) == count_free_until(qool, 0, p)) by Auto,
      2 (count_free_until(pool, p + 1, pool.size) == count_free_until(qool, p + 1, pool.size)) by Auto,
      3 (count_free_until(pool, p, p + 1) == 1) by Auto,
      4 (count_free_until(qool, p, p + 1) == 0) by Auto
    )
    count_free_until_split(pool, 0, p, p + 1)
    count_free_until_split(pool, 0, p + 1, pool.size)
    Deduce(|- ( // We have:
      count_free_until(pool, 0, pool.size) ==
      count_free_until(pool, 0, p) +
        count_free_until(pool, p, p + 1) +
        count_free_until(pool, p + 1, pool.size)))
    count_free_until_split(qool, 0, p, p + 1)
    count_free_until_split(qool, 0, p + 1, pool.size)
    Deduce(|- ( // We have:
      count_free_until(qool, 0, pool.size) ==
        count_free_until(qool, 0, p) +
          count_free_until(qool, p, p + 1) +
          count_free_until(qool, p + 1, pool.size)))
    count_free_until_size(pool, 0)
    count_free_until_size(qool, 0)
  }

  @pure def count_free_on_dealloc[E](pool: PoolMem[E], qool: PoolMem[E], p: PoolPtr): Unit = {
    Contract(
      Requires(
        pool.isInBound(p),
        pool.size == qool.size,
        All(pool.indices)(q => q != p ___>: pool(q) == qool(q)),
        pool(p).used,
        !qool(p).used
      ),
      Ensures(count_free(qool) == count_free(pool) + 1)
    )
    var k = p
    while (0 < k) {
      Invariant(
        Modifies(k),
        0 <= k, k <= p,
        count_free_until(pool, k, p) == count_free_until(qool, k, p)
      )
      k = k - 1
    }
    var l: PoolPtr = pool.size
    while (p + 1 < l) {
      Invariant(
        Modifies(l),
        p + 1 <= l, l <= pool.size,
        count_free_until(pool, l, pool.size) == count_free_until(qool, l, pool.size)
      )
      l = l - 1
    }
    Deduce( // Stock keeping:
      1 (count_free_until(pool, 0, p) == count_free_until(qool, 0, p)) by Auto,
      2 (count_free_until(pool, p + 1, pool.size) == count_free_until(qool, p + 1, pool.size)) by Auto,
      3 (count_free_until(pool, p, p + 1) == 0) by Auto,
      4 (count_free_until(qool, p, p + 1) == 1) by Auto
    )
    count_free_until_split(pool, 0, p, p + 1)
    count_free_until_split(pool, 0, p + 1, pool.size)
    Deduce(|- ( // We have:
      count_free_until(pool, 0, pool.size) ==
        count_free_until(pool, 0, p) +
          count_free_until(pool, p, p + 1) +
          count_free_until(pool, p + 1, pool.size)))
    count_free_until_split(qool, 0, p, p + 1)
    count_free_until_split(qool, 0, p + 1, pool.size)
    Deduce(|- ( // We have:
      count_free_until(qool, 0, pool.size) ==
        count_free_until(qool, 0, p) +
          count_free_until(qool, p, p + 1) +
          count_free_until(qool, p + 1, pool.size)))
    count_free_until_size(pool, 0)
    count_free_until_size(qool, 0)
  }

  @abs def asList[E](pool: PoolMem[E], head: PoolPtr): List[E] =
    if (isValidPointer(pool, head)) {
      Cons(pool(head).elem, asList(pool, pool(head).right))
    } else {
      Nil()
    }

  // Can only be proved with Simpl
  @pure def asList_Cons[E](pool: PoolMem[E], head: PoolPtr): Unit = {
    Contract(
      Requires(isValidPointer(pool, head)),
      Ensures(asList(pool, head) === Cons(pool(head).elem, asList(pool, pool(head).right)))
    )
    Deduce(
      1 (isValidPointer(pool, head)) by Auto,
      2 (asList(pool, head) === Cons[E](pool(head).elem, asList(pool, pool(head).right))) by RSimpl(RS(asList _))
    )
  }

  @pure def asList_Head[E](pool: PoolMem[E], head: PoolPtr, list: List[E]): Unit = {
    Contract(
      Requires(asList(pool, head) === list, isValidPointer(pool, head)),
      Ensures(list.hd === pool(head).elem)
    )
    hd_notempty(pool(head).elem, asList(pool, pool(head).right))
    Deduce(
      1 (asList(pool, head) === Cons(pool(head).elem, asList(pool, pool(head).right))) by Auto,
      2 (asList(pool, head) === list) by Premise,
      3 (list === Cons(pool(head).elem, asList(pool, pool(head).right))) by Subst_<(2, 1),
      4 (list.hd === Cons(pool(head).elem, asList(pool, pool(head).right)).hd) by Simpl
    )
  }

  @pure def asList_Nil[E](pool: PoolMem[E], head: PoolPtr): Unit = {
    Contract(
      Requires(!isValidPointer(pool, head)),
      Ensures(asList(pool, head) == Nil[E]())
    )
  }

//  @pure def asList_head[E](pool: PoolMem[E], p: PoolPtr, list: List[E]): Unit = {
//    Contract(
//      Requires(list != empty[E], isValidPointer(pool, p), asList(pool, p) == list),
//      Ensures(pool(p).elem == list.hd)
//    )
//    hd_notempty(pool(p).elem, asList(pool, pool(p).right))
//    Deduce(
//      1 (isValidPointer(pool, p)) by Premise,
//      2 (asList(pool, p) == Cons(pool(p).elem, asList(pool, pool(p).right))) by asList_Cons(pool, p),
//      3 (Cons(pool(p).elem, asList(pool, pool(p).right)).hd == pool(p).elem) by Premise
//    )
//  }

  // Programmatic proof by contradiction
  @pure def asList_Nil_inverse[E](pool: PoolMem[E], head: PoolPtr): Unit = {
    Contract(
      Requires(asList(pool, head) == Nil[E]()),
      Ensures(!isValidPointer(pool, head))
    )
    val list = asList(pool, head)
    if (isValidPointer(pool, head)) {
      distinctConsNil(list, pool(head).elem, asList(pool, pool(head).right))
      Deduce(
        1 (list == Cons(pool(head).elem, asList(pool, pool(head).right))) by Auto,
        2 (list != Nil[E]()) by Auto
      )
    }
  }

  @abs def refinesProp[E](pool: PoolMem[E], head: PoolPtr, list: List[E]): B = {
    asList(pool, head) === list
  }

  @pure def refines_list_head[E](pool: PoolMem[E], head: PoolPtr, list: List[E]): Unit = {
    Contract(
      Requires(refinesProp(pool, head, list), isValidPointer(pool, head)),
      Ensures(list.hd === pool(head).elem)
    )
    asList_Head(pool, head, list)
  }

  @pure def refines_nth_head[E](pool: PoolMem[E], head: PoolPtr, list: List[E]): Unit = {
    Contract(
      Requires(isValidPointer(pool, head), refinesProp(pool, head, list), list.length > 0),
      Ensures(list.nth(0) == pool(head).elem)
    )
    Spec { nth_base(pool(head).elem, asList(pool, pool(head).right)) }
    Deduce(
      1 (isValidPointer(pool, head)) by Premise,
      2 (refinesProp(pool, head, list)) by Premise,
      3 (list.length > 0) by Premise,
      4 (asList(pool, head) === list) by Rewrite(RS(refinesProp _), 2),
      5 (Cons(pool(head).elem, asList(pool, pool(head).right)) === list) by Rewrite(RS(asList _), 4)
    )
  }


  @pure def refines_nth_tail[E](pool: PoolMem[E], head: PoolPtr, list: List[E], n: Z): Unit = {
    Contract(
      Requires(isValidPointer(pool, head), refinesProp(pool, head, list), list.length > 0, n > 0),
      Ensures(list.nth(n) === asList(pool, pool(head).right).nth(n - 1))
    )
    Spec { nth_step(pool(head).elem, asList(pool, pool(head).right), n) }
    Deduce(
      1 (isValidPointer(pool, head)) by Premise,
      2 (refinesProp(pool, head, list)) by Premise,
      3 (list.length > 0) by Premise,
      4 (asList(pool, head) === list) by Rewrite(RS(refinesProp _), 2),
      5 (Cons(pool(head).elem, asList(pool, pool(head).right)) === list) by Rewrite(RS(asList _), 4)
    )
  }

  @pure def refines_p_not_Nil[E](pool: PoolMem[E], p: PoolPtr, l: List[E]): Unit = {
    Contract(
      Requires(isValidPointer(pool, p), refinesProp(pool, p, l)),
      Ensures(l != Nil[E]())
    )
    Deduce(
      1 (isValidPointer(pool, p)) by Premise,
      2 (pool.isInBound(p)) by Rewrite(RS(isValidPointer _), 1),
      3 (refinesProp(pool, p, l)) by Premise,
      4 (asList(pool, p) == l) by Auto and 3,
      5 (asList(pool, p) == Cons[E](pool(p).elem, asList(pool, pool(p).right))) by RSimpl(RS(asList _)) and (1, 2),
      6 (Cons[E](pool(p).elem, asList(pool, pool(p).right)) == l) by Subst_<(5, 4)
    )
  }

  @pure def refines_valid_pointer[E](pool: PoolMem[E], p: PoolPtr, l: List[E]): Unit = {
    Contract(
      Requires(isValidPointer(pool, p), refinesProp(pool, p, l)),
      Ensures()
    )
  }

  @pure def refines_p_sublist[E](pool: PoolMem[E], p: PoolPtr, l: List[E]): Unit = {
    Contract(
      Requires(isValidPointer(pool, p), refinesProp(pool, p, l)),
      Ensures(refinesProp(pool, pool(p).right, l.tl))
    )
    cons_tl(l, pool(p).elem, asList(pool, pool(p).right))
    l match {
      case Cons(value, next) =>
      //        Deduce(
      //          1 (isValidPointer(pool, p)) by Auto,
      //          2 (pool.isInBound(p)) by Auto and 1,
      //          3 (refinesProp(pool, p, l)) by Auto,
      //          4 (asList(pool, p) == l) by Auto and 3,
      //          5 (l == Cons(value, next)) by Auto,
      //          6 (pool(p).elem == value) by Auto,
      //          7 (next == asList(pool, pool(p).right)) by Auto,
      //          8 (l.tl == next) by Auto
      //        )
      case _ =>
    }
  }

  @pure
  @tailrec
  def listCoincidence[E](pool: PoolMem[E], qool: PoolMem[E], h: PoolPtr): Unit = {
    Contract(
      Requires(
        pool.size == qool.size,
        All(pool.indices)(p => pool(p).elem == qool(p).elem),
        All(pool.indices)(p => pool(p).used == qool(p).used),
        All(pool.indices)(p => pool(p).right == qool(p).right)
      ),
      Ensures(asList(pool, h) === asList(qool, h))
    )
    val l = asList(pool, h)
    l match {
      case Nil() =>
        asList_Nil_inverse(pool, h)
      case Cons(value, next) =>
        val r = pool(h).right
        val t = l.tl
        refines_p_sublist(pool, h, l)
        listCoincidence(pool, qool, r)
    }
  }

  @pure def freeCoincidence[E](pool: PoolMem[E], qool: PoolMem[E]): Unit = {
    Contract(
      Requires(
        pool.size == qool.size,
        All(pool.indices)(p => pool(p).used == qool(p).used)
      ),
      Ensures(count_free(pool) == count_free(qool))
    )
    var q: PoolPtr = pool.size
    while (q > 0) {
      Invariant(
        Modifies(q),
        0 <= q, q <= pool.size,
        count_free_rec(pool, q) == count_free_rec(qool, q)
      )
      q = q - 1
    }
  }

  @pure def refinesNewHead[E](pool: PoolMem[E], h: PoolPtr, l: List[E], n: PoolPtr, e: E): Unit = {
    Contract(
      Requires(
        refinesProp(pool, h, l),
        isValidPointer(pool, n),
        pool(n) == Node(e, T, Null, h)),
      Ensures(refinesProp(pool, n, Cons(e, l)))
    )
    Deduce(
      1 (asList(pool, h) == l) by Auto,
      2 (isValidPointer(pool, n)) by Premise,
      3 (pool(n) == Node(e, T, Null, h)) by Auto,
      4 (Cons(pool(n).elem, asList(pool, pool(n).right)) == asList(pool, n)) by RSimpl(RS(asList _)),
      5 (Cons(e, asList(pool, h)) == asList(pool, n)) by Auto,
      6 (Cons(e, l) == asList(pool, n)) by Subst_<(1, 5)
    )
  }

  @abs def freeNodesProp[E](pool: PoolMem[E], free: Z): B =
    free == count_free(pool)

  @abs def reachAcyclicProp[E](pool: PoolMem[E], head: PoolPtr): B = {
    All(pool.indices)(i => reach(pool, head, i) ___>: All(pool.indices)(j => reach(pool, i, j) ___>: (i != j)))
  }

  @abs def poolRightProp[E](pool: PoolMem[E]): B = {
    All(pool.indices)(i => isPointer(pool, pool(i).right))
  }

  @abs def poolRightValidProp[E](pool: PoolMem[E], tail: PoolPtr): B = {
    All(pool.indices)(i => (i != tail & pool(i).used) ___>: isValidPointer(pool, pool(i).right))
  }

  @abs def headUsedProp[E](pool: PoolMem[E], head: PoolPtr): B = {
    isValidPointer(pool, head) ___>: pool(head).used
  }

  @abs def headNullEmptyProp[E](pool: PoolMem[E], head: PoolPtr): B = {
    head == Null ___>: All(pool.indices)(p => !pool(p).used)
  }

  @abs def poolRightUsedProp[E](pool: PoolMem[E]): B = {
    All(pool.indices)(i => pool(i).used & isValidPointer(pool, pool(i).right) ___>: pool(pool(i).right).used)
  }

  @pure def unusedInv[E](pl: PoolMem[E], h: PoolPtr, l: List[E], ql: PoolMem[E], n: PoolPtr): Unit = {
    Contract(
      Requires(
        refinesProp(pl, h, l),
        headUsedProp(pl, h),
        poolRightUsedProp(pl),
        pl.size == ql.size,
        isValidPointer(pl, n),
        All(pl.indices)(p => p != n ___>: pl(p) == ql(p)),
        pl(n).used == F),
      Ensures(
        refinesProp(ql, h, l)
      )
    )
    //Deduce(1 (asList(pl, h) === l) by RSimpl(RS(asList _)))
    l match {
      case Nil() =>
        asList_Nil_inverse(pl, h)
        Deduce(
          1 (asList(pl, h) === Nil[E]()) by Auto,
          4 (!isValidPointer(pl, h)) by Auto,
          8 (refinesProp(ql, h, l)) by Auto
        )
      case Cons(value, next) =>
        Deduce(
          1 (isValidPointer(pl, h)) by Auto,
          2 (pl(h).used) by Auto,
          3 (h != n) by Auto,
          4 (ql(h).used) by Auto,
          5 (ql(h).elem == pl(h).elem) by Auto,
          6 (asList(pl, h) === Cons(pl(h).elem, asList(pl, pl(h).right))) by RSimpl(RS(asList _))
        )
        val r = pl(h).right
        val t = l.tl
        refines_p_sublist(pl, h, l)
        unusedInv(pl, r, t, ql, n)
        Deduce(
          1 (refinesProp(ql, r, t)) by Auto,
          3 (ql(h).right == r) by Auto,
          4 (asList(ql, ql(h).right) == t) by Auto,
          5 (asList(pl, pl(h).right) == t) by Auto,
          6 (isValidPointer(ql, h)) by Auto,
          7 (asList(ql, h) === Cons(ql(h).elem, asList(ql, ql(h).right))) by RSimpl(RS(asList _)),
          8 (asList(pl, h) === Cons(pl(h).elem, asList(pl, pl(h).right))) by Auto,
          9 (pl(h).right === ql(h).right) by Auto,
          10 (asList(pl, ql(h).right) === asList(ql, ql(h).right)) by Auto,
          11 (asList(pl, pl(h).right) === asList(ql, ql(h).right)) by Auto,
          944 (asList(ql, h) === Cons(pl(h).elem, asList(pl, pl(h).right))) by Auto,
          55 (asList(ql, h) === asList(pl, h)) by Auto,
          33 (Cons(ql(h).elem, asList(ql, ql(h).right)) === l) by Auto
        )
    }
  }
}

import DLLPool._

@record class DLLPool[@imm E](eDefault: E, poolSz: Z) {
  // Internal representation

  // "pointer" type for DLLPool, i.e., index to memory pool.
  // Out-of-bounds value means NULL

  val defaultNode: Node[E] = Node(eDefault, F, Null, Null)
  @spec def defaultNodeValue = Invariant(
    defaultNode == Node(eDefault, F, Null, Null)
  )

  val maxSz: Z = if (poolSz > 0) poolSz else 0
  val pool: PoolMem[E] = MSZ.create(maxSz, defaultNode)
  var free: Z = maxSz

  @pure def count_free_init(): Unit = {
    Contract(
      Requires(All(pool.indices)(i => pool(i) == defaultNode)),
      Ensures(count_free(pool) == maxSz)
    )
    var k: PoolPtr = 0
    while (k < maxSz) {
      Invariant(
        Modifies(k),
        0 <= k, k <= pool.size,
        k + count_free_rec(pool, k) == count_free(pool)
      )
      k = k + 1
    }
  }

  @spec def freeNodes = Invariant(
    freeNodesProp(pool, free)
  )

  @spec def maxSzPoolSize = Invariant(
    maxSz == pool.size
  )

  @spec def poolRight = Invariant(
    poolRightProp(pool)
  )

  @spec def poolRightValid = Invariant(
    poolRightValidProp(pool, tail)
  )

  @spec def poolRightUsed = Invariant(
    poolRightUsedProp(pool)
  )

  var head: PoolPtr = Null

  @spec def headIsPointer = Invariant(
    isPointer(pool, head)
  )

  @spec def headIsUsed = Invariant(
    isValidPointer(pool, head) ___>: pool(head).used
  )

  @spec def headNullEmpty = Invariant(
    headNullEmptyProp(pool, head)
  )

  @spec def headNodeLeft = Invariant(
    isValidPointer(pool, head) ___>: (pool(head).left == Null)
  )

  var tail: PoolPtr = Null

  @spec def tailIsPointer = Invariant(
    isPointer(pool, tail)
  )

  @spec def headTailSame = Invariant(
    (head == Null) == (tail == Null)
  )

  @spec var list: List[E] = $

  @spec var size: Z = $

  def initPool(): Unit = {
    Contract(
      Ensures(All(pool.indices)(i => pool(i) == defaultNode),
              count_free(pool) == maxSz))
    var p: PoolPtr = 0;
    while (p < pool.size) {
      Invariant(
        Modifies(p),
        0 <= p, p <= pool.size,
        All(0 until p)(i => pool(i) == defaultNode)
      )
      pool(p) = defaultNode
      p = p + 1
    }
    Spec { count_free_init() }
  }

  @pure def isEmpty: B = {
    Contract(Ensures(Res == (head == Null & tail == Null)))
    return head == Null
  }

  @pure def sizeOf: Z = {
    Contract(
      Requires(refinesProp(pool, head, list)),
      Ensures(refinesProp(pool, head, list), Res == list.length))
    var res: Z = 0
    var p = head
    @spec var l = list
    Spec { length_impl_with_acc(list) }
    while (!isLeaf(p)) {
      Invariant(
        Modifies(res, p, l),
        refinesProp(pool, p, l), isPointer(pool, p),
        l.length_acc(res) == list.length
      )
      Spec { length_impl_with_acc(l.tl)
             refines_p_not_Nil(pool, p, l)
             refines_p_sublist(pool, p, l) }
      res = res + 1
      p = pool(p).right
      Spec { l = l.tl }
    }
    return res
  }

  def findFreeNode(): PoolPtr = {
    Contract(
      Case(
        Requires(refinesProp(pool, head, list), free > 0),
        Ensures(
          isValidPointer(pool, Res), !pool(Res[Z]).used,
          refinesProp(pool, head, list)
        )
      ),
      Case(
        Requires(refinesProp(pool, head, list), free <= 0),
        Ensures(
          isPointer(pool, Res), !isValidPointer(pool, Res),
          refinesProp(pool, head, list)
        )
      )
    )
    if (free <= 0) {
      return Null
    }
    Spec { count_free_space(pool) }
    var p: PoolPtr = 0
    while (pool(p).used) { // changed test for defaultNode against .used
      Invariant(
        Modifies(p),
        0 <= p, p < pool.size,
        Exists(p until pool.size)(k => !pool(k).used)
      )
      p = p + 1
    }
    return p
  }

// SHA: needed to swap initPool with the two assignments because initPool
  // expects the invariant to be true initially. One could also consider to
  // permit "internal" non-invariant auxiliary functions that do not belong to the
  // classes interface.
  def clear(): Unit = {
    Contract(Ensures(refinesProp(pool, head, list)))
    initPool()
    head = Null
    tail = Null
    free = maxSz
    Spec { list = Nil() }
  }

  def nth(n: Z): Option[E] = {
    Contract(
      Case(
        Requires(refinesProp(pool, head, list), 0 <= n, n < sizeOf),
        Ensures(
          refinesProp(pool, head, list),
          Res == Some(list.nth(n)))
      ),
      Case(
        Requires(refinesProp(pool, head, list), n < 0),
        Ensures(
          refinesProp(pool, head, list),
          Res == None[E]())
      ),
      Case(
        Requires(refinesProp(pool, head, list), n >= sizeOf),
        Ensures(
          refinesProp(pool, head, list),
          Res == None[E]())
      )
    )
    if (n < 0 || n >= sizeOf) {
      return None[E]()
    }
    Spec { length_bound(list) }
    Deduce(
      |- (refinesProp(pool, head, list)),
      |- (list.length == sizeOf),
      |- (sizeOf > 0))
    var i: Z = n
    var p: PoolPtr = head
    Spec { refines_nth_head(pool, head, list) }
    Deduce(
      |- (list.length > 0),
      |- (pool(p).elem == list.nth(n - i)))
    @spec var l = list
    while (i > 0) {
      Invariant(
        Modifies(i, p, l),
        refinesProp(pool, p, l),
        isValidPointer(pool, p),
        0 <= i, i <= n, 0 <= n , n < list.length,
        l.length == list.length - (n - i),
        l.length > 0,
        l == list.drop(n - i),
        l.hd == pool(p).elem,
        pool(p).elem == list.nth(n - i)
      )
      Spec {
        refines_p_sublist(pool, p, l)
        length_decr_tl(l)
        drop_tl_other(l, list, n - i)
      }
      p = pool(p).right
      Spec { l = l.tl }
      i = i - 1
      Spec {
        refines_list_head(pool, p, l)
        drop_hd_nth(list, n - i)
      }
    }
    Deduce(|- (pool(p).elem== list.nth(n)))
    return Some(pool(p).elem)
  }

  def cons(elem: E): Unit = {
    Contract(Modifies(list),
      Case(
        Requires(free > 0, refinesProp(pool, head, list)),
        Ensures(refinesProp(pool, head, list),
                list == Cons(elem, In(list)))),
      Case(
        Requires(free <= 0, refinesProp(pool, head, list)),
        Ensures(refinesProp(pool, head, list))))
    if (free > 0) {
      if (isEmpty) {
        head = 0
        tail = 0
        @spec val qool = pool
        pool(0) = Node(elem, T, Null, Null)
        Spec { count_free_on_alloc(qool, pool, 0)
               list = List.make(elem) }
      } else {
        val pnew: Z = findFreeNode()
        @spec val qool = pool // permits easy access to "old" pool value
        pool(pnew) = Node(elem, T, Null, head)
        Spec { unusedInv(qool, head, list, pool, pnew)
               refinesNewHead(pool, head, list, pnew, elem)
               count_free_on_alloc(qool, pool, pnew) }
        @spec val rool = pool
        pool(head) = pool(head)(left = pnew)
        Spec { listCoincidence(pool, rool, head)
               freeCoincidence(pool, rool) }
        head = pnew
        Deduce(|- (poolRightProp(pool)),
               |- (poolRightValidProp(pool, tail)),
               |- (poolRightUsedProp(pool)))
        Spec { list = Cons(elem, list) }
      }
      free = free - 1
    }
  }

}

@anvil.test def test0(): Unit = {
  val dll = DLLPool[Z](0, 3)
  dll.initPool()
  dll.cons(0)
  println(dll.sizeOf)
  assert(dll.sizeOf == 1)
  println(dll.nth(0).asInstanceOf[Some[Z]].value)
  assert(dll.nth(0).asInstanceOf[Some[Z]].value == 0)
  println()
}

@anvil.test def test1(): Unit = {
  val dll = DLLPool[Z](0, 3)
  dll.initPool()
  dll.cons(5)
  dll.cons(3)
  println(dll.sizeOf)
  println(dll.nth(0).asInstanceOf[Some[Z]].value)
  println(dll.nth(1).asInstanceOf[Some[Z]].value)
  assert(dll.sizeOf == 2)
  assert(dll.nth(0).asInstanceOf[Some[Z]].value == 3)
  assert(dll.nth(1).asInstanceOf[Some[Z]].value == 5)
  println()
}

@anvil.test def test2(): Unit = {
  val dll = DLLPool[Z](0, 3)
  dll.initPool()
  dll.cons(5)
  dll.cons(3)
  dll.cons(2)
  println(dll.sizeOf)
  println(dll.nth(0).asInstanceOf[Some[Z]].value)
  println(dll.nth(1).asInstanceOf[Some[Z]].value)
  println(dll.nth(2).asInstanceOf[Some[Z]].value)
  assert(dll.sizeOf == 3)
  assert(dll.nth(0).asInstanceOf[Some[Z]].value == 2)
  assert(dll.nth(1).asInstanceOf[Some[Z]].value == 3)
  assert(dll.nth(2).asInstanceOf[Some[Z]].value == 5)
  println()
}
