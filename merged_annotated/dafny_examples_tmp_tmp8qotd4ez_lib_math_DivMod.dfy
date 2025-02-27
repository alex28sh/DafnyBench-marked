// dafny_examples_tmp_tmp8qotd4ez_lib_math_DivMod.dfy


module DivMod {
  function {:opaque} DivSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {
    if a < b then
      0
    else
      1 + DivSub(a - b, b)
  }
  // pure-end

  function {:opaque} ModSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {
    if a < b then
      a
    else
      ModSub(a - b, b)
  }
  // pure-end

  lemma DivModAdd1(a: int, b: int)
    // pre-conditions-start
    requires b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures (a + b) % b == a % b
    ensures (a + b) / b == a / b + 1
    // post-conditions-end
  {
  // impl-start
    var c := (a + b) / b - a / b - 1;
    assert c * b + (a + b) % b - a % b == 0;
  // impl-end
  }

  lemma DivModSub1(a: int, b: int)
    // pre-conditions-start
    requires b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures (a - b) % b == a % b
    ensures (a - b) / b == a / b - 1
    // post-conditions-end
  {
  // impl-start
    var c := (a - b) / b - a / b + 1;
    assert c * b + (a - b) % b - a % b == 0;
  // impl-end
  }

  lemma ModEq(a: int, b: int)
    // pre-conditions-start
    requires 0 <= a && 0 < b
    // pre-conditions-end
    // post-conditions-start
    ensures a % b == ModSub(a, b)
    // post-conditions-end
  {
  // impl-start
    reveal ModSub();
    if a >= b {
      DivModSub1(a, b);
    }
  // impl-end
  }

  lemma DivEq(a: int, b: int)
    // pre-conditions-start
    requires 0 <= a && 0 < b
    // pre-conditions-end
    // post-conditions-start
    ensures a / b == DivSub(a, b)
    // post-conditions-end
  {
  // impl-start
    reveal DivSub();
    if a >= b {
      DivModSub1(a, b);
    }
  // impl-end
  }

  lemma DivModSpec'(a: int, b: int, q: int, r: int)
    // pre-conditions-start
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    // pre-conditions-end
    // post-conditions-start
    ensures ModSub(a, b) == r
    ensures DivSub(a, b) == q
    // post-conditions-end
  {
  // impl-start
    reveal ModSub();
    reveal DivSub();
    if q > 0 {
      DivModSpec'(a - b, b, q - 1, r);
    }
  // impl-end
  }

  lemma DivModSpec(a: int, b: int, q: int, r: int)
    // pre-conditions-start
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    // pre-conditions-end
    // post-conditions-start
    ensures a % b == r
    ensures a / b == q
    // post-conditions-end
  {
  // impl-start
    ModEq(a, b);
    DivEq(a, b);
    DivModSpec'(a, b, q, r);
  // impl-end
  }

  lemma DivMul(a: int, b: int)
    // pre-conditions-start
    requires 0 <= a && 0 < b
    // pre-conditions-end
    // post-conditions-start
    ensures a * b / b == a
    // post-conditions-end
  {
  // impl-start
    DivModSpec(a * b, b, a, 0);
  // impl-end
  }

  lemma DivModMulAdd(a: int, b: int, c: int)
    // pre-conditions-start
    requires 0 <= a && 0 <= c < b && 0 < b
    // pre-conditions-end
    // post-conditions-start
    ensures (a * b + c) / b == a
    ensures (a * b + c) % b == c
    // post-conditions-end
  {
  // impl-start
    DivModSpec(a * b + c, b, a, c);
  // impl-end
  }
}
