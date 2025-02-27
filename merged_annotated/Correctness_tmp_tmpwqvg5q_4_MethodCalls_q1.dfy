function fusc(n: int): nat
// pure-end

lemma rule1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures fusc(0) == 0
  // post-conditions-end

lemma rule2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures fusc(1) == 1
  // post-conditions-end

lemma rule3(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures fusc(2 * n) == fusc(n)
  // post-conditions-end

lemma rule4(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures fusc(2 * n + 1) == fusc(n) + fusc(n + 1)
  // post-conditions-end

method ComputeFusc(N: int) returns (b: int)
  // pre-conditions-start
  requires N >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures b == fusc(N)
  // post-conditions-end
{
// impl-start
  b := 0;
  var n, a := N, 1;
  // assert-start
  assert 0 <= n <= N;
  // assert-end

  // assert-start
  assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
  // assert-end

  while n != 0
    // invariants-start

    invariant 0 <= n <= N
    invariant fusc(N) == a * fusc(n) + b * fusc(n + 1)
    decreases n
    // invariants-end

  {
    ghost var d := n;
    // assert-start
    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

    // assert-start
    assert n != 0;
    // assert-end

    // assert-start
    assert (n % 2 != 0 && n % 2 == 0) || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

    // assert-start
    assert n % 2 != 0 || n % 2 == 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

    // assert-start
    assert n % 2 != 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

    // assert-start
    assert n % 2 == 0 || fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

    // assert-start
    assert n % 2 == 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

    // assert-start
    assert n % 2 != 0 ==> fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

    if n % 2 == 0 {
      // assert-start
      rule4(n / 2);
      // assert-end

      // assert-start
      assert fusc(n / 2 + 1) == fusc(n + 1) - fusc(n / 2);
      // assert-end

      // assert-start
      rule3(n / 2);
      // assert-end

      // assert-start
      assert fusc(n / 2) == fusc(n);
      // assert-end

      // assert-start
      assert fusc(N) == (a + b) * fusc(n / 2) + b * fusc(n / 2 + 1);
      // assert-end

      a := a + b;
      // assert-start
      assert fusc(N) == a * fusc(n / 2) + b * fusc(n / 2 + 1);
      // assert-end

      n := n / 2;
      // assert-start
      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
      // assert-end

    } else {
      // assert-start
      rule4((n - 1) / 2);
      // assert-end

      // assert-start
      assert fusc(n) - fusc((n - 1) / 2) == fusc((n - 1) / 2 + 1);
      // assert-end

      // assert-start
      rule3((n - 1) / 2);
      // assert-end

      // assert-start
      assert fusc((n - 1) / 2) == fusc(n - 1);
      // assert-end

      // assert-start
      assert fusc((n - 1) / 2 + 1) == fusc((n + 1) / 2);
      // assert-end

      // assert-start
      rule3((n + 1) / 2);
      // assert-end

      // assert-start
      assert fusc((n + 1) / 2) == fusc(n + 1);
      // assert-end

      // assert-start
      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
      // assert-end

      // assert-start
      assert fusc(N) == b * fusc((n - 1) / 2 + 1) + a * fusc(n);
      // assert-end

      // assert-start
      assert fusc(N) == b * fusc(n) - b * fusc(n) + b * fusc((n - 1) / 2 + 1) + a * fusc(n);
      // assert-end

      // assert-start
      assert fusc(N) == b * fusc(n) - b * (fusc(n) - fusc((n - 1) / 2 + 1)) + a * fusc(n);
      // assert-end

      // assert-start
      assert fusc(N) == b * fusc(n) - b * fusc((n - 1) / 2) + a * fusc(n);
      // assert-end

      // assert-start
      assert fusc(N) == b * fusc(n) - b * fusc(n - 1) + a * fusc(n);
      // assert-end

      // assert-start
      assert fusc(N) == b * fusc(n) - b * fusc(n - 1) + a * fusc(n);
      // assert-end

      // assert-start
      assert fusc(N) == a * fusc(n - 1) + b * fusc(n) - b * fusc(n - 1) + a * fusc(n) - a * fusc(n - 1);
      // assert-end

      // assert-start
      assert fusc(N) == a * fusc(n - 1) + (b + a) * (fusc(n) - fusc(n - 1));
      // assert-end

      // assert-start
      assert fusc(N) == a * fusc(n - 1) + (b + a) * (fusc(n) - fusc((n - 1) / 2));
      // assert-end

      // assert-start
      assert fusc(N) == a * fusc((n - 1) / 2) + (b + a) * fusc((n - 1) / 2 + 1);
      // assert-end

      b := b + a;
      // assert-start
      assert fusc(N) == a * fusc((n - 1) / 2) + b * fusc((n - 1) / 2 + 1);
      // assert-end

      n := (n - 1) / 2;
      // assert-start
      assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
      // assert-end

    }
    // assert-start
    assert n < d;
    // assert-end

    // assert-start
    assert fusc(N) == a * fusc(n) + b * fusc(n + 1);
    // assert-end

  }
  // assert-start
  assert n == 0;
  // assert-end

  // assert-start
  rule1();
  // assert-end

  // assert-start
  assert fusc(0) == 0;
  // assert-end

  // assert-start
  rule2();
  // assert-end

  // assert-start
  assert fusc(1) == 1;
  // assert-end

  // assert-start
  assert fusc(N) == a * fusc(0) + b * fusc(0 + 1);
  // assert-end

  // assert-start
  assert fusc(N) == a * 0 + b * 1;
  // assert-end

  // assert-start
  assert b == fusc(N);
  // assert-end

// impl-end
}
