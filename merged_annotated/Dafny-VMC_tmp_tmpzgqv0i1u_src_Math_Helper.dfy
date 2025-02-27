// Dafny-VMC_tmp_tmpzgqv0i1u_src_Math_Helper.dfy


module Helper {
  function Power(b: nat, n: nat): (p: nat)
    ensures b > 0 ==> p > 0
  {
    match n
    case 0 =>
      1
    case 1 =>
      b
    case _ /* _v0 */ =>
      b * Power(b, n - 1)
  }
  // pure-end

  function Log2Floor(n: nat): nat
    requires n >= 1
    decreases n
  {
    if n < 2 then
      0
    else
      Log2Floor(n / 2) + 1
  }
  // pure-end

  lemma Log2FloorDef(n: nat)
    // pre-conditions-start
    requires n >= 1
    // pre-conditions-end
    // post-conditions-start
    ensures Log2Floor(2 * n) == Log2Floor(n) + 1
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  function boolToNat(b: bool): nat
  {
    if b then
      1
    else
      0
  }
  // pure-end

  lemma Congruence<T, U>(x: T, y: T, f: T -> U)
    // pre-conditions-start
    requires x == y
    // pre-conditions-end
    // post-conditions-start
    ensures f(x) == f(y)
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma DivisionSubstituteAlternativeReal(x: real, a: real, b: real)
    // pre-conditions-start
    requires a == b
    requires x != 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures a / x == b / x
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma DivModAddDenominator(n: nat, m: nat)
    // pre-conditions-start
    requires m > 0
    // pre-conditions-end
    // post-conditions-start
    ensures (n + m) / m == n / m + 1
    ensures (n + m) % m == n % m
    // post-conditions-end
  {
  // impl-start
    var zp := (n + m) / m - n / m - 1;
    assert 0 == m * zp + (n + m) % m - n % m;
  // impl-end
  }

  lemma DivModIsUnique(n: int, m: int, a: int, b: int)
    // pre-conditions-start
    requires n >= 0
    requires m > 0
    requires 0 <= b < m
    requires n == a * m + b
    // pre-conditions-end
    // post-conditions-start
    ensures a == n / m
    ensures b == n % m
    // post-conditions-end
  {
  // impl-start
    if a == 0 {
      assert n == b;
    } else {
      assert (n - m) / m == a - 1 && (n - m) % m == b by {
        DivModIsUnique(n - m, m, a - 1, b);
      }
      assert n / m == a && n % m == b by {
        DivModAddDenominator(n - m, m);
      }
    }
  // impl-end
  }

  lemma DivModAddMultiple(a: nat, b: nat, c: nat)
    // pre-conditions-start
    requires a > 0
    // pre-conditions-end
    // post-conditions-start
    ensures (c * a + b) / a == c + b / a
    ensures (c * a + b) % a == b % a
    // post-conditions-end
  {
  // impl-start
    calc {
      a * c + b;
    ==
      a * c + (a * (b / a) + b % a);
    ==
      a * (c + b / a) + b % a;
    }
    DivModIsUnique(a * c + b, a, c + b / a, b % a);
  // impl-end
  }

  lemma DivisionByTwo(x: real)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures 0.5 * x == x / 2.0
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma PowerGreater0(base: nat, exponent: nat)
    // pre-conditions-start
    requires base >= 1
    // pre-conditions-end
    // post-conditions-start
    ensures Power(base, exponent) >= 1
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma Power2OfLog2Floor(n: nat)
    // pre-conditions-start
    requires n >= 1
    // pre-conditions-end
    // post-conditions-start
    ensures Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1)
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma NLtPower2Log2FloorOf2N(n: nat)
    // pre-conditions-start
    requires n >= 1
    // pre-conditions-end
    // post-conditions-start
    ensures n < Power(2, Log2Floor(2 * n))
    // post-conditions-end
  {
  // impl-start
    calc {
      n;
    <
      {
        Power2OfLog2Floor(n);
      }
      Power(2, Log2Floor(n) + 1);
    ==
      {
        Log2FloorDef(n);
      }
      Power(2, Log2Floor(2 * n));
    }
  // impl-end
  }

  lemma MulMonotonic(a: nat, b: nat, c: nat, d: nat)
    // pre-conditions-start
    requires a <= c
    requires b <= d
    // pre-conditions-end
    // post-conditions-start
    ensures a * b <= c * d
    // post-conditions-end
  {
  // impl-start
    calc {
      a * b;
    <=
      c * b;
    <=
      c * d;
    }
  // impl-end
  }

  lemma MulMonotonicStrictRhs(b: nat, c: nat, d: nat)
    // pre-conditions-start
    requires b < d
    requires c > 0
    // pre-conditions-end
    // post-conditions-start
    ensures c * b < c * d
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma MulMonotonicStrict(a: nat, b: nat, c: nat, d: nat)
    // pre-conditions-start
    requires a <= c
    requires b <= d
    requires (a != c && d > 0) || (b != d && c > 0)
    // pre-conditions-end
    // post-conditions-start
    ensures a * b < c * d
    // post-conditions-end
  {
  // impl-start
    if a != c && d > 0 {
      calc {
        a * b;
      <=
        {
          MulMonotonic(a, b, a, d);
        }
        a * d;
      <
        c * d;
      }
    }
    if b != d && c > 0 {
      calc {
        a * b;
      <=
        c * b;
      <
        {
          MulMonotonicStrictRhs(b, c, d);
        }
        c * d;
      }
    }
  // impl-end
  }

  lemma AdditionOfFractions(x: real, y: real, z: real)
    // pre-conditions-start
    requires z != 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures x / z + y / z == (x + y) / z
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma DivSubstituteDividend(x: real, y: real, z: real)
    // pre-conditions-start
    requires y != 0.0
    requires x == z
    // pre-conditions-end
    // post-conditions-start
    ensures x / y == z / y
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma DivSubstituteDivisor(x: real, y: real, z: real)
    // pre-conditions-start
    requires y != 0.0
    requires y == z
    // pre-conditions-end
    // post-conditions-start
    ensures x / y == x / z
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma DivDivToDivMul(x: real, y: real, z: real)
    // pre-conditions-start
    requires y != 0.0
    requires z != 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures x / y / z == x / (y * z)
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma NatMulNatToReal(x: nat, y: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures (x * y) as real == x as real * y as real
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma SimplifyFractions(x: real, y: real, z: real)
    // pre-conditions-start
    requires z != 0.0
    requires y != 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures x / z / (y / z) == x / y
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma PowerOfTwoLemma(k: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures 1.0 / Power(2, k) as real / 2.0 == 1.0 / Power(2, k + 1) as real
    // post-conditions-end
  {
  // impl-start
    calc {
      1.0 / Power(2, k) as real / 2.0;
    ==
      {
        DivDivToDivMul(1.0, Power(2, k) as real, 2.0);
      }
      1.0 / (Power(2, k) as real * 2.0);
    ==
      {
        NatMulNatToReal(Power(2, k), 2);
      }
      1.0 / (Power(2, k) * 2) as real;
    ==
      1.0 / Power(2, k + 1) as real;
    }
  // impl-end
  }
}
