// ironsync-osdi2023_tmp_tmpx80antoe_lib_Marshalling_Math.dfy


module Math {
  function {:opaque} power2(exp: nat): nat
    ensures power2(exp) > 0
  {
    if exp == 0 then
      1
    else
      2 * power2(exp - 1)
  }
  // pure-end

  lemma lemma_2toX()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures power2(8) == 256
    ensures power2(16) == 65536
    ensures power2(19) == 524288
    ensures power2(24) == 16777216
    ensures power2(32) == 4294967296
    ensures power2(60) == 1152921504606846976
    ensures power2(64) == 18446744073709551616
    // post-conditions-end
  {
  // impl-start
    reveal_power2();
  // impl-end
  }

  lemma lemma_power2_adds(e1: nat, e2: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures power2(e1 + e2) == power2(e1) * power2(e2)
    decreases e2
    // post-conditions-end
  {
  // impl-start
    reveal_power2();
    if e2 == 0 {
    } else {
      lemma_power2_adds(e1, e2 - 1);
    }
  // impl-end
  }

  lemma lemma_2toX32()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures power2(0) == 1
    ensures power2(1) == 2
    ensures power2(2) == 4
    ensures power2(3) == 8
    ensures power2(4) == 16
    ensures power2(5) == 32
    ensures power2(6) == 64
    ensures power2(7) == 128
    ensures power2(8) == 256
    ensures power2(9) == 512
    ensures power2(10) == 1024
    ensures power2(11) == 2048
    ensures power2(12) == 4096
    ensures power2(13) == 8192
    ensures power2(14) == 16384
    ensures power2(15) == 32768
    ensures power2(16) == 65536
    ensures power2(17) == 131072
    ensures power2(18) == 262144
    ensures power2(19) == 524288
    ensures power2(20) == 1048576
    ensures power2(21) == 2097152
    ensures power2(22) == 4194304
    ensures power2(23) == 8388608
    ensures power2(24) == 16777216
    ensures power2(25) == 33554432
    ensures power2(26) == 67108864
    ensures power2(27) == 134217728
    ensures power2(28) == 268435456
    ensures power2(29) == 536870912
    ensures power2(30) == 1073741824
    ensures power2(31) == 2147483648
    ensures power2(32) == 4294967296
    // post-conditions-end
  {
  // impl-start
    reveal_power2();
  // impl-end
  }

  lemma bounded_mul_eq_0(x: int, m: int)
    // pre-conditions-start
    requires -m < m * x < m
    // pre-conditions-end
    // post-conditions-start
    ensures x == 0
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma lemma_div_ind(x: int, d: int)
    // pre-conditions-start
    requires d > 0
    // pre-conditions-end
    // post-conditions-start
    ensures x / d + 1 == (x + d) / d
    // post-conditions-end
  {
  // impl-start
    assert d * (x / d + 1) == x / d * d + d == x - x % d + d;
    assert d * ((x + d) / d) == x + d - (x + d) % d;
    assert 0 <= x % d < d;
    assert 0 <= (x + d) % d < d;
    assert d * (x / d + 1) - d * ((x + d) / d) == (x + d) % d - x % d;
    assert -d < d * (x / d + 1) - d * ((x + d) / d) < d;
    assert -d < d * (x / d + 1 - (x + d) / d) < d;
    bounded_mul_eq_0(x / d + 1 - (x + d) / d, d);
  // impl-end
  }

  lemma lemma_add_mul_div(a: int, b: int, d: int)
    // pre-conditions-start
    requires d > 0
    // pre-conditions-end
    // post-conditions-start
    ensures (a + b * d) / d == a / d + b
    decreases if b > 0 then b else -b
    // post-conditions-end
  {
  // impl-start
    if b == 0 {
    } else if b > 0 {
      lemma_add_mul_div(a, b - 1, d);
      lemma_div_ind(a + (b - 1) * d, d);
    } else {
      lemma_add_mul_div(a, b + 1, d);
      lemma_div_ind(a + b * d, d);
    }
  // impl-end
  }

  lemma lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    // pre-conditions-start
    requires 0 < d
    requires 0 <= b < d
    // pre-conditions-end
    // post-conditions-start
    ensures (d * x + b) / d == x
    decreases if x > 0 then x else -x
    // post-conditions-end
  {
  // impl-start
    if x == 0 {
    } else if x > 0 {
      lemma_div_multiples_vanish_fancy(x - 1, b, d);
      lemma_div_ind(d * (x - 1) + b, d);
    } else {
      lemma_div_multiples_vanish_fancy(x + 1, b, d);
      lemma_div_ind(d * x + b, d);
    }
  // impl-end
  }

  lemma lemma_div_by_multiple(b: int, d: int)
    // pre-conditions-start
    requires 0 < d
    // pre-conditions-end
    // post-conditions-start
    ensures b * d / d == b
    // post-conditions-end
  {
  // impl-start
    lemma_div_multiples_vanish_fancy(b, 0, d);
  // impl-end
  }

  lemma lemma_mod_multiples_basic(x: int, m: int)
    // pre-conditions-start
    requires m > 0
    // pre-conditions-end
    // post-conditions-start
    ensures x * m % m == 0
    // post-conditions-end
  {
  // impl-start
    assert x * m % m == x * m - x * m / m * m;
    lemma_div_by_multiple(x, m);
    assert x * m / m == x;
    assert x * m - x * m / m * m == x * m - x * m == 0;
  // impl-end
  }

  lemma lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    // pre-conditions-start
    requires x < y
    requires y == m * z
    requires z > 0
    // pre-conditions-end
    // post-conditions-start
    ensures x / z < y / z
    // post-conditions-end
  {
  // impl-start
    lemma_mod_multiples_basic(m, z);
    if x / z <= m - 1 {
    } else {
      lemma_div_by_multiple_is_strongly_ordered(x, y - z, m - 1, z);
    }
  // impl-end
  }

  lemma lemma_power2_div_is_sub(x: int, y: int)
    // pre-conditions-start
    requires 0 <= x <= y
    // pre-conditions-end
    // post-conditions-start
    ensures power2(y - x) == power2(y) / power2(x) >= 0
    // post-conditions-end
  {
  // impl-start
    calc {
      power2(y) / power2(x);
      {
        lemma_power2_adds(y - x, x);
      }
      power2(y - x) * power2(x) / power2(x);
      {
        lemma_div_by_multiple(power2(y - x), power2(x));
      }
      power2(y - x);
    }
  // impl-end
  }

  lemma lemma_div_denominator(x: int, c: nat, d: nat)
    // pre-conditions-start
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    // pre-conditions-end
    // post-conditions-start
    ensures c * d != 0
    ensures x / c / d == x / (c * d)
    // post-conditions-end
  {
  // impl-start
    if x < c * d {
      assert x / (c * d) == 0;
      assert x / c < d;
      assert x / c / d == 0;
    } else {
      calc {
        x / c / d;
        (x - c * d + c * d) / c / d;
        {
          lemma_add_mul_div(x - c * d, d, c);
        }
        ((x - c * d) / c + d) / d;
        {
          lemma_div_ind((x - c * d) / c, d);
        }
        (x - c * d) / c / d + 1;
        {
          lemma_div_denominator(x - c * d, c, d);
        }
        (x - c * d) / (c * d) + 1;
        {
          lemma_div_ind(x - c * d, c * d);
        }
        x / (c * d);
      }
    }
  // impl-end
  }
}
