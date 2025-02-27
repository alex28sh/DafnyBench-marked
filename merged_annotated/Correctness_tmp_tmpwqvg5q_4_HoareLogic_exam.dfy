function gcd(a: nat, b: nat): nat
// pure-end

lemma r1(a: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures gcd(a, 0) == a
  // post-conditions-end

lemma r2(a: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures gcd(a, a) == a
  // post-conditions-end

lemma r3(a: nat, b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures gcd(a, b) == gcd(b, a)
  // post-conditions-end

lemma r4(a: nat, b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)
  // post-conditions-end

method GCD1(a: int, b: int) returns (r: int)
  // pre-conditions-start
  requires a > 0 && b > 0
  // pre-conditions-end
  // post-conditions-start
  ensures gcd(a, b) == r
  decreases b
  // post-conditions-end
{
// impl-start
  if a < b {
    // assert-start
    r3(a, b);
    // assert-end

    r := GCD1(b, a);
  } else if a % b == 0 {
    // assert-start
    r4(a, b);
    // assert-end

    // assert-start
    assert b > 0;
    // assert-end

    // assert-start
    assert gcd(a, b) == gcd(b, a % b);
    // assert-end

    // assert-start
    assert a % b == 0;
    // assert-end

    // assert-start
    assert gcd(a, b) == gcd(b, 0);
    // assert-end

    // assert-start
    r1(b);
    // assert-end

    // assert-start
    assert gcd(a, b) == b;
    // assert-end

    r := b;
    // assert-start
    assert gcd(a, b) == r;
    // assert-end

  } else {
    // assert-start
    r4(a, b);
    // assert-end

    r := GCD1(b, a % b);
    // assert-start
    assert gcd(a, b) == r;
    // assert-end

  }
  // assert-start
  assert gcd(a, b) == r;
  // assert-end

// impl-end
}

method GCD2(a: int, b: int) returns (r: int)
  // pre-conditions-start
  requires a > 0 && b >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures gcd(a, b) == r
  decreases b
  // post-conditions-end
{
// impl-start
  // assert-start
  r1(a);
  // assert-end

  // assert-start
  r4(a, b);
  // assert-end

  // assert-start
  assert (b != 0 || (a > 0 && b >= 0 && gcd(a, b) == a)) && (b < 0 || b == 0 || (b > 0 && a % b >= 0 ==> gcd(a, b) == gcd(b, a % b)));
  // assert-end

  // assert-start
  assert b != 0 || (a > 0 && b >= 0 && gcd(a, b) == a);
  // assert-end

  // assert-start
  assert b == 0 ==> a > 0 && b >= 0 && gcd(a, b) == a;
  // assert-end

  // assert-start
  assert b < 0 || b == 0 || (b > 0 && a % b >= 0 ==> gcd(a, b) == gcd(b, a % b));
  // assert-end

  // assert-start
  assert b >= 0 && b != 0 ==> b > 0 && a % b >= 0 ==> gcd(a, b) == gcd(b, a % b);
  // assert-end

  if b == 0 {
    // assert-start
    r1(a);
    // assert-end

    // assert-start
    assert gcd(a, b) == a;
    // assert-end

    r := a;
    // assert-start
    assert gcd(a, b) == r;
    // assert-end

  } else {
    // assert-start
    r4(a, b);
    // assert-end

    // assert-start
    assert b > 0 && a % b >= 0 ==> gcd(a, b) == gcd(b, a % b);
    // assert-end

    r := GCD2(b, a % b);
    // assert-start
    assert gcd(a, b) == r;
    // assert-end

  }
  // assert-start
  assert gcd(a, b) == r;
  // assert-end

// impl-end
}
