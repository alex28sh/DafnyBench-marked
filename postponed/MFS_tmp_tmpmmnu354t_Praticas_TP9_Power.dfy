function power(x: real, n: nat): real
{
  if n == 0 then
    1.0
  else
    x * power(x, n - 1)
}
// pure-end

method powerIter(b: real, n: nat) returns (p: real)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p == power(b, n)
  // post-conditions-end
{
// impl-start
  p := 1.0;
  var i := 0;
  while i < n
    // invariants-start

    invariant p == power(b, i) && 0 <= i <= n
    // invariants-end

  {
    p := p * b;
    i := i + 1;
  }
// impl-end
}

lemma {:induction e1} powDist(b: real, e1: nat, e2: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures power(b, e1 + e2) == power(b, e1) * power(b, e2)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma {:induction false} distributiveProperty(x: real, a: nat, b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures power(x, a) * power(x, b) == power(x, a + b)
  // post-conditions-end
{
// impl-start
  if a == 0 {
    assert power(x, a) * power(x, b) == 1.0 * power(x, b) == power(x, b) == power(x, a + b);
  } else {
    distributiveProperty(x, a - 1, b);
    assert power(x, a) * power(x, b) == x * power(x, a - 1) * power(x, b) == x * (power(x, a - 1) * power(x, b)) == x * power(x, a - 1 + b) == power(x, a + b);
  }
// impl-end
}

method powerOpt(b: real, n: nat) returns (p: real)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p == power(b, n)
  // post-conditions-end
{
// impl-start
  if n == 0 {
    return 1.0;
  } else if n % 2 == 0 {
    // assert-start
    distributiveProperty(b, n / 2, n / 2);
    // assert-end

    var r := powerOpt(b, n / 2);
    return r * r;
  } else {
    // assert-start
    distributiveProperty(b, (n - 1) / 2, (n - 1) / 2);
    // assert-end

    var r := powerOpt(b, (n - 1) / 2);
    return r * r * b;
  }
// impl-end
}

method testPower()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var p1 := powerIter(2.0, 5);
  var p2 := powerOpt(2.0, 5);
  print "P1: ", p1, "\n";
  print "P2: ", p2, "\n";
  // assert-start
  assert p1 == 32.0;
  // assert-end

  // assert-start
  assert p2 == 32.0;
  // assert-end

// impl-end
}
