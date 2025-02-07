function power(x: real, n: nat): real
{
  if n == 0 then
    1.0
  else
    x * power(x, n - 1)
}
// pure-end

method powerDC(x: real, n: nat) returns (p: real)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p == power(x, n)
  // post-conditions-end
{
// impl-start
  if n == 0 {
    return 1.0;
  } else if n == 1 {
    return x;
  } else if n % 2 == 0 {
    // assert-start
    productOfPowers(x, n / 2, n / 2);
    // assert-end

    var temp := powerDC(x, n / 2);
    return temp * temp;
  } else {
    // assert-start
    productOfPowers(x, (n - 1) / 2, (n - 1) / 2);
    // assert-end

    var temp := powerDC(x, (n - 1) / 2);
    return temp * temp * x;
  }
// impl-end
}

lemma {:induction a} productOfPowers(x: real, a: nat, b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures power(x, a) * power(x, b) == power(x, a + b)
  // post-conditions-end
{
// impl-start
// impl-end
}

method testPowerDC()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var p1 := powerDC(2.0, 5);
  // assert-start
  assert p1 == 32.0;
  // assert-end

  var p2 := powerDC(-2.0, 2);
  // assert-start
  assert p2 == 4.0;
  // assert-end

  var p3 := powerDC(-2.0, 1);
  // assert-start
  assert p3 == -2.0;
  // assert-end

  var p4 := powerDC(-2.0, 0);
  // assert-start
  assert p4 == 1.0;
  // assert-end

  var p5 := powerDC(0.0, 0);
  // assert-start
  assert p5 == 1.0;
  // assert-end

// impl-end
}
