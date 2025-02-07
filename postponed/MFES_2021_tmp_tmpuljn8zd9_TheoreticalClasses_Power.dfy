function power(x: real, n: nat): real
  decreases n
{
  if n == 0 then
    1.0
  else
    x * power(x, n - 1)
}
// pure-end

method powerIter(x: real, n: nat) returns (p: real)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p == power(x, n)
  // post-conditions-end
{
// impl-start
  var i := 0;
  p := 1.0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n && p == power(x, i)
    decreases n - i
    // invariants-end

  {
    p := p * x;
    i := i + 1;
  }
// impl-end
}

method powerOpt(x: real, n: nat) returns (p: real)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p == power(x, n)
  decreases n
  // post-conditions-end
{
// impl-start
  if n == 0 {
    return 1.0;
  } else if n == 1 {
    return x;
  } else if n % 2 == 0 {
    // assert-start
    distributiveProperty(x, n / 2, n / 2);
    // assert-end

    var temp := powerOpt(x, n / 2);
    return temp * temp;
  } else {
    // assert-start
    distributiveProperty(x, (n - 1) / 2, (n - 1) / 2);
    // assert-end

    var temp := powerOpt(x, (n - 1) / 2);
    return temp * temp * x;
  }
// impl-end
}

lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures power(x, a) * power(x, b) == power(x, a + b)
  // post-conditions-end
{
// impl-start
// impl-end
}

method testPowerIter()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var p1 := powerIter(2.0, 5);
  // assert-start
  assert p1 == 32.0;
  // assert-end

// impl-end
}

method testPowerOpt()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var p1 := powerOpt(2.0, 5);
  // assert-start
  assert p1 == 32.0;
  // assert-end

// impl-end
}
