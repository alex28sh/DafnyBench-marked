function power(n: real, alpha: real): real
  requires n > 0.0 && alpha > 0.0
  ensures power(n, alpha) > 0.0
// pure-end

function log(n: real, alpha: real): real
  requires n > 0.0 && alpha > 0.0
  ensures log(n, alpha) > 0.0
// pure-end

lemma consistency(n: real, alpha: real)
  // pre-conditions-start
  requires n > 0.0 && alpha > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures log(power(n, alpha), alpha) == n
  ensures power(log(n, alpha), alpha) == n
  // post-conditions-end

lemma logarithmSum(n: real, alpha: real, x: real, y: real)
  // pre-conditions-start
  requires n > 0.0 && alpha > 0.0
  requires x > 0.0
  requires n == x * y
  // pre-conditions-end
  // post-conditions-start
  ensures log(n, alpha) == log(x, alpha) + log(y, alpha)
  // post-conditions-end

lemma powerLemma(n: real, alpha: real)
  // pre-conditions-start
  requires n > 0.0 && alpha > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures power(n, alpha) * alpha == power(n + 1.0, alpha)
  // post-conditions-end

lemma power1(alpha: real)
  // pre-conditions-start
  requires alpha > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures power(1.0, alpha) == alpha
  // post-conditions-end

lemma test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var pow3 := power(3.0, 4.0);
  consistency(3.0, 4.0);
  assert log(pow3, 4.0) == 3.0;
  var log6 := log(6.0, 8.0);
  logarithmSum(6.0, 8.0, 2.0, 3.0);
  assert log6 == log(2.0, 8.0) + log(3.0, 8.0);
// impl-end
}

lemma test2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var pow3 := power(3.0, 4.0);
  var power4 := power(4.0, 4.0);
  powerLemma(3.0, 4.0);
  assert pow3 * 4.0 == power4;
// impl-end
}

method pow(n: nat, alpha: real) returns (product: real)
  // pre-conditions-start
  requires n > 0
  requires alpha > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures product == power(n as real, alpha)
  // post-conditions-end
{
// impl-start
  product := alpha;
  var i: nat := 1;
  // assert-start
  power1(alpha);
  // assert-end

  // assert-start
  assert product == power(1.0, alpha);
  // assert-end

  while i < n
    // invariants-start

    invariant i <= n
    invariant product == power(i as real, alpha)
    // invariants-end

  {
    // assert-start
    powerLemma(i as real, alpha);
    // assert-end

    product := product * alpha;
    i := i + 1;
  }
  // assert-start
  assert i == n;
  // assert-end

  // assert-start
  assert product == power(n as real, alpha);
  // assert-end

// impl-end
}
