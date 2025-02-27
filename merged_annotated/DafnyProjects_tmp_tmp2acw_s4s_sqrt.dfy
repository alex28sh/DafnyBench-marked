method sqrt(x: real) returns (r: real)
  // pre-conditions-start
  requires x >= 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures r * r == x && r >= 0.0
  // post-conditions-end

method testSqrt()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var r := sqrt(4.0);
  if r < 2.0 {
    // assert-start
    monotonicSquare(r, 2.0);
    // assert-end

  }
  // assert-start
  assert r == 2.0;
  // assert-end

// impl-end
}

lemma monotonicMult(c: real, x: real, y: real)
  // pre-conditions-start
  requires x < y && c > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures c * x < c * y
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma monotonicSquare(x: real, y: real)
  // pre-conditions-start
  requires 0.0 < x < y
  // pre-conditions-end
  // post-conditions-start
  ensures 0.0 < x * x < y * y
  // post-conditions-end
{
// impl-start
  monotonicMult(x, x, y);
// impl-end
}
