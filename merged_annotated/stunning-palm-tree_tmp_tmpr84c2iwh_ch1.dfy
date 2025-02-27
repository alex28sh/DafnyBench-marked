method Triple(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  var y := 2 * x;
  r := y + x;
  // assert-start
  assert r == 3 * x;
  // assert-end

// impl-end
}

method Caller()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var t := Triple(18);
  // assert-start
  assert t < 100;
  // assert-end

// impl-end
}

method MinUnderSpec(x: int, y: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r <= x && r <= y
  // post-conditions-end
{
// impl-start
  if x <= y {
    r := x - 1;
  } else {
    r := y - 1;
  }
// impl-end
}

method Min(x: int, y: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r <= x && r <= y
  ensures r == x || r == y
  // post-conditions-end
{
// impl-start
  if x <= y {
    r := x;
  } else {
    r := y;
  }
// impl-end
}

method MaxSum(x: int, y: int)
    returns (s: int, m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
  // post-conditions-end

method MaxSumCaller()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var s, m := MaxSum(1928, 1);
  // assert-start
  assert s == 1929;
  // assert-end

  // assert-start
  assert m == 1928;
  // assert-end

// impl-end
}

method ReconstructFromMaxSum(s: int, m: int)
    returns (x: int, y: int)
  // pre-conditions-start
  requires s - m <= m
  // pre-conditions-end
  // post-conditions-start
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
  // post-conditions-end
{
// impl-start
  x := m;
  y := s - m;
// impl-end
}

method TestMaxSum(x: int, y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var s, m := MaxSum(x, y);
  var xx, yy := ReconstructFromMaxSum(s, m);
  // assert-start
  assert (xx == x && yy == y) || (xx == y && yy == x);
  // assert-end

// impl-end
}

function Average(a: int, b: int): int
{
  (a + b) / 2
}
// pure-end

method Triple'(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Average(2 * r, 6 * x) == 6 * x
  // post-conditions-end
{
// impl-start
  r := x + x + x;
// impl-end
}
