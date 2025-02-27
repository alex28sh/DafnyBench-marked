method Index(n: int) returns (i: int)
  // pre-conditions-start
  requires 1 <= n
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < n
  // post-conditions-end
{
// impl-start
  i := n / 2;
// impl-end
}

method Min(x: int, y: int) returns (m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures m <= x && m <= y
  ensures m == x || m == y
  // post-conditions-end
{
// impl-start
  if x >= y {
    m := y;
  } else {
    m := x;
  }
  // assert-start
  assert m <= x && m <= y;
  // assert-end

// impl-end
}

method Max(x: int, y: int) returns (m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if x >= y {
    m := x;
  } else {
    m := y;
  }
  // assert-start
  assert m >= x && m >= y;
  // assert-end

// impl-end
}

method MaxSum(x: int, y: int)
    returns (s: int, m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == x + y
  ensures m == if x >= y then x else y
  // post-conditions-end
{
// impl-start
  s := x + y;
  if x >= y {
    m := x;
  } else {
    m := y;
  }
// impl-end
}

method MaxSumCaller()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x: int := 1928;
  var y: int := 1;
  var a, b: int;
  a, b := MaxSum(x, y);
  // assert-start
  assert a == 1929;
  // assert-end

  // assert-start
  assert b == 1928;
  // assert-end

// impl-end
}

method ReconstructFromMaxSum(s: int, m: int)
    returns (x: int, y: int)
  // pre-conditions-start
  requires s <= 2 * m
  // pre-conditions-end
  // post-conditions-start
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
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
