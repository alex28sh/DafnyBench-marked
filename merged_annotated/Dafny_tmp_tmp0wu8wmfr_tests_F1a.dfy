method F() returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r <= 0
  // post-conditions-end
{
// impl-start
  r := 0;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x := F();
  // assert-start
  assert x <= 0;
  // assert-end

  x := x - 1;
  // assert-start
  assert x <= -1;
  // assert-end

  print x;
// impl-end
}

method Mid(p: int, q: int) returns (m: int)
  // pre-conditions-start
  requires p <= q
  // pre-conditions-end
  // post-conditions-start
  ensures p <= m <= q
  ensures m - p <= q - m
  ensures 0 <= q - m - (m - p) <= 1
  // post-conditions-end
{
// impl-start
  m := (p + q) / 2;
  // assert-start
  assert m == p + (q - p) / 2;
  // assert-end

// impl-end
}
