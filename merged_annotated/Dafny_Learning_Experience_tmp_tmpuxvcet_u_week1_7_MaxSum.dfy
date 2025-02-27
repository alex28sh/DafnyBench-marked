method MaxSum(x: int, y: int)
    returns (s: int, m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
  // post-conditions-end
{
// impl-start
  s := x + y;
  if x > y {
    m := x;
  } else if y > x {
    m := y;
  } else {
    m := x;
  }
  // assert-start
  assert m >= y;
  // assert-end

// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var m, n := 4, 5;
  var a, b := MaxSum(m, n);
  print "Search return a is ", a, ",,,,, b is ", b, "\n";
// impl-end
}
