method Abs(x: int) returns (y: int)
  // pre-conditions-start
  requires x < 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 < y
  ensures y == -x
  // post-conditions-end
{
// impl-start
  return -x;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := Abs(-3);
  // assert-start
  assert a == 3;
  // assert-end

// impl-end
}
