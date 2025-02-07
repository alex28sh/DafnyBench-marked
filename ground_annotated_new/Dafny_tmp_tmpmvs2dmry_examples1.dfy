method Abs(x: int) returns (y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y >= 0
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> -x == y
  ensures y == abs(x)
  // post-conditions-end
{
// impl-start
  if x < 0 {
    return -x;
  } else {
    return x;
  }
// impl-end
}

function abs(x: int): int
{
  if x > 0 then
    x
  else
    -x
}
// pure-end

method Testing()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var v := Abs(-3);
  // assert-start
  assert v >= 0;
  // assert-end

  // assert-start
  assert v == 3;
  // assert-end

// impl-end
}

method MultiReturn(x: int, y: int)
    returns (more: int, less: int)
  // pre-conditions-start
  requires y >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures less <= x <= more
  // post-conditions-end
{
// impl-start
  more := x + y;
  less := x - y;
// impl-end
}

method Max(x: int, y: int) returns (a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == x || a == y
  ensures x > y ==> a == x
  ensures x <= y ==> a == y
  // post-conditions-end
{
// impl-start
  if x > y {
    a := x;
  } else {
    a := y;
  }
// impl-end
}
