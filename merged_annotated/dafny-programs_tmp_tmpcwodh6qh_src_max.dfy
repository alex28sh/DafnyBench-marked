method Max(a: int, b: int) returns (c: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
  // post-conditions-end
{
// impl-start
  if a > b {
    return a;
  } else {
    return b;
  }
// impl-end
}

method MaxTest()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var low := 1;
  var high := 10;
  var v := Max(low, high);
  // assert-start
  assert v == high;
  // assert-end

// impl-end
}

function max(a: int, b: int): int
{
  if a > b then
    a
  else
    b
}
// pure-end

method maxTest()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert max(1, 10) == 10;
  // assert-end

// impl-end
}
