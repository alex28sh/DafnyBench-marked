function abs(x: int): int
{
  if x < 0 then
    -x
  else
    x
}
// pure-end

method Testing_abs()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var v := abs(3);
  // assert-start
  assert v == 3;
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

method Testing_max()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert max(3, 4) == 4;
  // assert-end

  // assert-start
  assert max(-1, -4) == -1;
  // assert-end

// impl-end
}

method Abs(x: int) returns (y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures abs(x) == y
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

function Double(val: int): int
{
  2 * val
}
// pure-end

method TestDouble(val: int) returns (val2: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures val2 == Double(val)
  // post-conditions-end
{
// impl-start
  val2 := 2 * val;
// impl-end
}
