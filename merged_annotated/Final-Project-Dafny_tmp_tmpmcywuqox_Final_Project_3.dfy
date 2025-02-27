method nonZeroReturn(x: int) returns (y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y != 0
  // post-conditions-end
{
// impl-start
  if x == 0 {
    return x + 1;
  } else {
    return -x;
  }
// impl-end
}

method test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var input := nonZeroReturn(-1);
  // assert-start
  assert input != 0;
  // assert-end

// impl-end
}
