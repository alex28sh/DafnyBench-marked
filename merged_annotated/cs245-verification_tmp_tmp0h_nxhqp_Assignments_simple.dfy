method simple(y: int) returns (x: int)
  // pre-conditions-start
  requires y == 6
  // pre-conditions-end
  // post-conditions-start
  ensures x == 7
  // post-conditions-end
{
// impl-start
  // assert-start
  assert y + 1 == 7;
  // assert-end

  x := y + 1;
// impl-end
}
