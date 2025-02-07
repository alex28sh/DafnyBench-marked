method Max(a: int, b: int) returns (c: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c >= a && c >= b
  // post-conditions-end
{
// impl-start
  if a < b {
    c := b;
  } else {
    c := a;
  }
  // assert-start
  assert a <= c && b <= c;
  // assert-end

// impl-end
}

method Testing()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var v := Max(2, 3);
  // assert-start
  assert v >= 3;
  // assert-end

// impl-end
}
