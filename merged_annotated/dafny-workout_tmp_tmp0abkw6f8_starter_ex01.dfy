method Max(a: int, b: int) returns (c: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c >= a && c >= b && (c == a || c == b)
  // post-conditions-end
{
// impl-start
  if a >= b {
    return a;
  } else {
    return b;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  print "Testing max...\n";
  var max := Max(3, 4);
  // assert-start
  assert max == 4;
  // assert-end

  max := Max(-3, 4);
  // assert-start
  assert max == 4;
  // assert-end

  max := Max(-3, -4);
  // assert-start
  assert max == -3;
  // assert-end

  max := Max(5555555, 5555);
  // assert-start
  assert max == 5555555;
  // assert-end

// impl-end
}
