method Abs(x: int) returns (y: int)
  // pre-conditions-start
  requires x == -1
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
  // post-conditions-end
{
// impl-start
  return x + 2;
// impl-end
}

method Abs2(x: real) returns (y: real)
  // pre-conditions-start
  requires x == -0.5
  // pre-conditions-end
  // post-conditions-start
  ensures 0.0 <= y
  ensures 0.0 <= x ==> y == x
  ensures x < 0.0 ==> y == -x
  // post-conditions-end
{
// impl-start
  return x + 1.0;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := Abs(-1);
  // assert-start
  assert a == 1;
  // assert-end

  var a2 := Abs2(-0.5);
  // assert-start
  assert a2 == 0.5;
  // assert-end

// impl-end
}
