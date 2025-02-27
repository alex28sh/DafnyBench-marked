method Abs(x: int) returns (y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
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

method TestingAbs()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var w := Abs(4);
  // assert-start
  assert w >= 0;
  // assert-end

  var v := Abs(3);
  // assert-start
  assert 0 <= v;
  // assert-end

// impl-end
}

method TestingAbs2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var v := Abs(3);
  // assert-start
  assert 0 <= v;
  // assert-end

  // assert-start
  assert v == 3;
  // assert-end

// impl-end
}

method Max(a: int, b: int) returns (c: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c >= a
  ensures c >= b
  // post-conditions-end
{
// impl-start
  c := a;
  if b > c {
    c := b;
  }
// impl-end
}

method TestingMax()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := 3;
  var b := 2;
  var c := Max(a, b);
  // assert-start
  assert c >= a;
  // assert-end

  // assert-start
  assert c >= b;
  // assert-end

// impl-end
}
