function Average(a: int, b: int): int
{
  (a + b) / 2
}
// pure-end

ghost method Triple(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  r := Average(2 * x, 4 * x);
// impl-end
}

method Triple1(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  var y := 2 * x;
  r := x + y;
  ghost var a, b := DoubleQuadruple(x);
  // assert-start
  assert a <= r <= b || b <= r <= a;
  // assert-end

// impl-end
}

ghost method DoubleQuadruple(x: int) returns (a: int, b: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == 2 * x && b == 4 * x
  // post-conditions-end
{
// impl-start
  a := 2 * x;
  b := 2 * a;
// impl-end
}

function F(): int
{
  29
}
// pure-end

method M() returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 29
  // post-conditions-end
{
// impl-start
  r := 29;
// impl-end
}

method Caller()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := F();
  var b := M();
  // assert-start
  assert a == 29;
  // assert-end

  // assert-start
  assert b == 29;
  // assert-end

// impl-end
}

method MyMethod(x: int) returns (y: int)
  // pre-conditions-start
  requires 10 <= x
  // pre-conditions-end
  // post-conditions-start
  ensures 25 <= y
  // post-conditions-end
{
// impl-start
  var a, b;
  a := x + 3;
  if x < 20 {
    b := 32 - x;
  } else {
    b := 16;
  }
  y := a + b;
// impl-end
}
