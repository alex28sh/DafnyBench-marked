method Add(x: int, y: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == x + y
  // post-conditions-end
{
// impl-start
  r := x;
  if y < 0 {
    var n := y;
    while n != 0
      // invariants-start

      invariant r == x + y - n && 0 <= -n
      // invariants-end

    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while n != 0
      // invariants-start

      invariant r == x + y - n && 0 <= n
      // invariants-end

    {
      r := r + 1;
      n := n - 1;
    }
  }
// impl-end
}

method Mul(x: int, y: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == x * y
  decreases x < 0, x
  // post-conditions-end
{
// impl-start
  if x == 0 {
    r := 0;
  } else if x < 0 {
    r := Mul(-x, y);
    r := -r;
  } else {
    r := Mul(x - 1, y);
    r := Add(r, y);
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
  TestAdd(3, 180);
  TestAdd(3, -180);
  TestAdd(0, 1);
  TestMul(3, 180);
  TestMul(3, -180);
  TestMul(180, 3);
  TestMul(-180, 3);
  TestMul(0, 1);
  TestMul(1, 0);
// impl-end
}

method TestAdd(x: int, y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  print x, " + ", y, " = ";
  var z := Add(x, y);
  print z, "\n";
// impl-end
}

method TestMul(x: int, y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  print x, " * ", y, " = ";
  var z := Mul(x, y);
  print z, "\n";
// impl-end
}
