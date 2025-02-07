method max(a: int, b: int) returns (z: int)
  // pre-conditions-start
  requires true
  // pre-conditions-end
  // post-conditions-start
  ensures z >= a || z >= b
  // post-conditions-end
{
// impl-start
  if a > b {
    z := a;
  } else {
    z := b;
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
  var x;
  // assert-start
  assert true;
  // assert-end

  x := max(23, 50);
  // assert-start
  assert x >= 50 || x >= 23;
  // assert-end

// impl-end
}

method mystery1(n: nat, m: nat) returns (res: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures n + m == res
  // post-conditions-end
{
// impl-start
  if n == 0 {
    return m;
  } else {
    var aux := mystery1(n - 1, m);
    return 1 + aux;
  }
// impl-end
}

method mystery2(n: nat, m: nat) returns (res: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures n * m == res
  // post-conditions-end
{
// impl-start
  if n == 0 {
    return 0;
  } else {
    var aux := mystery2(n - 1, m);
    var aux2 := mystery1(m, aux);
    return aux2;
  }
// impl-end
}

method m1(x: int, y: int) returns (z: int)
  // pre-conditions-start
  requires 0 < x < y
  // pre-conditions-end
  // post-conditions-start
  ensures z >= 0 && z < y && z != x
  // post-conditions-end
{
// impl-start
  if x > 0 && y > 0 && y > x {
    z := x - 1;
  }
// impl-end
}

method m2(x: nat) returns (y: int)
  // pre-conditions-start
  requires x <= -1
  // pre-conditions-end
  // post-conditions-start
  ensures y > x && y < x
  // post-conditions-end
{
// impl-start
  if x <= -1 {
    y := x + 1;
  }
// impl-end
}

method m3(x: int, y: int) returns (z: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures z ==> x == y
  // post-conditions-end
{
// impl-start
  if x == y {
    z := true;
  } else {
    z := false;
  }
// impl-end
}

method m4(x: int, y: int) returns (z: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures z ==> x == y && x == y ==> z
  // post-conditions-end
{
// impl-start
  if x == y {
    z := true;
  } else {
    z := false;
  }
// impl-end
}
