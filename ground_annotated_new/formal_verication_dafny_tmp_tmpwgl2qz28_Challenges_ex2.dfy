method Forbid42(x: int, y: int) returns (z: int)
  // pre-conditions-start
  requires y != 42
  // pre-conditions-end
  // post-conditions-start
  ensures z == x / (42 - y)
  // post-conditions-end
{
// impl-start
  z := x / (42 - y);
  return z;
// impl-end
}

method Allow42(x: int, y: int)
    returns (z: int, err: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y != 42 ==> z == x / (42 - y) && err == false
  ensures y == 42 ==> z == 0 && err == true
  // post-conditions-end
{
// impl-start
  if y != 42 {
    z := x / (42 - y);
    return z, false;
  }
  return 0, true;
// impl-end
}

method TEST1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var c: int := Forbid42(0, 1);
  // assert-start
  assert c == 0;
  // assert-end

  c := Forbid42(10, 32);
  // assert-start
  assert c == 1;
  // assert-end

  c := Forbid42(-100, 38);
  // assert-start
  assert c == -25;
  // assert-end

  var d: int, z: bool := Allow42(0, 42);
  // assert-start
  assert d == 0 && z == true;
  // assert-end

  d, z := Allow42(-10, 42);
  // assert-start
  assert d == 0 && z == true;
  // assert-end

  d, z := Allow42(0, 1);
  // assert-start
  assert d == 0 && z == false;
  // assert-end

  d, z := Allow42(10, 32);
  // assert-start
  assert d == 1 && z == false;
  // assert-end

  d, z := Allow42(-100, 38);
  // assert-start
  assert d == -25 && z == false;
  // assert-end

// impl-end
}
