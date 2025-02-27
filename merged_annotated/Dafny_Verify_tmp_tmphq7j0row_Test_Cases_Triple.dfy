method Triple(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var y := 2 * x;
  r := x + y;
  // assert-start
  assert r == 3 * x;
  // assert-end

// impl-end
}

method TripleIf(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if x == 0 {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
  // assert-start
  assert r == 3 * x;
  // assert-end

// impl-end
}

method TripleOver(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if {
    case x < 18 =>
      var a, b := 2 * x, 4 * x;
      r := (a + b) / 2;
    case 0 <= x =>
      var y := 2 * x;
      r := x + y;
  }
  // assert-start
  assert r == 3 * x;
  // assert-end

// impl-end
}

method TripleConditions(x: int) returns (r: int)
  // pre-conditions-start
  requires x % 2 == 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  var y := x / 2;
  r := 6 * y;
  // assert-start
  assert r == 3 * x;
  // assert-end

// impl-end
}

method Caller()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var t := TripleConditions(18);
  // assert-start
  assert t < 100;
  // assert-end

// impl-end
}
