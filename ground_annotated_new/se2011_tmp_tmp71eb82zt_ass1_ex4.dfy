method Eval(x: int) returns (r: int)
  // pre-conditions-start
  requires x >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == x * x
  // post-conditions-end
{
// impl-start
  var y: int := x;
  var z: int := 0;
  while y > 0
    // invariants-start

    invariant 0 <= y <= x && z == x * (x - y)
    decreases y
    // invariants-end

  {
    z := z + x;
    y := y - 1;
  }
  return z;
// impl-end
}
