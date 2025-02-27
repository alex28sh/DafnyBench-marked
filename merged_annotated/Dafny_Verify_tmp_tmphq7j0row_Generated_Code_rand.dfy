method Main(xInit: int, y: int) returns (z: int)
  // pre-conditions-start
  requires xInit >= 0
  requires y >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures z == 0
  // post-conditions-end
{
// impl-start
  var x := xInit;
  z := x * y;
  while x > 0
    // invariants-start

    invariant x >= 0
    invariant z == x * y
    decreases x
    // invariants-end

  {
    x := x - 1;
    z := z - y;
  }
// impl-end
}
