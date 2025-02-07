function max(x: nat, y: nat): nat
{
  if x < y then
    y
  else
    x
}
// pure-end

method slow_max(a: nat, b: nat) returns (z: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures z == max(a, b)
  // post-conditions-end
{
// impl-start
  z := 0;
  var x := a;
  var y := b;
  while z < x && z < y
    // invariants-start

    invariant x >= 0
    invariant y >= 0
    invariant z == a - x && z == b - y
    invariant a - x == b - y
    decreases x, y
    // invariants-end

  {
    z := z + 1;
    x := x - 1;
    y := y - 1;
  }
  if x <= y {
    return b;
  } else {
    return a;
  }
// impl-end
}
