method Mult(x: nat, y: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == x * y
  // post-conditions-end
{
// impl-start
  var m := x;
  var n := y;
  r := 0;
  while m > 0
    // invariants-start

    invariant m * n + r == x * y
    invariant m >= 0
    // invariants-end

  {
    r := r + n;
    m := m - 1;
  }
  return r;
// impl-end
}
