method max(a: array<int>) returns (x: int)
  // pre-conditions-start
  requires a.Length != 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
  // post-conditions-end
{
// impl-start
  x := 0;
  var y := a.Length - 1;
  ghost var m := y;
  while x != y
    // invariants-start

    invariant 0 <= x <= y < a.Length
    invariant m == x || m == y
    invariant forall i :: 0 <= i < x ==> a[i] <= a[m]
    invariant forall i :: y < i < a.Length ==> a[i] <= a[m]
    // invariants-end

  {
    if a[x] <= a[y] {
      x := x + 1;
      m := y;
    } else {
      y := y - 1;
      m := x;
    }
  }
  return x;
// impl-end
}
