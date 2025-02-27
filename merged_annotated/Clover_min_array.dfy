method minArray(a: array<int>) returns (r: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
  // post-conditions-end
{
// impl-start
  r := a[0];
  var i := 1;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> r <= a[x]
    invariant exists x :: 0 <= x < i && r == a[x]
    // invariants-end

  {
    if r > a[i] {
      r := a[i];
    }
    i := i + 1;
  }
// impl-end
}
