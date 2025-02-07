method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
  // pre-conditions-start
  requires a != null && a.Length > 0
  requires forall x, y :: cmp.requires(x, y)
  requires forall x, y :: cmp(x, y) || cmp(y, x)
  requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z)
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: 0 <= x < a.Length ==> cmp(a[x], max)
  // post-conditions-end
{
// impl-start
  max := a[0];
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> cmp(a[x], max)
    // invariants-end

  {
    if !cmp(a[i], max) {
      max := a[i];
    }
    i := i + 1;
  }
// impl-end
}
