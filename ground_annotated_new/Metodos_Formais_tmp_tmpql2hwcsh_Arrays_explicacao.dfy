method buscar(a: array<int>, x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
  ensures 0 <= r < a.Length ==> a[r] == x
  // post-conditions-end
{
// impl-start
  r := 0;
  while r < a.Length
    // invariants-start

    invariant 0 <= r <= a.Length
    invariant forall i :: 0 <= i < r ==> a[i] != x
    decreases a.Length - r
    // invariants-end

  {
    if a[r] == x {
      return r;
    }
    r := r + 1;
  }
  return -1;
// impl-end
}
