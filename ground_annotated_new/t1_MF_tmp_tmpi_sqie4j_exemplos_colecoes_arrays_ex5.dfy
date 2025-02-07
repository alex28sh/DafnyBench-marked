method Busca<T(==)>(a: array<T>, x: T) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= r ==> r < a.Length && a[r] == x
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
  // post-conditions-end
{
// impl-start
  r := 0;
  while r < a.Length
    // invariants-start

    invariant 0 <= r <= a.Length
    invariant forall i :: 0 <= i < r ==> a[i] != x
    // invariants-end

  {
    if a[r] == x {
      return;
    }
    r := r + 1;
  }
  r := -1;
// impl-end
}
