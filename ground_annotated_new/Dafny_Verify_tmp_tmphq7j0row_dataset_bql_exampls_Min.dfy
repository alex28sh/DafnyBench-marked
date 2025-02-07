method min(a: array<int>, n: int) returns (min: int)
  // pre-conditions-start
  requires 0 < n <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures exists i: int :: 0 <= i && i < n && a[i] == min
  ensures forall i: int :: 0 <= i && i < n ==> a[i] >= min
  // post-conditions-end
{
// impl-start
  var i: int;
  min := a[0];
  i := 1;
  while i < n
    // invariants-start

    invariant i <= n
    invariant exists j: int :: 0 <= j && j < i && a[j] == min
    invariant forall j: int :: 0 <= j && j < i ==> a[j] >= min
    // invariants-end

  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
// impl-end
}
