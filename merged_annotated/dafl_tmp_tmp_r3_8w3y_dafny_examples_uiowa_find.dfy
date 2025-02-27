method Find(a: array<int>, key: int) returns (i: int)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i ==> i < a.Length && a[i] == key && forall k :: 0 <= k < i ==> a[k] != key
  ensures i < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  // post-conditions-end
{
// impl-start
  i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != key
    decreases a.Length - i
    // invariants-end

  {
    if a[i] == key {
      return;
    }
    i := i + 1;
  }
  i := -1;
// impl-end
}
