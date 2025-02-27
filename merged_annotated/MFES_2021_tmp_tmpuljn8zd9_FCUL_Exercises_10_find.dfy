method find(a: array<int>, key: int) returns (index: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= index <= a.Length
  ensures index < a.Length ==> a[index] == key
  // post-conditions-end
{
// impl-start
  index := 0;
  while index < a.Length && a[index] != key
    // invariants-start

    invariant 0 <= index <= a.Length
    invariant forall x :: 0 <= x < index ==> a[x] != key
    decreases a.Length - index
    // invariants-end

  {
    index := index + 1;
  }
// impl-end
}
