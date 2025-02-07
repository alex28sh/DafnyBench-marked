method Find(a: array<int>, key: int) returns (index: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= index < a.Length
  ensures index != -1 ==> a[index] == key && forall i :: 0 <= i < index ==> a[i] != key
  ensures index == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
  // post-conditions-end
{
// impl-start
  index := 0;
  while index < a.Length
    // invariants-start

    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] != key
    // invariants-end

  {
    if a[index] == key {
      return;
    }
    index := index + 1;
  }
  if index >= a.Length {
    index := -1;
  }
// impl-end
}
