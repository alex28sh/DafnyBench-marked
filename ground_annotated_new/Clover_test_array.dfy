method TestArrayElements(a: array<int>, j: nat)
  // pre-conditions-start
  requires 0 <= j < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
  // post-conditions-end
{
// impl-start
  a[j] := 60;
// impl-end
}
