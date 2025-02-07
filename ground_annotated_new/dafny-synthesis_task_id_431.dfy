method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
  // pre-conditions-start
  requires a != null && b != null
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
  ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
  // post-conditions-end
{
// impl-start
  result := false;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant !result ==> forall k, j :: 0 <= k < i && 0 <= j < b.Length ==> a[k] != b[j]
    // invariants-end

  {
    for j := 0 to b.Length
      // invariants-start

      invariant 0 <= j <= b.Length
      invariant !result ==> forall k :: 0 <= k < j ==> a[i] != b[k]
      // invariants-end

    {
      if a[i] == b[j] {
        result := true;
        return;
      }
    }
  }
// impl-end
}
