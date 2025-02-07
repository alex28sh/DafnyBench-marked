method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
  ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
  // post-conditions-end
{
// impl-start
  if a.Length == 0 {
    return true;
  }
  var firstElement := a[0];
  result := true;
  for i := 1 to a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant result ==> forall k :: 0 <= k < i ==> a[k] == firstElement
    // invariants-end

  {
    if a[i] != firstElement {
      result := false;
      break;
    }
  }
// impl-end
}
