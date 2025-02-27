method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
  ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
  // post-conditions-end
{
// impl-start
  result := true;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result ==> forall k :: 0 <= k < i ==> a[k] == n
    // invariants-end

  {
    if a[i] != n {
      result := false;
      break;
    }
  }
// impl-end
}
