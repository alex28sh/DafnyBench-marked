method SquareElements(a: array<int>) returns (squared: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures squared.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> squared[i] == a[i] * a[i]
  // post-conditions-end
{
// impl-start
  squared := new int[a.Length];
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant squared.Length == a.Length
    invariant forall k :: 0 <= k < i ==> squared[k] == a[k] * a[k]
    // invariants-end

  {
    squared[i] := a[i] * a[i];
  }
// impl-end
}
