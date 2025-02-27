method CubeElements(a: array<int>) returns (cubed: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures cubed.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
  // post-conditions-end
{
// impl-start
  var cubedArray := new int[a.Length];
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant cubedArray.Length == a.Length
    invariant forall k :: 0 <= k < i ==> cubedArray[k] == a[k] * a[k] * a[k]
    // invariants-end

  {
    cubedArray[i] := a[i] * a[i] * a[i];
  }
  return cubedArray;
// impl-end
}
