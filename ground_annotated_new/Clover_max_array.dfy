method maxArray(a: array<int>) returns (m: int)
  // pre-conditions-start
  requires a.Length >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
  // post-conditions-end
{
// impl-start
  m := a[0];
  var index := 1;
  while index < a.Length
    // invariants-start

    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> m >= a[k]
    invariant exists k :: 0 <= k < index && m == a[k]
    decreases a.Length - index
    // invariants-end

  {
    m := if m > a[index] then m else a[index];
    index := index + 1;
  }
// impl-end
}
