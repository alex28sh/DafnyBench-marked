method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
  // pre-conditions-start
  requires a != null && b != null
  requires a.Length == b.Length
  requires forall i :: 0 <= i < b.Length ==> b[i] != 0
  // pre-conditions-end
  // post-conditions-start
  ensures result != null
  ensures result.Length == a.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
  // post-conditions-end
{
// impl-start
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] % b[k]
    // invariants-end

  {
    result[i] := a[i] % b[i];
    i := i + 1;
  }
// impl-end
}
