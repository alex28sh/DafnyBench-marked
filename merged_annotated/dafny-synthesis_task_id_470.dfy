method PairwiseAddition(a: array<int>) returns (result: array<int>)
  // pre-conditions-start
  requires a != null
  requires a.Length % 2 == 0
  // pre-conditions-end
  // post-conditions-start
  ensures result != null
  ensures result.Length == a.Length / 2
  ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2 * i] + a[2 * i + 1]
  // post-conditions-end
{
// impl-start
  result := new int[a.Length / 2];
  var i := 0;
  while i < a.Length / 2
    // invariants-start

    invariant 0 <= i <= a.Length / 2
    invariant result.Length == a.Length / 2
    invariant forall k :: 0 <= k < i ==> result[k] == a[2 * k] + a[2 * k + 1]
    // invariants-end

  {
    result[i] := a[2 * i] + a[2 * i + 1];
    i := i + 1;
  }
// impl-end
}
