method LucidNumbers(n: int) returns (lucid: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
  ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
  ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
  // post-conditions-end
{
// impl-start
  lucid := [];
  var i := 0;
  while i <= n
    // invariants-start

    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] % 3 == 0
    invariant forall k :: 0 <= k < |lucid| ==> lucid[k] <= i - 1
    invariant forall k, l :: 0 <= k < l < |lucid| ==> lucid[k] < lucid[l]
    // invariants-end

  {
    if i % 3 == 0 {
      lucid := lucid + [i];
    }
    i := i + 1;
  }
// impl-end
}
