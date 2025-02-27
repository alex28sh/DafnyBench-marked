method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
  // pre-conditions-start
  requires |a| == |b|
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
  // post-conditions-end
{
// impl-start
  result := [];
  var i := 0;
  while i < |a|
    // invariants-start

    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] ^ b[k]
    // invariants-end

  {
    result := result + [a[i] ^ b[i]];
    i := i + 1;
  }
// impl-end
}
