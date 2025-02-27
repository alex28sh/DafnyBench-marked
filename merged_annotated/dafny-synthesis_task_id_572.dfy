method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // post-conditions-end
{
// impl-start
  var res: seq<int> := [];
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: x in res <==> exists k :: 0 <= k < i && a[k] == x
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
    // invariants-end

  {
    if a[i] !in res {
      res := res + [a[i]];
    }
  }
  result := res;
// impl-end
}
