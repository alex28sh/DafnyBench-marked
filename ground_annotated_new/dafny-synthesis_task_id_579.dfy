function InArray(a: array<int>, x: int): bool
  reads a
{
  exists i :: 
    0 <= i < a.Length &&
    a[i] == x
}
// pure-end

method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: x in result ==> InArray(a, x) != InArray(b, x)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // post-conditions-end
{
// impl-start
  var res: seq<int> := [];
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: x in res ==> InArray(a, x)
    invariant forall x :: x in res ==> InArray(a, x) != InArray(b, x)
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
    // invariants-end

  {
    if !InArray(b, a[i]) && a[i] !in res {
      res := res + [a[i]];
    }
  }
  ghost var partialSize := |res|;
  for i := 0 to b.Length
    // invariants-start

    invariant 0 <= i <= b.Length
    invariant forall k :: partialSize <= k < |res| ==> InArray(b, res[k])
    invariant forall k :: 0 <= k < |res| ==> InArray(a, res[k]) != InArray(b, res[k])
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
    // invariants-end

  {
    if !InArray(a, b[i]) && b[i] !in res {
      res := res + [b[i]];
    }
  }
  result := res;
// impl-end
}
