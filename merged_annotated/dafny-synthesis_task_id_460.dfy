method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |lst|
  ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
  // post-conditions-end
{
// impl-start
  result := [];
  for i := 0 to |lst|
    // invariants-start

    invariant 0 <= i <= |lst|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == lst[j][0]
    // invariants-end

  {
    result := result + [lst[i][0]];
  }
// impl-end
}
