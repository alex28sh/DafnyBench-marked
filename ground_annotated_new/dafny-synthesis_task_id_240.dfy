method ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |first| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |first| - 1 + |second|
  ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
  ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
  // post-conditions-end
{
// impl-start
  result := first[0 .. |first| - 1] + second;
// impl-end
}
