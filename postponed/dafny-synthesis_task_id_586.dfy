method SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
  // pre-conditions-start
  requires n >= 0 && n < |l|
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
  // post-conditions-end
{
// impl-start
  var firstPart: seq<int> := l[..n];
  var secondPart: seq<int> := l[n..];
  r := secondPart + firstPart;
// impl-end
}
