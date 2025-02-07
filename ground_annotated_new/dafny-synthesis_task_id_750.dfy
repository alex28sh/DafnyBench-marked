method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |l| + 1
  ensures r[|r| - 1] == t
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
  // post-conditions-end
{
// impl-start
  r := l + [t];
// impl-end
}
