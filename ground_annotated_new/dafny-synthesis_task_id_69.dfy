method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> exists i :: 0 <= i < |list| && sub == list[i]
  // post-conditions-end
{
// impl-start
  result := false;
  for i := 0 to |list|
    // invariants-start

    invariant 0 <= i <= |list|
    invariant result <==> exists k :: 0 <= k < i && sub == list[k]
    // invariants-end

  {
    if sub == list[i] {
      result := true;
      break;
    }
  }
// impl-end
}
