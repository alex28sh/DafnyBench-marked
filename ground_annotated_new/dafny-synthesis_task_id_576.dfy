method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures true <== exists i :: 0 <= i <= |main| - |sub| && sub == main[i .. i + |sub|]
  // post-conditions-end
{
// impl-start
  if |sub| > |main| {
    return false;
  }
  for i := 0 to |main| - |sub| + 1
    // invariants-start

    invariant 0 <= i <= |main| - |sub| + 1
    invariant true <== exists j :: 0 <= j < i && sub == main[j .. j + |sub|]
    // invariants-end

  {
    if sub == main[i .. i + |sub|] {
      result := true;
    }
  }
  result := false;
// impl-end
}
