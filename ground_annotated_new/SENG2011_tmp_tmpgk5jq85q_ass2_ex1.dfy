method StringSwap(s: string, i: nat, j: nat)
    returns (t: string)
  // pre-conditions-start
  requires i >= 0 && j >= 0 && |s| >= 0
  requires |s| > 0 ==> i < |s| && j < |s|
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(s[..]) == multiset(t[..])
  ensures |s| == |t|
  ensures |s| > 0 ==> forall k: nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
  ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i]
  ensures |s| == 0 ==> t == s
  // post-conditions-end
{
// impl-start
  t := s;
  if |s| == 0 {
    return t;
  }
  t := t[i := s[j]];
  t := t[j := s[i]];
// impl-end
}

method check()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: string := "1scow2";
  var b: string := StringSwap(a, 1, 5);
  // assert-start
  assert b == "12cows";
  // assert-end

  var c: string := "";
  var d: string := StringSwap(c, 1, 2);
  // assert-start
  assert c == d;
  // assert-end

// impl-end
}
