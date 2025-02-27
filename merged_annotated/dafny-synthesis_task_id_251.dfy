method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |v| == 2 * |s|
  ensures forall i :: 0 <= i < |s| ==> v[2 * i] == x && v[2 * i + 1] == s[i]
  // post-conditions-end
{
// impl-start
  v := [];
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant |v| == 2 * i
    invariant forall j :: 0 <= j < i ==> v[2 * j] == x && v[2 * j + 1] == s[j]
    // invariants-end

  {
    v := v + [x, s[i]];
  }
// impl-end
}
