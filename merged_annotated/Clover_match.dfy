method Match(s: string, p: string) returns (b: bool)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
    // invariants-end

  {
    if s[i] != p[i] && p[i] != '?' {
      return false;
    }
    i := i + 1;
  }
  return true;
// impl-end
}
