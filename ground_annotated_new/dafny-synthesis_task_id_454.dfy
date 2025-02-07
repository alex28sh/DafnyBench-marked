method ContainsZ(s: string) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
  // post-conditions-end
{
// impl-start
  result := false;
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
    // invariants-end

  {
    if s[i] == 'z' || s[i] == 'Z' {
      result := true;
      break;
    }
  }
// impl-end
}
