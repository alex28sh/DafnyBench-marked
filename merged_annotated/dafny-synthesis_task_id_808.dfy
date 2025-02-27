method ContainsK(s: seq<int>, k: int) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> k in s
  // post-conditions-end
{
// impl-start
  result := false;
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
    // invariants-end

  {
    if s[i] == k {
      result := true;
      break;
    }
  }
// impl-end
}
