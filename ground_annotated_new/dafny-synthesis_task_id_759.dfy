method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  ensures !result ==> !exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  // post-conditions-end
{
// impl-start
  result := false;
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
    // invariants-end

  {
    if s[i] == '.' && |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
// impl-end
}
