function IsDigit(c: char): bool
{
  48 <= c as int <= 57
}
// pure-end

method IsInteger(s: string) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
  // post-conditions-end
{
// impl-start
  result := true;
  if |s| == 0 {
    result := false;
  } else {
    for i := 0 to |s|
      // invariants-start

      invariant 0 <= i <= |s|
      invariant result <==> forall k :: 0 <= k < i ==> IsDigit(s[k])
      // invariants-end

    {
      if !IsDigit(s[i]) {
        result := false;
        break;
      }
    }
  }
// impl-end
}
