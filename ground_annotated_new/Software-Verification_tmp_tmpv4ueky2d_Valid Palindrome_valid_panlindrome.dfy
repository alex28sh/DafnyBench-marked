method isPalindrome(s: array<char>) returns (result: bool)
  // pre-conditions-start
  requires 1 <= s.Length <= 200000
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> forall i :: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i]
  // post-conditions-end
{
// impl-start
  var length := s.Length;
  var i := 0;
  while i < length / 2
    // invariants-start

    invariant 0 <= i <= length
    invariant forall j :: 0 <= j < i ==> s[j] == s[length - 1 - j]
    // invariants-end

  {
    if s[i] != s[length - 1 - i] {
      return false;
    }
    i := i + 1;
  }
  return true;
// impl-end
}
