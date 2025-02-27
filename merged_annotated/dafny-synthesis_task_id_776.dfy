function IsVowel(c: char): bool
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}
// pure-end

method CountVowelNeighbors(s: string) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
  // post-conditions-end
{
// impl-start
  var vowels := set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1]);
  count := |vowels|;
// impl-end
}
