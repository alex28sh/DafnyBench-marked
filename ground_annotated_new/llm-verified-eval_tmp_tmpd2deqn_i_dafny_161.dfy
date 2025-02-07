function IsLetter(c: char): bool
{
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}
// pure-end

function NoLetters(s: string, n: nat): bool
  requires n <= |s|
{
  forall c :: 
    0 <= c < n ==>
      !IsLetter(s[c])
}
// pure-end

function ToggleCase(c: char): char
{
  if c >= 'a' && c <= 'z' then
    c - 'a' + 'A'
  else if c >= 'A' && c <= 'Z' then
    c - 'A' + 'a'
  else
    c
}
// pure-end

function isReverse(s: string, s_prime: string): bool
{
  |s| == |s_prime| &&
  forall si :: 
    0 <= si < |s| / 2 ==>
      s_prime[|s| - si - 1] == s[si]
}
// pure-end

method Reverse(original: seq<char>) returns (reversed: seq<char>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |reversed| == |original|
  ensures forall i :: 0 <= i < |original| ==> reversed[i] == original[|original| - 1 - i]
  // post-conditions-end
{
// impl-start
  reversed := [];
  var i := |original|;
  while i > 0
    // invariants-start

    invariant 0 <= i <= |original|
    invariant |reversed| == |original| - i
    invariant forall j :: 0 <= j < |original| - i ==> reversed[j] == original[|original| - 1 - j]
    decreases i
    // invariants-end

  {
    i := i - 1;
    reversed := reversed + [original[i]];
  }
// impl-end
}

method solve(s: string) returns (result: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |s|
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && IsLetter(s[i]) ==> result[i] == ToggleCase(s[i])
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && !IsLetter(s[i]) ==> result[i] == s[i]
  ensures NoLetters(s, |s|) ==> isReverse(result, s)
  // post-conditions-end
{
// impl-start
  var flg: bool := false;
  result := "";
  for i := 0 to |s|
    // invariants-start

    invariant |result| == i
    invariant flg <==> !NoLetters(s, i)
    invariant forall j :: 0 <= j < i ==> result[j] == ToggleCase(s[j])
    // invariants-end

  {
    if IsLetter(s[i]) {
      result := result + [ToggleCase(s[i])];
      flg := true;
    } else {
      result := result + [s[i]];
    }
  }
  if !flg {
    result := Reverse(s);
  }
// impl-end
}
