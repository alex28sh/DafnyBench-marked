// dafny-aoc-2019_tmp_tmpj6suy_rv_parser_split.dfy


module Split {
  function splitHelper(s: string, separator: string, index: nat, sindex: nat, results: seq<string>): seq<seq<char>>
    requires index <= |s|
    requires sindex <= |s|
    requires sindex <= index
    decreases |s| - index
  {
    if index >= |s| then
      results + [s[sindex .. index]]
    else if |separator| == 0 && index == |s| - 1 then
      splitHelper(s, separator, index + 1, index, results)
    else if |separator| == 0 then
      assert separator == [];
      assert s[sindex .. index + 1] != [];
      splitHelper(s, separator, index + 1, index + 1, results + [s[sindex .. index + 1]])
    else if index + |separator| > |s| then
      splitHelper(s, separator, |s|, sindex, results)
    else if s[index .. index + |separator|] == separator then
      splitHelper(s, separator, index + |separator|, index + |separator|, results + [s[sindex .. index]])
    else
      splitHelper(s, separator, index + 1, sindex, results)
  }
  // pure-end

  function split(s: string, separator: string): seq<string>
    ensures split(s, separator) == splitHelper(s, separator, 0, 0, [])
  {
    splitHelper(s, separator, 0, 0, [])
  }
  // pure-end

  predicate Contains(haystack: string, needle: string)
    ensures Contains(haystack, needle) <==> exists k :: 0 <= k <= |haystack| && needle <= haystack[k..]
    ensures Contains(haystack, needle) <==> exists i :: 0 <= i <= |haystack| && needle <= haystack[i..]
    ensures !Contains(haystack, needle) <==> forall i :: 0 <= i <= |haystack| ==> !(needle <= haystack[i..])
  {
    if needle <= haystack then
      assert haystack[0..] == haystack;
      true
    else if |haystack| > 0 then
      assert forall i :: 1 <= i <= |haystack| ==> haystack[i..] == haystack[1..][i - 1..];
      Contains(haystack[1..], needle)
    else
      false
  }
  // pure-end

  function splitOnBreak(s: string): seq<string>
  {
    if Contains(s, "\r\n") then
      split(s, "\r\n")
    else
      split(s, "\n")
  }
  // pure-end

  function splitOnDoubleBreak(s: string): seq<string>
  {
    if Contains(s, "\r\n") then
      split(s, "\r\n\r\n")
    else
      split(s, "\n\n")
  }
  // pure-end
}
