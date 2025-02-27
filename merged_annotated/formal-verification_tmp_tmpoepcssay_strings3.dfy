function isPrefixPred(pre: string, str: string): bool
{
  |pre| <= |str| &&
  pre == str[..|pre|]
}
// pure-end

function isNotPrefixPred(pre: string, str: string): bool
{
  |pre| > |str| || pre != str[..|pre|]
}
// pure-end

lemma PrefixNegationLemma(pre: string, str: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
  ensures !isPrefixPred(pre, str) <==> isNotPrefixPred(pre, str)
  // post-conditions-end
{
// impl-start
// impl-end
}

method isPrefix(pre: string, str: string) returns (res: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !res <==> isNotPrefixPred(pre, str)
  ensures res <==> isPrefixPred(pre, str)
  // post-conditions-end
{
// impl-start
  return |pre| <= |str| && forall i :: 0 <= i < |pre| ==> pre[i] == str[i];
// impl-end
}

function isSubstringPred(sub: string, str: string): bool
{
  exists i :: 
    0 <= i <= |str| &&
    isPrefixPred(sub, str[i..])
}
// pure-end

function isNotSubstringPred(sub: string, str: string): bool
{
  forall i :: 
    0 <= i <= |str| ==>
      isNotPrefixPred(sub, str[i..])
}
// pure-end

lemma SubstringNegationLemma(sub: string, str: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
  ensures !isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str)
  // post-conditions-end
{
// impl-start
// impl-end
}

method isSubstring(sub: string, str: string) returns (res: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res <==> isSubstringPred(sub, str)
  ensures res ==> isSubstringPred(sub, str)
  ensures isSubstringPred(sub, str) ==> res
  ensures isSubstringPred(sub, str) ==> res
  ensures !res <==> isNotSubstringPred(sub, str)
  // post-conditions-end
{
// impl-start
  if |str| < |sub| {
    return false;
  } else {
    var i: nat := 0;
    res := false;
    while i <= |str| - |sub| && res == false
      // invariants-start

      invariant 0 <= i <= |str| - |sub| + 1
      invariant res ==> isSubstringPred(sub, str)
      invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
      decreases |str| - |sub| - i + if !res then 1 else 0
      // invariants-end

    {
      res := isPrefix(sub, str[i..]);
      if !res {
        i := i + 1;
      }
    }
  }
// impl-end
}

function haveCommonKSubstringPred(k: nat, str1: string, str2: string): bool
{
  exists i1, j1 :: 
    0 <= i1 <= |str1| - k &&
    j1 == i1 + k &&
    isSubstringPred(str1[i1 .. j1], str2)
}
// pure-end

function haveNotCommonKSubstringPred(k: nat, str1: string, str2: string): bool
{
  forall i1, j1 :: 
    0 <= i1 <= |str1| - k &&
    j1 == i1 + k ==>
      isNotSubstringPred(str1[i1 .. j1], str2)
}
// pure-end

lemma commonKSubstringLemma(k: nat, str1: string, str2: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
  ensures !haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2)
  // post-conditions-end
{
// impl-start
// impl-end
}

method haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures found <==> haveCommonKSubstringPred(k, str1, str2)
  ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
  // post-conditions-end
{
// impl-start
  if k <= |str1| && k <= |str2| {
    var slice: string;
    found := false;
    var i: nat := 0;
    while i <= |str1| - k && found == false
      // invariants-start

      invariant found ==> haveCommonKSubstringPred(k, str1, str2)
      invariant forall x, y :: 0 <= x < i && found == false && y == x + k && y <= |str1| ==> isNotSubstringPred(str1[x .. y], str2)
      decreases |str1| - k - i + if !found then 1 else 0
      // invariants-end

    {
      slice := str1[i .. i + k];
      found := isSubstring(slice, str2);
      i := i + 1;
    }
  } else {
    return false;
  }
// impl-end
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  // pre-conditions-start
  requires |str1| <= |str2|
  // pre-conditions-end
  // post-conditions-start
  ensures forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
  ensures haveCommonKSubstringPred(len, str1, str2)
  // post-conditions-end
{
// impl-start
  // assert-start
  assert isPrefixPred(str1[0 .. 0], str2[0..]);
  // assert-end

  len := |str1|;
  var hasCommon: bool := true;
  while len > 0
    // invariants-start

    invariant forall i :: len < i <= |str1| ==> !haveCommonKSubstringPred(i, str1, str2)
    decreases len
    // invariants-end

  {
    hasCommon := haveCommonKSubstring(len, str1, str2);
    if hasCommon {
      return len;
    }
    len := len - 1;
  }
  return len;
// impl-end
}
