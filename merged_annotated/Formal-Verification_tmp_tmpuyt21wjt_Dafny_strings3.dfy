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
  if |pre| > |str| {
    return false;
  }
  var i := 0;
  while i < |pre|
    // invariants-start

    invariant 0 <= i <= |pre|
    invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
    decreases |pre| - i
    // invariants-end

  {
    if pre[i] != str[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
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
  // post-conditions-end
{
// impl-start
  if |sub| > |str| {
    return false;
  }
  var i := |str| - |sub|;
  while i >= 0
    // invariants-start

    invariant i >= -1
    invariant forall j :: i < j <= |str| - |sub| ==> !isPrefixPred(sub, str[j..])
    decreases i
    // invariants-end

  {
    var isPref := isPrefix(sub, str[i..]);
    if isPref {
      return true;
    }
    i := i - 1;
  }
  return false;
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
  // post-conditions-end
{
// impl-start
  if |str1| < k || |str2| < k {
    return false;
  }
  var i := |str1| - k;
  while i >= 0
    // invariants-start

    invariant i >= -1
    invariant forall j, t :: i < j <= |str1| - k && t == j + k ==> !isSubstringPred(str1[j .. t], str2)
    decreases i
    // invariants-end

  {
    var t := i + k;
    var isSub := isSubstring(str1[i .. t], str2);
    if isSub {
      return true;
    }
    i := i - 1;
  }
  return false;
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
  var i := |str1|;
  while i > 0
    // invariants-start

    invariant i >= 0
    invariant forall j :: i < j <= |str1| ==> !haveCommonKSubstringPred(j, str1, str2)
    decreases i
    // invariants-end

  {
    var ans := haveCommonKSubstring(i, str1, str2);
    if ans {
      return i;
    }
    i := i - 1;
  }
  // assert-start
  assert i == 0;
  // assert-end

  // assert-start
  assert isPrefixPred(str1[0 .. 0], str2[0..]);
  // assert-end

  return 0;
// impl-end
}
