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
  if |str| < |pre| {
    return false;
  } else if pre[..] == str[..|pre|] {
    return true;
  } else {
    return false;
  }
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
  var i := 0;
  res := false;
  while i <= |str|
    // invariants-start

    invariant 0 <= i <= |str| + 1
    invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
    decreases |str| - i
    // invariants-end

  {
    var temp := isPrefix(sub, str[i..]);
    if temp == true {
      return true;
    }
    i := i + 1;
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
  if k > |str1| || k > |str2| {
    return false;
  }
  var i := 0;
  var temp := false;
  while i <= |str1| - k
    // invariants-start

    invariant 0 <= i <= |str1| - k + 1
    invariant temp ==> 0 <= i <= |str1| - k && isSubstringPred(str1[i .. i + k], str2)
    invariant !temp ==> forall m, n :: 0 <= m < i && n == m + k ==> isNotSubstringPred(str1[m .. n], str2)
    decreases |str1| - k - i
    // invariants-end

  {
    temp := isSubstring(str1[i .. i + k], str2);
    if temp == true {
      return true;
    }
    i := i + 1;
  }
  return false;
// impl-end
}

lemma haveCommon0SubstringLemma(str1: string, str2: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures haveCommonKSubstringPred(0, str1, str2)
  // post-conditions-end
{
// impl-start
  assert isPrefixPred(str1[0 .. 0], str2[0..]);
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
  var temp := false;
  var i := |str1| + 1;
  len := i;
  while i > 0
    // invariants-start

    invariant 0 <= i <= |str1| + 1
    invariant temp ==> haveCommonKSubstringPred(i, str1, str2)
    invariant !temp ==> haveNotCommonKSubstringPred(i, str1, str2)
    invariant !temp ==> forall k :: i <= k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
    invariant temp ==> forall k :: i < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
    decreases i
    // invariants-end

  {
    i := i - 1;
    len := i;
    temp := haveCommonKSubstring(i, str1, str2);
    if temp == true {
      break;
    }
  }
  // assert-start
  haveCommon0SubstringLemma(str1, str2);
  // assert-end

  return len;
// impl-end
}
