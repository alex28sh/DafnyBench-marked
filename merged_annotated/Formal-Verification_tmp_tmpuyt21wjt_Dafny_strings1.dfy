function isPrefixPredicate(pre: string, str: string): bool
{
  |str| >= |pre| &&
  pre <= str
}
// pure-end

method isPrefix(pre: string, str: string) returns (res: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
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

function isSubstringPredicate(sub: string, str: string): bool
{
  |str| >= |sub| &&
  exists i :: 
    0 <= i <= |str| &&
    isPrefixPredicate(sub, str[i..])
}
// pure-end

method isSubstring(sub: string, str: string) returns (res: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res == isSubstringPredicate(sub, str)
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
    invariant forall j :: i < j <= |str| - |sub| ==> !isPrefixPredicate(sub, str[j..])
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

function haveCommonKSubstringPredicate(k: nat, str1: string, str2: string): bool
{
  |str1| >= k &&
  |str2| >= k &&
  exists i :: 
    0 <= i <= |str1| - k &&
    isSubstringPredicate(str1[i..][..k], str2)
}
// pure-end

method haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k, str1, str2) == found
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
    invariant forall j :: i < j <= |str1| - k ==> !isSubstringPredicate(str1[j..][..k], str2)
    decreases i
    // invariants-end

  {
    var isSub := isSubstring(str1[i..][..k], str2);
    if isSub {
      return true;
    }
    i := i - 1;
  }
  return false;
// impl-end
}

function maxCommonSubstringPredicate(str1: string, str2: string, len: nat): bool
{
  forall k :: 
    len < k <= |str1| ==>
      !haveCommonKSubstringPredicate(k, str1, str2)
}
// pure-end

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures len <= |str1| && len <= |str2|
  ensures len >= 0
  ensures maxCommonSubstringPredicate(str1, str2, len)
  // post-conditions-end
{
// impl-start
  var i := |str1|;
  while i > 0
    // invariants-start

    invariant i >= 0
    invariant forall j :: i < j <= |str1| ==> !haveCommonKSubstringPredicate(j, str1, str2)
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

  return 0;
// impl-end
}
