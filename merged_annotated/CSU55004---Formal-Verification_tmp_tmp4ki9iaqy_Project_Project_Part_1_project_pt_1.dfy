method isPrefix(pre: string, str: string) returns (res: bool)
  // pre-conditions-start
  requires 0 < |pre| <= |str|
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < |pre|
    // invariants-start

    invariant 0 <= i <= |pre|
    decreases |pre| - i
    // invariants-end

  {
    if str[i] != pre[i] {
      print str[i], " != ", pre[i], "\n";
      return false;
    } else {
      print str[i], " == ", pre[i], "\n";
      i := i + 1;
    }
  }
  return true;
// impl-end
}

method isSubstring(sub: string, str: string) returns (res: bool)
  // pre-conditions-start
  requires 0 < |sub| <= |str|
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i := 0;
  var n := |str| - |sub|;
  while i < n + 1
    // invariants-start

    invariant 0 <= i <= n + 1
    decreases n - i
    // invariants-end

  {
    print "\n", sub, ", ", str[i .. |str|], "\n";
    var result := isPrefix(sub, str[i .. |str|]);
    if result == true {
      return true;
    } else {
      i := i + 1;
    }
  }
  return false;
// impl-end
}

method haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  // pre-conditions-start
  requires 0 < k <= |str1| && 0 < k <= |str2|
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i := 0;
  var n := |str1| - k;
  while i < n
    // invariants-start

    decreases n - i
    // invariants-end

  {
    print "\n", str1[i .. i + k], ", ", str2, "\n";
    var result := isSubstring(str1[i .. i + k], str2);
    if result == true {
      return true;
    } else {
      i := i + 1;
    }
  }
  return false;
// impl-end
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  // pre-conditions-start
  requires 0 < |str1| && 0 < |str1|
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var result: bool;
  var i := |str1|;
  if |str2| < |str1| {
    i := |str2|;
  }
  while i > 0
    // invariants-start

    decreases i - 0
    // invariants-end

  {
    print str1, ", ", str2, " k = ", i, "\n";
    result := haveCommonKSubstring(i, str1, str2);
    if result == true {
      return i;
    } else {
      i := i - 1;
    }
  }
  return 0;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var prefix: string := "pre";
  var str_1: string := "prehistoric";
  var result: bool;
  var substring := "and";
  var str_2 := "operand";
  var string1 := "operation";
  var string2 := "irrational";
  var k: nat := 5;
  var x := maxCommonSubstringLength(string1, string2);
  print "Result: ", x, "\n";
// impl-end
}
