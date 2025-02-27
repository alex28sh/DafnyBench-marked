method IsPalindrome(x: seq<char>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1]
  // post-conditions-end
{
// impl-start
  if |x| == 0 {
    return true;
  }
  var i := 0;
  var j := |x| - 1;
  result := true;
  while i < j
    // invariants-start

    invariant 0 <= i <= j + 1 && 0 <= j < |x|
    invariant i + j == |x| - 1
    invariant forall k :: 0 <= k < i ==> x[k] == x[|x| - k - 1]
    // invariants-end

  {
    if x[i] != x[j] {
      result := false;
      return;
    }
    i := i + 1;
    j := j - 1;
  }
// impl-end
}
