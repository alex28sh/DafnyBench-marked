function isPeek(v: array<int>, i: int): bool
  requires 0 <= i < v.Length
  reads v
{
  forall k :: 
    0 <= k < i ==>
      v[i] >= v[k]
}
// pure-end

function peekSum(v: array<int>, i: int): int
  requires 0 <= i <= v.Length
  reads v
  decreases i
{
  if i == 0 then
    0
  else if isPeek(v, i - 1) then
    v[i - 1] + peekSum(v, i - 1)
  else
    peekSum(v, i - 1)
}
// pure-end

method mPeekSum(v: array<int>) returns (sum: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == peekSum(v, v.Length)
  // post-conditions-end
{
// impl-start
  var i := 1;
  sum := v[0];
  var lmax := v[0];
  while i < v.Length
    // invariants-start

    invariant 0 < i <= v.Length
    invariant lmax in v[..i]
    invariant forall k :: 0 <= k < i ==> lmax >= v[k]
    invariant sum == peekSum(v, i)
    decreases v.Length - i
    // invariants-end

  {
    if v[i] >= lmax {
      sum := sum + v[i];
      lmax := v[i];
    }
    i := i + 1;
  }
// impl-end
}
