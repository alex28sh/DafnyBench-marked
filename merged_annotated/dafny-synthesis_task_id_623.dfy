method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |l|
  ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
  // post-conditions-end
{
// impl-start
  result := [];
  for i := 0 to |l|
    // invariants-start

    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == Power(l[k], n)
    // invariants-end

  {
    result := result + [Power(l[i], n)];
  }
// impl-end
}

function Power(base: int, exponent: int): int
  requires exponent >= 0
{
  if exponent == 0 then
    1
  else
    base * Power(base, exponent - 1)
}
// pure-end
