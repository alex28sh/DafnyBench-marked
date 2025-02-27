method SumMinMax(a: array<int>) returns (sum: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == Max(a[..]) + Min(a[..])
  // post-conditions-end
{
// impl-start
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant minVal <= maxVal
    invariant forall k :: 0 <= k < i ==> minVal <= a[k] && a[k] <= maxVal
    invariant minVal == Min(a[..i])
    invariant maxVal == Max(a[..i])
    // invariants-end

  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
    // assert-start
    assert a[..i + 1][..i] == a[..i];
    // assert-end

  }
  // assert-start
  assert a[..a.Length] == a[..];
  // assert-end

  sum := minVal + maxVal;
// impl-end
}

function Min(a: seq<int>): int
  requires |a| > 0
{
  if |a| == 1 then
    a[0]
  else
    var minPrefix := Min(a[..|a| - 1]); if a[|a| - 1] <= minPrefix then a[|a| - 1] else Min(a[..|a| - 1])
}
// pure-end

function Max(a: seq<int>): int
  requires |a| > 0
{
  if |a| == 1 then
    a[0]
  else
    var maxPrefix := Max(a[..|a| - 1]); if a[|a| - 1] >= maxPrefix then a[|a| - 1] else Max(a[..|a| - 1])
}
// pure-end
