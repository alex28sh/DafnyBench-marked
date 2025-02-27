function IsOdd(n: int): bool
{
  n % 2 == 1
}
// pure-end

method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> forall i :: 0 <= i < a.Length ==> IsOdd(i) ==> IsOdd(a[i])
  // post-conditions-end
{
// impl-start
  result := true;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result <==> forall k :: 0 <= k < i ==> IsOdd(k) ==> IsOdd(a[k])
    // invariants-end

  {
    if IsOdd(i) && !IsOdd(a[i]) {
      result := false;
      break;
    }
  }
// impl-end
}
