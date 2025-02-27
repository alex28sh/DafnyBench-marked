function IsEven(n: int): bool
{
  n % 2 == 0
}
// pure-end

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> forall i :: 0 <= i < |lst| ==> IsEven(i) ==> IsEven(lst[i])
  // post-conditions-end
{
// impl-start
  result := true;
  for i := 0 to |lst|
    // invariants-start

    invariant 0 <= i <= |lst|
    invariant result <==> forall k :: 0 <= k < i ==> IsEven(k) ==> IsEven(lst[k])
    // invariants-end

  {
    if IsEven(i) && !IsEven(lst[i]) {
      result := false;
      break;
    }
  }
// impl-end
}
