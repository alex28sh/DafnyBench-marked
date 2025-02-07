function IsEven(n: int): bool
{
  n % 2 == 0
}
// pure-end

function IsOdd(n: int): bool
{
  n % 2 != 0
}
// pure-end

method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  // pre-conditions-start
  requires a.Length >= 2
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  // pre-conditions-end
  // post-conditions-start
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && (forall k :: 0 <= k < i ==> IsOdd(a[k])) && forall k :: 0 <= k < j ==> IsEven(a[k])
  // post-conditions-end
{
// impl-start
  var firstEven: int := -1;
  var firstOdd: int := -1;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant firstEven == -1 || (0 <= firstEven < i && IsEven(a[firstEven]))
    invariant firstOdd == -1 || (0 <= firstOdd < i && IsOdd(a[firstOdd]))
    invariant firstEven == -1 ==> forall k :: 0 <= k < i ==> !IsEven(a[k])
    invariant firstOdd == -1 ==> forall k :: 0 <= k < i ==> !IsOdd(a[k])
    invariant firstEven != -1 ==> forall k :: 0 <= k < firstEven ==> IsOdd(a[k])
    invariant firstOdd != -1 ==> forall k :: 0 <= k < firstOdd ==> IsEven(a[k])
    // invariants-end

  {
    if firstEven == -1 && IsEven(a[i]) {
      firstEven := i;
    }
    if firstOdd == -1 && IsOdd(a[i]) {
      firstOdd := i;
    }
    if firstEven != -1 && firstOdd != -1 {
      break;
    }
  }
  diff := a[firstEven] - a[firstOdd];
// impl-end
}
