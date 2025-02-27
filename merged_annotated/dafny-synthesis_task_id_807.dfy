function IsOdd(x: int): bool
{
  x % 2 != 0
}
// pure-end

method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
  ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
  // post-conditions-end
{
// impl-start
  found := false;
  index := 0;
  while index < a.Length
    // invariants-start

    invariant 0 <= index <= a.Length
    invariant !found ==> forall i :: 0 <= i < index ==> !IsOdd(a[i])
    invariant found ==> IsOdd(a[index - 1]) && forall i :: 0 <= i < index - 1 ==> !IsOdd(a[i])
    // invariants-end

  {
    if IsOdd(a[index]) {
      found := true;
      return;
    }
    index := index + 1;
  }
// impl-end
}
