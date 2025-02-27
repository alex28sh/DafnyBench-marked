function IsEven(n: int): bool
{
  n % 2 == 0
}
// pure-end

method IsProductEven(a: array<int>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
  // post-conditions-end
{
// impl-start
  result := false;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result <==> exists k :: 0 <= k < i && IsEven(a[k])
    // invariants-end

  {
    if IsEven(a[i]) {
      result := true;
      break;
    }
  }
// impl-end
}
