method IsGreater(n: int, a: array<int>) returns (result: bool)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
  ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
  // post-conditions-end
{
// impl-start
  result := true;
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result ==> forall k :: 0 <= k < i ==> n > a[k]
    invariant !result ==> exists k :: 0 <= k < i && n <= a[k]
    // invariants-end

  {
    if n <= a[i] {
      result := false;
      break;
    }
    i := i + 1;
  }
// impl-end
}
