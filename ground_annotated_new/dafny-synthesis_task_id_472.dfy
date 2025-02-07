method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1]
  // post-conditions-end
{
// impl-start
  result := false;
  for i := 0 to a.Length - 1
    // invariants-start

    invariant 0 <= i <= a.Length - 1
    invariant result <==> exists k :: 0 <= k < i && a[k] + 1 == a[k + 1]
    // invariants-end

  {
    if a[i] + 1 == a[i + 1] {
      result := true;
      break;
    }
  }
// impl-end
}
