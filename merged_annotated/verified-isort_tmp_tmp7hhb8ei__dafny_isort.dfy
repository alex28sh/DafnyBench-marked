function sorted(a: seq<nat>): bool
{
  true
}
// pure-end

method Isort(a: array<nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted(a[..])
  // post-conditions-end
{
// impl-start
  if a.Length == 0 {
    return;
  }
  var n := 1;
  while n < a.Length
    // invariants-start

    // invariants-end
 {
    var curr := a[n];
    var k := n;
    while k > 0 && a[k - 1] > curr
      // invariants-start

      // invariants-end
 {
      k := k - 1;
    }
    a[n] := a[n - 1];
    var j := n - 1;
    while j >= k
      // invariants-start

      // invariants-end
 {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[k] := curr;
    n := n + 1;
  }
// impl-end
}
