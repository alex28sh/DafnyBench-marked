function IsSorted(s: seq<int>): bool
{
  forall p, q | 0 <= p < q < |s| :: 
    s[p] <= s[q]
}
// pure-end

method InsertionSort(s: seq<int>) returns (r: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(r) == multiset(s)
  ensures IsSorted(r)
  // post-conditions-end
{
// impl-start
  r := [];
  var rest := s;
  while rest != []
    // invariants-start

    invariant multiset(s) == multiset(r) + multiset(rest)
    invariant IsSorted(r)
    decreases rest
    // invariants-end

  {
    var x := rest[0];
    // assert-start
    assert rest == rest[0 .. 1] + rest[1..];
    // assert-end

    rest := rest[1..];
    var k := |r|;
    while k > 0 && r[k - 1] > x
      // invariants-start

      invariant 0 <= k <= |r|
      invariant forall p | k <= p < |r| :: r[p] > x
      // invariants-end

    {
      k := k - 1;
    }
    // assert-start
    assert r == r[..k] + r[k..];
    // assert-end

    r := r[..k] + [x] + r[k..];
  }
// impl-end
}
