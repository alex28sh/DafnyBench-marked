method MinOfMultiset(m: multiset<int>) returns (min: int)
  // pre-conditions-start
  requires m != multiset{}
  // pre-conditions-end
  // post-conditions-start
  ensures min in m
  ensures forall z | z in m :: min <= z
  // post-conditions-end
{
// impl-start
  min :| min in m;
  var done := multiset{min};
  var m' := m - done;
  while m' != multiset{}
    // invariants-start

    invariant m == done + m'
    invariant min in done
    invariant forall z | z in done :: min <= z
    decreases m'
    // invariants-end

  {
    var z :| z in m';
    done := done + multiset{z};
    m' := m' - multiset{z};
    if z < min {
      min := z;
    }
  }
// impl-end
}

method Test(m: multiset<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var s := Sort(m);
  // assert-start
  assert multiset(s) == m;
  // assert-end

  // assert-start
  assert forall p, q | 0 <= p < q < |s| :: s[p] <= s[q];
  // assert-end

// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var m := multiset{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  var s := Sort(m);
  // assert-start
  assert multiset(s) == m;
  // assert-end

  // assert-start
  assert forall p, q | 0 <= p < q < |s| :: s[p] <= s[q];
  // assert-end

  print s;
// impl-end
}

method Sort(m: multiset<int>) returns (s: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(s) == m
  ensures forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  // post-conditions-end
{
// impl-start
  s := [];
  var m' := m;
  while m' != multiset{}
    // invariants-start

    invariant m == m' + multiset(s)
    invariant forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
    invariant forall z | z in m' :: forall r | 0 <= r < |s| :: z >= s[r]
    decreases m'
    // invariants-end

  {
    var x := MinOfMultiset(m');
    m' := m' - multiset{x};
    s := s + [x];
  }
  return s;
// impl-end
}
