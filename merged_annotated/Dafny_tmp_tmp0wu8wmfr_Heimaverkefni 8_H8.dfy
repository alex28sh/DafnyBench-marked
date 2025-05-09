method Partition(m: multiset<int>)
    returns (pre: multiset<int>, p: int, post: multiset<int>)
  // pre-conditions-start
  requires |m| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures p in m
  ensures m == pre + multiset{p} + post
  ensures forall z | z in pre :: z <= p
  ensures forall z | z in post :: z >= p
  // post-conditions-end
{
// impl-start
  p :| p in m;
  var m' := m;
  m' := m' - multiset{p};
  pre := multiset{};
  post := multiset{};
  while m' != multiset{}
    // invariants-start

    invariant m == m' + pre + multiset{p} + post
    invariant forall k | k in pre :: k <= p
    invariant forall k | k in post :: k >= p
    decreases m'
    // invariants-end

  {
    var temp :| temp in m';
    m' := m' - multiset{temp};
    if temp <= p {
      pre := pre + multiset{temp};
    } else {
      post := post + multiset{temp};
    }
  }
  return pre, p, post;
// impl-end
}

method QuickSelect(m: multiset<int>, k: int)
    returns (pre: multiset<int>, kth: int, post: multiset<int>)
  // pre-conditions-start
  requires 0 <= k < |m|
  // pre-conditions-end
  // post-conditions-start
  ensures kth in m
  ensures m == pre + multiset{kth} + post
  ensures |pre| == k
  ensures forall z | z in pre :: z <= kth
  ensures forall z | z in post :: z >= kth
  decreases m
  // post-conditions-end
{
// impl-start
  pre, kth, post := Partition(m);
  // assert-start
  assert m == pre + multiset{kth} + post;
  // assert-end

  if |pre| != k {
    if k > |pre| {
      var pre', p, post' := QuickSelect(post, k - |pre| - 1);
      // assert-start
      assert pre' + multiset{p} + post' == post;
      // assert-end

      pre := pre + multiset{kth} + pre';
      post := post - pre' - multiset{p};
      kth := p;
    } else if k < |pre| {
      var pre', p, post' := QuickSelect(pre, k);
      pre := pre - multiset{p} - post';
      post := post + multiset{kth} + post';
      kth := p;
    }
  } else {
    return pre, kth, post;
  }
// impl-end
}
