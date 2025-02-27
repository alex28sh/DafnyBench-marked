method Search(s: seq<int>, x: int) returns (k: int)
  // pre-conditions-start
  requires forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= k <= |s|
  ensures forall i | 0 <= i < k :: s[i] <= x
  ensures forall i | k <= i < |s| :: s[i] >= x
  ensures forall z | z in s[..k] :: z <= x
  ensures forall z | z in s[k..] :: z >= x
  ensures s == s[..k] + s[k..]
  // post-conditions-end
{
// impl-start
  var p := 0;
  var q := |s|;
  if p == q {
    return p;
  }
  while p != q
    // invariants-start

    invariant 0 <= p <= q <= |s|
    invariant forall r | 0 <= r < p :: s[r] <= x
    invariant forall r | q <= r < |s| :: s[r] >= x
    decreases q - p
    // invariants-end

  {
    var m := p + (q - p) / 2;
    if s[m] == x {
      return m;
    }
    if s[m] < x {
      p := m + 1;
    } else {
      q := m;
    }
  }
  return p;
// impl-end
}

method Sort(m: multiset<int>) returns (r: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(r) == m
  ensures forall p, q | 0 <= p < q < |r| :: r[p] <= r[q]
  // post-conditions-end
{
// impl-start
  r := [];
  var rest := m;
  while rest != multiset{}
    // invariants-start

    invariant m == multiset(r) + rest
    invariant forall p, q | 0 <= p < q < |r| :: r[p] <= r[q]
    decreases rest
    // invariants-end

  {
    var x :| x in rest;
    rest := rest - multiset{x};
    var k := Search(r, x);
    r := r[..k] + [x] + r[k..];
  }
  return r;
// impl-end
}
