function strictSorted(s: seq<int>): bool
{
  forall u, w :: 
    0 <= u < w < |s| ==>
      s[u] < s[w]
}
// pure-end

method mcontained(v: array<int>, w: array<int>, n: int, m: int)
    returns (b: bool)
  // pre-conditions-start
  requires n <= m && n >= 0
  requires strictSorted(v[..])
  requires strictSorted(w[..])
  requires v.Length >= n && w.Length >= m
  // pre-conditions-end
  // post-conditions-start
  ensures b == forall k :: 0 <= k < n ==> v[k] in w[..m]
  // post-conditions-end
{
// impl-start
  var i := 0;
  var j := 0;
  while i < n && j < m && v[i] >= w[j]
    // invariants-start

    invariant 0 <= i <= n
    invariant 0 <= j <= m
    invariant strictSorted(v[..])
    invariant strictSorted(w[..])
    invariant forall k :: 0 <= k < i ==> v[k] in w[..j]
    invariant i < n ==> !(v[i] in w[..j])
    decreases w.Length - j, v.Length - i
    // invariants-end

  {
    if v[i] == w[j] {
      i := i + 1;
    }
    j := j + 1;
  }
  // assert-start
  assert i < n ==> !(v[i] in w[..m]);
  // assert-end

  b := i == n;
// impl-end
}
