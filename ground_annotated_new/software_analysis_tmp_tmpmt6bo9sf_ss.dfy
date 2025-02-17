method find_min_index(a: array<int>, s: int, e: int)
    returns (min_i: int)
  // pre-conditions-start
  requires a.Length > 0
  requires 0 <= s < a.Length
  requires e <= a.Length
  requires e > s
  // pre-conditions-end
  // post-conditions-start
  ensures min_i >= s
  ensures min_i < e
  ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
  // post-conditions-end
{
// impl-start
  min_i := s;
  var i: int := s;
  while i < e
    // invariants-start

    invariant s <= i <= e
    invariant s <= min_i < e
    invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    decreases e - i
    // invariants-end

  {
    if a[i] <= a[min_i] {
      min_i := i;
    }
    i := i + 1;
  }
// impl-end
}

function is_sorted(ss: seq<int>): bool
{
  forall i, j: int :: 
    0 <= i <= j < |ss| ==>
      ss[i] <= ss[j]
}
// pure-end

function is_permutation(a: seq<int>, b: seq<int>): bool
  decreases |a|, |b|
{
  |a| == |b| &&
  ((|a| == 0 && |b| == 0) || exists i, j: int :: 0 <= i < |a| && 0 <= j < |b| && a[i] == b[j] && is_permutation(a[0 .. i] + if i < |a| then a[i + 1..] else [], b[0 .. j] + if j < |b| then b[j + 1..] else []))
}
// pure-end

function is_permutation2(a: seq<int>, b: seq<int>): bool
{
  multiset(a) == multiset(b)
}
// pure-end

method selection_sort(ns: array<int>)
  // pre-conditions-start
  requires ns.Length >= 0
  // pre-conditions-end
  // post-conditions-start
  modifies ns
  ensures is_sorted(ns[..])
  ensures is_permutation2(old(ns[..]), ns[..])
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  var l: int := ns.Length;
  while i < l
    // invariants-start

    invariant 0 <= i <= l
    invariant is_permutation2(old(ns[..]), ns[..])
    invariant forall k, kk: int :: 0 <= k < i && i <= kk < ns.Length ==> ns[k] <= ns[kk]
    invariant is_sorted(ns[..i])
    decreases l - i
    // invariants-end

  {
    var min_i: int := find_min_index(ns, i, ns.Length);
    ns[i], ns[min_i] := ns[min_i], ns[i];
    i := i + 1;
  }
// impl-end
}
