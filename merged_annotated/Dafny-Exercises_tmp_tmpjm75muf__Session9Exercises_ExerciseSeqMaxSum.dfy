function Sum(v: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= v.Length
  reads v
  decreases j
{
  if i == j then
    0
  else
    Sum(v, i, j - 1) + v[j - 1]
}
// pure-end

function SumMaxToRight(v: array<int>, i: int, s: int): bool
  requires 0 <= i < v.Length
  reads v
{
  forall l, ss {:induction l} :: 
    0 <= l <= i &&
    ss == i + 1 ==>
      Sum(v, l, ss) <= s
}
// pure-end

method segMaxSum(v: array<int>, i: int)
    returns (s: int, k: int)
  // pre-conditions-start
  requires v.Length > 0 && 0 <= i < v.Length
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= k <= i && s == Sum(v, k, i + 1) && SumMaxToRight(v, i, s)
  // post-conditions-end
{
// impl-start
  s := v[0];
  k := 0;
  var j := 0;
  while j < i
    // invariants-start

    invariant 0 <= j <= i
    invariant 0 <= k <= j && s == Sum(v, k, j + 1)
    invariant SumMaxToRight(v, j, s)
    decreases i - j
    // invariants-end

  {
    if s + v[j + 1] > v[j + 1] {
      s := s + v[j + 1];
    } else {
      k := j + 1;
      s := v[j + 1];
    }
    j := j + 1;
  }
// impl-end
}

function Sum2(v: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= v.Length
  reads v
  decreases j - i
{
  if i == j then
    0
  else
    v[i] + Sum2(v, i + 1, j)
}
// pure-end

function SumMaxToRight2(v: array<int>, j: int, i: int, s: int): bool
  requires 0 <= j <= i < v.Length
  reads v
{
  forall l, ss {:induction l} :: 
    j <= l <= i &&
    ss == i + 1 ==>
      Sum2(v, l, ss) <= s
}
// pure-end

method segSumaMaxima2(v: array<int>, i: int)
    returns (s: int, k: int)
  // pre-conditions-start
  requires v.Length > 0 && 0 <= i < v.Length
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= k <= i && s == Sum2(v, k, i + 1) && SumMaxToRight2(v, 0, i, s)
  // post-conditions-end
{
// impl-start
  s := v[i];
  k := i;
  var j := i;
  var maxs := s;
  while j > 0
    // invariants-start

    invariant 0 <= j <= i
    invariant 0 <= k <= i
    invariant s == Sum2(v, j, i + 1)
    invariant SumMaxToRight2(v, j, i, maxs)
    invariant maxs == Sum2(v, k, i + 1)
    decreases j
    // invariants-end

  {
    s := s + v[j - 1];
    if s > maxs {
      maxs := s;
      k := j - 1;
    }
    j := j - 1;
  }
  s := maxs;
// impl-end
}
