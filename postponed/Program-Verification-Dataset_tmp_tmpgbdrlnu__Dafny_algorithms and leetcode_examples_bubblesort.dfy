function NChoose2(n: int): int
{
  n * (n - 1) / 2
}
// pure-end

function SumRange(lo: int, hi: int): int
  decreases hi - lo
{
  if lo >= hi then
    0
  else
    SumRange(lo, hi - 1) + hi - 1
}
// pure-end

lemma SumRangeNChoose2(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SumRange(0, n) == NChoose2(n)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma SumRangeUnrollLeft(lo: int, hi: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SumRange(lo, hi) == if lo >= hi then 0 else lo + SumRange(lo + 1, hi)
  decreases hi - lo
  // post-conditions-end
{
// impl-start
// impl-end
}

method BubbleSort(a: array<int>) returns (n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures n <= NChoose2(a.Length)
  // post-conditions-end
{
// impl-start
  if a.Length == 0 {
    return 0;
  }
  var i := a.Length - 1;
  n := 0;
  while i > 0
    // invariants-start

    invariant 0 <= i < a.Length
    invariant n <= SumRange(i + 1, a.Length)
    // invariants-end

  {
    var j := 0;
    while j < i
      // invariants-start

      invariant n <= SumRange(i + 1, a.Length) + j
      invariant j <= i
      // invariants-end

    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
        n := n + 1;
      }
      j := j + 1;
    }
    // assert-start
    assert n <= SumRange(i, a.Length) by {
      SumRangeUnrollLeft(i, a.Length);
    }
    // assert-end

    i := i - 1;
  }
  calc <= {
    n;
    SumRange(1, a.Length);
    {
      SumRangeUnrollLeft(0, a.Length);
    }
    SumRange(0, a.Length);
    {
      SumRangeNChoose2(a.Length);
    }
    NChoose2(a.Length);
  }
// impl-end
}
