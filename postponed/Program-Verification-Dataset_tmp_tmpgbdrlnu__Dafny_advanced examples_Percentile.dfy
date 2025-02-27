
function SumUpto(A: array<real>, end: int): real
  requires -1 <= end < A.Length
  reads A
{
  if end == -1 then
    0.0
  else
    A[end] + SumUpto(A, end - 1)
}
// pure-end

function Sum(A: array<real>): real
  reads A
{
  SumUpto(A, A.Length - 1)
}
// pure-end

method Percentile(p: real, A: array<real>, total: real)
    returns (i: int)
  // pre-conditions-start
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= p / 100.0 * total
  ensures i + 1 < A.Length ==> SumUpto(A, i + 1) > p / 100.0 * total
  // post-conditions-end
{
// impl-start
  i := -1;
  var s: real := 0.0;
  while i + 1 != A.Length && s + A[i + 1] <= p / 100.0 * total
    // invariants-start

    invariant -1 <= i < A.Length
    invariant s == SumUpto(A, i)
    invariant s <= p / 100.0 * total
    // invariants-end

  {
    i := i + 1;
    s := s + A[i];
  }
// impl-end
}

method PercentileNonUniqueAnswer()
    returns (p: real, A: array<real>, total: real, i1: int, i2: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures 0.0 <= p <= 100.0
  ensures total == Sum(A)
  ensures total > 0.0
  ensures -1 <= i1 < A.Length
  ensures SumUpto(A, i1) <= p / 100.0 * total
  ensures i1 + 1 < A.Length ==> SumUpto(A, i1 + 1) >= p / 100.0 * total
  ensures -1 <= i2 < A.Length
  ensures SumUpto(A, i2) <= p / 100.0 * total
  ensures i2 + 1 < A.Length ==> SumUpto(A, i2 + 1) >= p / 100.0 * total
  ensures i1 != i2
  // post-conditions-end
{
// impl-start
  p := 100.0;
  A := new real[1];
  A[0] := 1.0;
  total := 1.0;
  // assert-start
  assert SumUpto(A, 0) == 1.0;
  // assert-end

  i1 := -1;
  i2 := 0;
// impl-end
}

lemma PercentileUniqueAnswer(p: real, A: array<real>, total: real, i1: int, i2: int)
  // pre-conditions-start
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  requires -1 <= i1 < A.Length
  requires SumUpto(A, i1) <= p / 100.0 * total
  requires i1 + 1 < A.Length ==> SumUpto(A, i1 + 1) > p / 100.0 * total
  requires -1 <= i2 < A.Length
  requires SumUpto(A, i2) <= p / 100.0 * total
  requires i2 + 1 < A.Length ==> SumUpto(A, i2 + 1) > p / 100.0 * total
  // pre-conditions-end
  // post-conditions-start
  ensures i1 == i2
  decreases if i2 < i1 then 1 else 0
  // post-conditions-end
{
// impl-start
  if i1 + 1 < i2 {
    SumUpto_increase(A, i1 + 1, i2);
  }
// impl-end
}

lemma SumUpto_increase(A: array<real>, end1: int, end2: int)
  // pre-conditions-start
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires -1 <= end1 < A.Length
  requires -1 <= end2 < A.Length
  requires end1 < end2
  // pre-conditions-end
  // post-conditions-start
  ensures SumUpto(A, end1) < SumUpto(A, end2)
  // post-conditions-end
{
// impl-start
// impl-end
}
