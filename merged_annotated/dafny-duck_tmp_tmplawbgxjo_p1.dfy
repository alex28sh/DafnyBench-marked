function Sum(xs: seq<int>): int
{
  if |xs| == 0 then
    0
  else
    Sum(xs[..|xs| - 1]) + xs[|xs| - 1]
}
// pure-end

method SumArray(xs: array<int>) returns (s: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == Sum(xs[..])
  // post-conditions-end
{
// impl-start
  s := 0;
  var i := 0;
  while i < xs.Length
    // invariants-start

    invariant 0 <= i <= xs.Length
    invariant s == Sum(xs[..i])
    // invariants-end

  {
    s := s + xs[i];
    // assert-start
    assert xs[..i + 1] == xs[..i] + [xs[i]];
    // assert-end

    i := i + 1;
  }
  // assert-start
  assert xs[..] == xs[..i];
  // assert-end

// impl-end
}
