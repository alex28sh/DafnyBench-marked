method SqrSum(n: int) returns (s: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i, k: int;
  s := 0;
  k := 1;
  i := 1;
  while i <= n
    // invariants-start

    decreases n - i
    // invariants-end

  {
    s := s + k;
    k := k + 2 * i + 1;
    i := i + 1;
  }
// impl-end
}

method DivMod(a: int, b: int)
    returns (q: int, r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  decreases *
  // post-conditions-end
{
// impl-start
  q := 0;
  r := a;
  while r >= b
    // invariants-start

    decreases *
    // invariants-end

  {
    r := r - b;
    q := q + 1;
  }
// impl-end
}

method HoareTripleAssmAssrt()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i: int := *;
  var k: int := *;
  // assert-start
  assume k == i * i;
  // assert-end

  k := k + 2 * i + 1;
  // assert-start
  assert k == (i + 1) * (i + 1);
  // assert-end

// impl-end
}

method HoareTripleReqEns(i: int, k: int) returns (k': int)
  // pre-conditions-start
  requires k == i * i
  // pre-conditions-end
  // post-conditions-start
  ensures k' == (i + 1) * (i + 1)
  // post-conditions-end
{
// impl-start
  k' := k + 2 * i + 1;
// impl-end
}

method Invariant1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var n: int :| n >= 0;
  var y := n;
  var x := 0;
  while y >= 0
    // invariants-start

    invariant x + y == n
    decreases y
    // invariants-end

  {
    x := x + 1;
    y := y - 1;
  }
  // assert-start
  assert y < 0 && x + y == n;
  // assert-end

// impl-end
}

function SqrSumRec(n: int): int
  requires n >= 0
{
  if n == 0 then
    0
  else
    n * n + SqrSumRec(n - 1)
}
// pure-end

method SqrSum1(n: int) returns (s: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures s == SqrSumRec(n)
  // post-conditions-end
{
// impl-start
  var i, k: int;
  s := 0;
  k := 1;
  i := 1;
  while i <= n
    // invariants-start

    invariant k == i * i
    invariant s == SqrSumRec(i - 1)
    invariant i <= n + 1
    decreases n - i
    // invariants-end

  {
    s := s + k;
    k := k + 2 * i + 1;
    i := i + 1;
  }
// impl-end
}

least lemma L1(n: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures SqrSumRec(n) == n * (n + 1) * (2 * n + 1) / 6
  // post-conditions-end
{
// impl-start
// impl-end
}

method DivMod1(a: int, b: int)
    returns (q: int, r: int)
  // pre-conditions-start
  requires b > 0 && a >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures a == b * q + r && 0 <= r < b
  // post-conditions-end
{
// impl-start
  q := 0;
  r := a;
  while r >= b
    // invariants-start

    invariant r >= 0
    invariant a == b * q + r
    decreases r
    // invariants-end

  {
    r := r - b;
    q := q + 1;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  decreases *
  // post-conditions-end
{
// impl-start
  var v := SqrSum(5);
  print "SqrSum(5): ", v, "\n";
  var q, r := DivMod(5, 3);
  print "DivMod(5, 3): ", q, ", ", r, "\n";
// impl-end
}
