method multipleReturns(x: int, y: int)
    returns (more: int, less: int)
  // pre-conditions-start
  requires y > 0
  // pre-conditions-end
  // post-conditions-start
  ensures less < x < more
  // post-conditions-end

method multipleReturns2(x: int, y: int)
    returns (more: int, less: int)
  // pre-conditions-start
  requires y > 0
  // pre-conditions-end
  // post-conditions-start
  ensures more + less == 2 * x
  // post-conditions-end

method multipleReturns3(x: int, y: int)
    returns (more: int, less: int)
  // pre-conditions-start
  requires y > 0
  // pre-conditions-end
  // post-conditions-start
  ensures more - less == 2 * y
  // post-conditions-end

function factorial(n: int): int
  requires n >= 0
{
  if n == 0 || n == 1 then
    1
  else
    n * factorial(n - 1)
}
// pure-end

method ComputeFact(n: int) returns (f: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures f == factorial(n)
  // post-conditions-end
{
// impl-start
  // assert-start
  assert 0 <= n <= n && 1 * factorial(n) == factorial(n);
  // assert-end

  f := 1;
  // assert-start
  assert 0 <= n <= n && f * factorial(n) == factorial(n);
  // assert-end

  var x := n;
  // assert-start
  assert 0 <= x <= n && f * factorial(x) == factorial(n);
  // assert-end

  while x > 0
    // invariants-start

    invariant 0 <= x <= n
    invariant f * factorial(x) == factorial(n)
    decreases x - 0
    // invariants-end

  {
    // assert-start
    assert 0 <= x - 1 <= n && f * x * factorial(x - 1) == factorial(n);
    // assert-end

    f := f * x;
    // assert-start
    assert 0 <= x - 1 <= n && f * factorial(x - 1) == factorial(n);
    // assert-end

    x := x - 1;
    // assert-start
    assert 0 <= x <= n && f * factorial(x) == factorial(n);
    // assert-end

  }
  // assert-start
  assert 0 <= x <= n && f * factorial(x) == factorial(n);
  // assert-end

// impl-end
}

method ComputeFact2(n: int) returns (f: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures f == factorial(n)
  // post-conditions-end
{
// impl-start
  var x := 0;
  f := 1;
  while x < n
    // invariants-start

    invariant 0 <= x <= n
    invariant f == factorial(x)
    decreases n - x
    // invariants-end

  {
    x := x + 1;
    f := f * x;
    // assert-start
    assert 0 <= x <= n && f == factorial(x);
    // assert-end

  }
// impl-end
}

method Sqare(a: int) returns (x: int)
  // pre-conditions-start
  requires a >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures x == a * a
  // post-conditions-end
{
// impl-start
  // assert-start
  assert 1 == 1 && 1 <= 1 <= a;
  // assert-end

  var y := 1;
  // assert-start
  assert y * y == 1 && 1 <= y <= a;
  // assert-end

  x := 1;
  while y < a
    // invariants-start

    invariant 1 <= y <= a
    invariant y * y == x
    // invariants-end

  {
    // assert-start
    assert (y + 1) * (y + 1) == x + (2 * (y + 1) - 1) && 1 <= y + 1 <= a;
    // assert-end

    y := y + 1;
    // assert-start
    assert y * y == x + (2 * y - 1) && 1 <= y <= a;
    // assert-end

    x := x + (2 * y - 1);
    // assert-start
    assert y * y == x && 1 <= y <= a;
    // assert-end

  }
  // assert-start
  assert y * y == x && 1 <= y <= a;
  // assert-end

// impl-end
}

function sumSerie(n: int): int
  requires n >= 1
{
  if n == 1 then
    1
  else
    sumSerie(n - 1) + 2 * n - 1
}
// pure-end

lemma {:induction false} Sqare_Lemma(n: int)
  // pre-conditions-start
  requires n >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures sumSerie(n) == n * n
  // post-conditions-end
{
// impl-start
  if n == 1 {
  } else {
    Sqare_Lemma(n - 1);
    assert sumSerie(n - 1) == (n - 1) * (n - 1);
    calc == {
      sumSerie(n);
      sumSerie(n - 1) + 2 * n - 1;
      {
        Sqare_Lemma(n - 1);
        assert sumSerie(n - 1) == (n - 1) * (n - 1);
      }
      (n - 1) * (n - 1) + 2 * n - 1;
      n * n - 2 * n + 1 + 2 * n - 1;
      n * n;
    }
    assert sumSerie(n) == n * n;
  }
// impl-end
}

method Sqare2(a: int) returns (x: int)
  // pre-conditions-start
  requires a >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures x == a * a
  // post-conditions-end
{
// impl-start
  // assert-start
  assert 1 <= 1 <= a && 1 == 1 * 1;
  // assert-end

  var y := 1;
  // assert-start
  assert 1 <= y <= a && 1 == y * y;
  // assert-end

  x := 1;
  // assert-start
  assert 1 <= y <= a && x == y * y;
  // assert-end

  while y < a
    // invariants-start

    invariant 1 <= y <= a
    invariant x == y * y
    decreases a - y
    // invariants-end

  {
    // assert-start
    assert 1 <= y + 1 <= a && x + 2 * (y + 1) - 1 == (y + 1) * (y + 1);
    // assert-end

    y := y + 1;
    // assert-start
    assert 1 <= y <= a && x + 2 * y - 1 == y * y;
    // assert-end

    x := x + 2 * y - 1;
    // assert-start
    assert 1 <= y <= a && x == y * y;
    // assert-end

  }
  // assert-start
  assert 1 <= y <= a && x == y * y;
  // assert-end

// impl-end
}
