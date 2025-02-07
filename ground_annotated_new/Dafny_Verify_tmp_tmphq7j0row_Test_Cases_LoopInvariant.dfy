method UpWhileLess(N: int) returns (i: int)
  // pre-conditions-start
  requires 0 <= N
  // pre-conditions-end
  // post-conditions-start
  ensures i == N
  // post-conditions-end
{
// impl-start
  i := 0;
  while i < N
    // invariants-start

    invariant 0 <= i <= N
    decreases N - i
    // invariants-end

  {
    i := i + 1;
  }
// impl-end
}

method UpWhileNotEqual(N: int) returns (i: int)
  // pre-conditions-start
  requires 0 <= N
  // pre-conditions-end
  // post-conditions-start
  ensures i == N
  // post-conditions-end
{
// impl-start
  i := 0;
  while i != N
    // invariants-start

    invariant 0 <= i <= N
    decreases N - i
    // invariants-end

  {
    i := i + 1;
  }
// impl-end
}

method DownWhileNotEqual(N: int) returns (i: int)
  // pre-conditions-start
  requires 0 <= N
  // pre-conditions-end
  // post-conditions-start
  ensures i == 0
  // post-conditions-end
{
// impl-start
  i := N;
  while i != 0
    // invariants-start

    invariant 0 <= i <= N
    decreases i
    // invariants-end

  {
    i := i - 1;
  }
// impl-end
}

method DownWhileGreater(N: int) returns (i: int)
  // pre-conditions-start
  requires 0 <= N
  // pre-conditions-end
  // post-conditions-start
  ensures i == 0
  // post-conditions-end
{
// impl-start
  i := N;
  while 0 < i
    // invariants-start

    invariant 0 <= i <= N
    decreases i
    // invariants-end

  {
    i := i - 1;
  }
// impl-end
}

method Quotient()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x, y := 0, 191;
  while 7 <= y
    // invariants-start

    invariant 0 <= y && 7 * x + y == 191
    // invariants-end

  {
    y := y - 7;
    x := x + 1;
  }
  // assert-start
  assert x == 191 / 7 && y == 191 % 7;
  // assert-end

// impl-end
}

method Quotient1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x, y := 0, 191;
  while 7 <= y
    // invariants-start

    invariant 0 <= y && 7 * x + y == 191
    // invariants-end

  {
    x, y := 27, 2;
  }
  // assert-start
  assert x == 191 / 7 && y == 191 % 7;
  // assert-end

// impl-end
}
