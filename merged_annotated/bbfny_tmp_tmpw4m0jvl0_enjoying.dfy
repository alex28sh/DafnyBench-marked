method MultipleReturns(x: int, y: int)
    returns (more: int, less: int)
  // pre-conditions-start
  requires 0 < y
  // pre-conditions-end
  // post-conditions-start
  ensures less < x < more
  // post-conditions-end
{
// impl-start
  more := x + y;
  less := x - y;
// impl-end
}

method Max(a: int, b: int) returns (c: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a <= c && b <= c
  ensures a == c || b == c
  // post-conditions-end
{
// impl-start
  if a > b {
    c := a;
  } else {
    c := b;
  }
// impl-end
}

method Testing()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x := Max(3, 15);
  // assert-start
  assert x >= 3 && x >= 15;
  // assert-end

  // assert-start
  assert x == 15;
  // assert-end

// impl-end
}

function max(a: int, b: int): int
{
  if a > b then
    a
  else
    b
}
// pure-end

method Testing'()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert max(1, 2) == 2;
  // assert-end

  // assert-start
  assert forall a, b: int :: max(a, b) == a || max(a, b) == b;
  // assert-end

// impl-end
}

function abs(x: int): int
{
  if x < 0 then
    -x
  else
    x
}
// pure-end

method Abs(x: int) returns (y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y == abs(x)
  // post-conditions-end
{
// impl-start
  return abs(x);
// impl-end
}

method m(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i != n
    // invariants-start

    invariant 0 <= i <= n
    // invariants-end

  {
    i := i + 1;
  }
  // assert-start
  assert i == n;
  // assert-end

// impl-end
}

function fib(n: nat): nat
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}
// pure-end

method Find(a: array<int>, key: int) returns (index: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != key
    // invariants-end

  {
    if a[i] == key {
      return i;
    }
    i := i + 1;
  }
  // assert-start
  assert i == a.Length;
  // assert-end

  return -1;
// impl-end
}

method FindMax(a: array<int>) returns (i: int)
  // pre-conditions-start
  requires a.Length >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
  // post-conditions-end
{
// impl-start
  i := 0;
  var max := a[i];
  var j := 1;
  while j < a.Length
    // invariants-start

    invariant 0 < j <= a.Length
    invariant i < j
    invariant max == a[i]
    invariant forall k :: 0 <= k < j ==> a[k] <= max
    // invariants-end

  {
    if max < a[j] {
      max := a[j];
      i := j;
    }
    j := j + 1;
  }
// impl-end
}

function sorted(a: array<int>): bool
  reads a
{
  forall j, k :: 
    0 <= j < k < a.Length ==>
      a[j] < a[k]
}
// pure-end

function sorted'(a: array?<int>): bool
  reads a
{
  forall j, k :: 
    a != null &&
    0 <= j < k < a.Length ==>
      a[j] <= a[k]
}
// pure-end
