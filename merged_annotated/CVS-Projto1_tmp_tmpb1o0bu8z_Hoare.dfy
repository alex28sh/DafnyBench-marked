method Max(x: nat, y: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r >= x && r >= y
  ensures r == x || r == y
  // post-conditions-end
{
// impl-start
  if x >= y {
    r := x;
  } else {
    r := y;
  }
// impl-end
}

method Test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var result := Max(42, 73);
  // assert-start
  assert result == 73;
  // assert-end

// impl-end
}

method m1(x: int, y: int) returns (z: int)
  // pre-conditions-start
  requires 0 < x < y
  // pre-conditions-end
  // post-conditions-start
  ensures z >= 0 && z <= y && z != x
  // post-conditions-end
{
// impl-start
  z := 0;
// impl-end
}

function fib(n: nat): nat
{
  if n == 0 then
    1
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}
// pure-end

method Fib(n: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == fib(n)
  // post-conditions-end
{
// impl-start
  if n == 0 {
    return 1;
  }
  r := 1;
  var next := 2;
  var i := 1;
  while i < n
    // invariants-start

    invariant 1 <= i <= n
    invariant r == fib(i)
    invariant next == fib(i + 1)
    // invariants-end

  {
    var tmp := next;
    next := next + r;
    r := tmp;
    i := i + 1;
  }
  // assert-start
  assert r == fib(n);
  // assert-end

  return r;
// impl-end
}

function add(l: List<int>): int
{
  match l
  case Nil =>
    0
  case Cons(x, xs) =>
    x + add(xs)
}
// pure-end

method addImp(l: List<int>) returns (s: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == add(l)
  // post-conditions-end
{
// impl-start
  var ll := l;
  s := 0;
  while ll != Nil
    // invariants-start

    invariant add(l) == s + add(ll)
    decreases ll
    // invariants-end

  {
    s := s + ll.head;
    ll := ll.tail;
  }
  // assert-start
  assert s == add(l);
  // assert-end

// impl-end
}

method MaxA(a: array<int>) returns (m: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures exists i :: 0 <= i < a.Length && a[i] == m
  // post-conditions-end
{
// impl-start
  m := a[0];
  var i := 1;
  while i < a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && a[j] == m
    // invariants-end

  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
// impl-end
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
