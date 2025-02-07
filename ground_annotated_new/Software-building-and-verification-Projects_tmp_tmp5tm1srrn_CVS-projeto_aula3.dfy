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
  var next := 2;
  r := 1;
  var i := 1;
  while i < n
    // invariants-start

    invariant next == fib(i + 1)
    invariant r == fib(i)
    invariant 1 <= i <= n
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

method addImp(l: List<int>) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == add(l)
  // post-conditions-end
{
// impl-start
  r := 0;
  var ll := l;
  while ll != Nil
    // invariants-start

    invariant r == add(l) - add(ll)
    decreases ll
    // invariants-end

  {
    r := r + ll.head;
    ll := ll.tail;
  }
  // assert-start
  assert r == add(l);
  // assert-end

// impl-end
}

method maxArray(arr: array<int>) returns (max: int)
  // pre-conditions-start
  requires arr.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x :: 0 <= x < arr.Length && arr[x] == max
  // post-conditions-end
{
// impl-start
  max := arr[0];
  var index := 1;
  while index < arr.Length
    // invariants-start

    invariant 0 <= index <= arr.Length
    invariant forall i: int :: 0 <= i < index ==> arr[i] <= max
    invariant exists x :: 0 <= x < arr.Length && arr[x] == max
    // invariants-end

  {
    if arr[index] > max {
      max := arr[index];
    }
    index := index + 1;
  }
// impl-end
}

method maxArrayReverse(arr: array<int>) returns (max: int)
  // pre-conditions-start
  requires arr.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x :: 0 <= x < arr.Length && arr[x] == max
  // post-conditions-end
{
// impl-start
  var ind := arr.Length - 1;
  max := arr[ind];
  while ind > 0
    // invariants-start

    invariant 0 <= ind <= arr.Length
    invariant forall i: int :: ind <= i < arr.Length ==> arr[i] <= max
    invariant exists x :: 0 <= x < arr.Length && arr[x] == max
    // invariants-end

  {
    if arr[ind - 1] > max {
      max := arr[ind - 1];
    }
    ind := ind - 1;
  }
// impl-end
}

function sum(n: nat): nat
{
  if n == 0 then
    0
  else
    n + sum(n - 1)
}
// pure-end

method sumBackwards(n: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == sum(n)
  // post-conditions-end
{
// impl-start
  var i := n;
  r := 0;
  while i > 0
    // invariants-start

    invariant 0 <= i <= n
    invariant r == sum(n) - sum(i)
    // invariants-end

  {
    r := r + i;
    i := i - 1;
  }
// impl-end
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
