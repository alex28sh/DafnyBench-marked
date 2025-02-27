function sum(a: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j
{
  if i == j then
    0
  else
    a[j - 1] + sum(a, i, j - 1)
}
// pure-end

method query(a: array<int>, i: int, j: int)
    returns (s: int)
  // pre-conditions-start
  requires 0 <= i <= j <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures s == sum(a, i, j)
  // post-conditions-end
{
// impl-start
  s := 0;
  var aux := i;
  while aux < j
    // invariants-start

    invariant i <= aux <= j
    invariant s == sum(a, i, aux)
    decreases j - aux
    // invariants-end

  {
    s := s + a[aux];
    aux := aux + 1;
  }
  return s;
// impl-end
}

lemma queryLemma(a: array<int>, i: int, j: int, k: int)
  // pre-conditions-start
  requires 0 <= i <= k <= j <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
  // post-conditions-end
{
// impl-start
// impl-end
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int)
    returns (r: int)
  // pre-conditions-start
  requires is_prefix_sum_for(a, c) && 0 <= i <= j <= a.Length < c.Length
  // pre-conditions-end
  // post-conditions-start
  ensures r == sum(a, i, j)
  // post-conditions-end
{
// impl-start
  r := c[j] - c[i];
  // assert-start
  queryLemma(a, 0, j, i);
  // assert-end

  return r;
// impl-end
}

function is_prefix_sum_for(a: array<int>, c: array<int>): bool
  reads c, a
{
  a.Length + 1 == c.Length &&
  c[0] == 0 &&
  forall j :: 
    1 <= j <= a.Length ==>
      c[j] == sum(a, 0, j)
}
// pure-end

method from_array<T>(a: array<T>) returns (l: List<T>)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall j :: 0 <= j < a.Length ==> mem(a[j], l)
  // post-conditions-end
{
// impl-start
  var i := a.Length - 1;
  l := Nil;
  while i >= 0
    // invariants-start

    invariant -1 <= i < a.Length
    invariant forall j :: i + 1 <= j < a.Length ==> mem(a[j], l)
    // invariants-end

  {
    l := Cons(a[i], l);
    i := i - 1;
  }
  return l;
// impl-end
}

function mem<T(==)>(x: T, l: List<T>): bool
  decreases l
{
  match l
  case Nil =>
    false
  case Cons(y, r) =>
    if x == y then
      true
    else
      mem(x, r)
}
// pure-end

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
