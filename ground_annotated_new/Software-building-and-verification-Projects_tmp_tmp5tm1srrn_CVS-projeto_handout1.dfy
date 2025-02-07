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
    returns (res: int)
  // pre-conditions-start
  requires 0 <= i <= j <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures res == sum(a, i, j)
  // post-conditions-end
{
// impl-start
  res := 0;
  var ind := j - 1;
  while ind >= i
    // invariants-start

    invariant i - 1 <= ind < j
    invariant res == sum(a, i, j) - sum(a, i, ind + 1)
    decreases ind
    // invariants-end

  {
    res := res + a[ind];
    ind := ind - 1;
  }
// impl-end
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int)
    returns (r: int)
  // pre-conditions-start
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c)
  // pre-conditions-end
  // post-conditions-start
  ensures r == sum(a, i, j)
  // post-conditions-end
{
// impl-start
  var k := i;
  // assert-start
  proof(a, 0, j, k);
  // assert-end

  r := c[j] - c[i];
// impl-end
}

function is_prefix_sum_for(a: array<int>, c: array<int>): bool
  reads c, a
{
  a.Length + 1 == c.Length &&
  forall i: int :: 
    0 <= i <= a.Length ==>
      c[i] == sum(a, 0, i)
}
// pure-end

lemma proof(a: array<int>, i: int, j: int, k: int)
  // pre-conditions-start
  requires 0 <= i <= k <= j <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
  // post-conditions-end

method from_array<T>(a: array<T>) returns (l: List<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
  // post-conditions-end
{
// impl-start
  l := Nil;
  var i := a.Length - 1;
  while i >= 0
    // invariants-start

    invariant 0 <= i + 1 <= a.Length
    invariant forall j: int :: i < j < a.Length ==> mem(a[j], l)
    invariant forall x: T :: mem(x, l) ==> exists y: int :: i + 1 <= y < a.Length && a[y] == x
    decreases i
    // invariants-end

  {
    l := Cons(a[i], l);
    i := i - 1;
  }
// impl-end
}

function mem<T(==)>(x: T, l: List<T>): bool
{
  match l
  case Nil =>
    false
  case Cons(h, t) =>
    h == x || mem(x, t)
}
// pure-end

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
