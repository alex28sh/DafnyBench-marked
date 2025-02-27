
function sum(a: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j - i
{
  if i == j then
    0
  else
    a[i] + sum(a, i + 1, j)
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
  var k := i;
  while k < j
    // invariants-start

    invariant i <= k <= j <= a.Length
    invariant res + sum(a, k, j) == sum(a, i, j)
    // invariants-end

  {
    res := res + a[k];
    k := k + 1;
  }
// impl-end
}

predicate is_prefix_sum_for(a: array<int>, c: array<int>)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  reads c, a
{
  forall i: int :: 
    0 <= i < a.Length ==>
      c[i + 1] == c[i] + a[i]
}
// pure-end

lemma aux(a: array<int>, c: array<int>, i: int, j: int)
  // pre-conditions-start
  requires 0 <= i <= j <= a.Length
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  requires is_prefix_sum_for(a, c)
  // pre-conditions-end
  // post-conditions-start
  ensures forall k: int :: i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k]
  decreases j - i
  // post-conditions-end
{
// impl-start
// impl-end
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int)
    returns (r: int)
  // pre-conditions-start
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c)
  // pre-conditions-end
  // post-conditions-start
  ensures r == sum(a, i, j)
  // post-conditions-end
{
// impl-start
  // assert-start
  aux(a, c, i, j);
  // assert-end

  r := c[j] - c[i];
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x := new int[10];
  x[0], x[1], x[2], x[3] := 2, 2, 1, 5;
  var y := sum(x, 0, x.Length);
  var c := new int[11];
  c[0], c[1], c[2], c[3], c[4] := 0, 2, 4, 5, 10;
// impl-end
}
