method LinearSeach0<T>(a: array<T>, P: T -> bool) returns (n: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  // post-conditions-end
{
// impl-start
  n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    // invariants-end

  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
// impl-end
}

function P(n: int): bool
{
  n % 2 == 0
}
// pure-end

method TestLinearSearch()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[3] [1, 2, 3];
  var n := LinearSeach1<int>(a, P);
  // assert-start
  assert n == 1 || n == 2 || n == 3 || n == 0;
  // assert-end

// impl-end
}

method LinearSeach1<T>(a: array<T>, P: T -> bool) returns (n: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
  // post-conditions-end
{
// impl-start
  n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !P(a[i])
    // invariants-end

  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
// impl-end
}
