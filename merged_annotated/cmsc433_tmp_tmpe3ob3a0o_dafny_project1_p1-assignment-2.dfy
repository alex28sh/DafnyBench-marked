method PlusOne(x: int) returns (y: int)
  // pre-conditions-start
  requires x >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures y > 0
  // post-conditions-end
{
// impl-start
  y := x + 1;
// impl-end
}

method Swap(a: array?<int>, i: int, j: int)
  // pre-conditions-start
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  // post-conditions-end
{
// impl-start
  var tmp: int := a[i];
  a[i] := a[j];
  a[j] := a[i];
// impl-end
}

method IntDiv(m: int, n: int)
    returns (d: int, r: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures m == n * d + r && 0 <= r < n
  // post-conditions-end
{
// impl-start
  return m / n, m % n;
// impl-end
}

method ArraySum(a: array<int>, b: array<int>) returns (c: array<int>)
  // pre-conditions-start
  requires a.Length == b.Length
  // pre-conditions-end
  // post-conditions-start
  ensures c.Length == a.Length && forall i: int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
  // post-conditions-end
{
// impl-start
  c := new int[a.Length];
  var i: int := 0;
  while i < a.Length
    // invariants-start

    invariant i <= a.Length
    invariant forall j: int :: 0 <= j < i ==> c[j] == a[j] + b[j]
    // invariants-end

  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
// impl-end
}

method Euclid(m: int, n: int) returns (gcd: int)
  // pre-conditions-start
  requires m > 1 && n > 1 && m >= n
  // pre-conditions-end
  // post-conditions-start
  ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
  // post-conditions-end

method IsSorted(a: array<int>) returns (isSorted: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures isSorted <==> forall j: int :: 1 <= j < a.Length ==> a[j - 1] <= a[j]
  // post-conditions-end
{
// impl-start
  isSorted := true;
  var i: int := 1;
  if a.Length < 2 {
    return;
  } else {
    while i < a.Length
      // invariants-start

      invariant 1 <= i <= a.Length
      invariant isSorted <==> forall j: int :: 1 <= j < i ==> a[j - 1] <= a[j]
      // invariants-end

    {
      if a[i - 1] > a[i] {
        return false;
      }
      i := i + 1;
    }
  }
// impl-end
}

method IsPrime(m: int) returns (isPrime: bool)
  // pre-conditions-start
  requires m > 0
  // pre-conditions-end
  // post-conditions-start
  ensures isPrime <==> m > 1 && forall j: int :: 2 <= j < m ==> m % j != 0
  // post-conditions-end
{
// impl-start
  isPrime := true;
  if m <= 1 {
    isPrime := false;
  } else {
    var i: int := 2;
    while i < m
      // invariants-start

      invariant isPrime <==> forall j: int :: 2 <= j < i ==> m % j != 0
      // invariants-end

    {
      if m % i == 0 {
        isPrime := false;
        break;
      }
      i := i + 1;
    }
  }
// impl-end
}

method Reverse(a: array<int>) returns (aRev: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures aRev.Length == a.Length
  ensures forall i: int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length - i - 1]
  ensures fresh(aRev)
  // post-conditions-end
{
// impl-start
  aRev := new int[a.Length];
  var i: int := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j: int :: 0 <= j < i ==> aRev[j] == a[a.Length - j - 1]
    // invariants-end

  {
    aRev[i] := a[a.Length - i - 1];
    i := i + 1;
  }
// impl-end
}

method NoDups(a: array<int>) returns (noDups: bool)
  // pre-conditions-start
  requires forall j: int :: 0 < j < a.Length ==> a[j - 1] <= a[j]
  // pre-conditions-end
  // post-conditions-start
  ensures noDups <==> forall j: int :: 1 <= j < a.Length ==> a[j - 1] != a[j]
  // post-conditions-end
{
// impl-start
  noDups := true;
  var i: int := 1;
  if a.Length < 2 {
    return;
  }
  while i < a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant noDups <==> forall j: int :: 1 <= j < i ==> a[j - 1] != a[j]
    // invariants-end

  {
    if a[i - 1] == a[i] {
      noDups := false;
      break;
    }
    i := i + 1;
  }
// impl-end
}
