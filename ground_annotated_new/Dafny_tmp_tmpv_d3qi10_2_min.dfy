function min(a: int, b: int): int
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
{
  if a < b then
    a
  else
    b
}
// pure-end

method minMethod(a: int, b: int) returns (c: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c <= a && c <= b
  ensures c == a || c == b
  ensures c == min(a, b)
  // post-conditions-end
{
// impl-start
  if a < b {
    c := a;
  } else {
    c := b;
  }
// impl-end
}

function minFunction(a: int, b: int): int
  ensures minFunction(a, b) <= a && minFunction(a, b) <= b
  ensures minFunction(a, b) == a || minFunction(a, b) == b
{
  if a < b then
    a
  else
    b
}
// pure-end

method minArray(a: array<int>) returns (m: int)
  // pre-conditions-start
  requires a != null && a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall k | 0 <= k < a.Length :: m <= a[k]
  ensures exists k | 0 <= k < a.Length :: m == a[k]
  // post-conditions-end
{
// impl-start
  m := a[0];
  var i := 1;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall k | 0 <= k < i :: m <= a[k]
    invariant exists k | 0 <= k < i :: m == a[k]
    // invariants-end

  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var integer := min(1, 2);
  print integer;
// impl-end
}
