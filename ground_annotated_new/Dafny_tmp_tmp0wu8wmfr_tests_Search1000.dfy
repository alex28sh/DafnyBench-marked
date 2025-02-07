method Search1000(a: array<int>, x: int) returns (k: int)
  // pre-conditions-start
  requires a.Length >= 1000
  requires forall p, q | 0 <= p < q < 1000 :: a[p] <= a[q]
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= k <= 1000
  ensures forall r | 0 <= r < k :: a[r] < x
  ensures forall r | k <= r < 1000 :: a[r] >= x
  // post-conditions-end
{
// impl-start
  k := 0;
  if a[500] < x {
    k := 489;
  }
  if a[k + 255] < x {
    k := k + 256;
  }
  if a[k + 127] < x {
    k := k + 128;
  }
  if a[k + 63] < x {
    k := k + 64;
  }
  if a[k + 31] < x {
    k := k + 32;
  }
  if a[k + 15] < x {
    k := k + 16;
  }
  if a[k + 7] < x {
    k := k + 8;
  }
  if a[k + 3] < x {
    k := k + 4;
  }
  if a[k + 1] < x {
    k := k + 2;
  }
  if a[k] < x {
    k := k + 1;
  }
// impl-end
}

function Is2Pow(n: int): bool
  decreases n
{
  if n < 1 then
    false
  else if n == 1 then
    true
  else
    n % 2 == 0 && Is2Pow(n / 2)
}
// pure-end

method Search2PowLoop(a: array<int>, i: int, n: int, x: int)
    returns (k: int)
  // pre-conditions-start
  requires 0 <= i <= i + n <= a.Length
  requires forall p, q | i <= p < q < i + n :: a[p] <= a[q]
  requires Is2Pow(n + 1)
  // pre-conditions-end
  // post-conditions-start
  ensures i <= k <= i + n
  ensures forall r | i <= r < k :: a[r] < x
  ensures forall r | k <= r < i + n :: a[r] >= x
  // post-conditions-end
{
// impl-start
  k := i;
  var c := n;
  while c != 0
    // invariants-start

    invariant Is2Pow(c + 1)
    invariant i <= k <= k + c <= i + n
    invariant forall r | i <= r < k :: a[r] < x
    invariant forall r | k + c <= r < i + n :: a[r] >= x
    decreases c
    // invariants-end

  {
    c := c / 2;
    if a[k + c] < x {
      k := k + c + 1;
    }
  }
// impl-end
}

method Search2PowRecursive(a: array<int>, i: int, n: int, x: int)
    returns (k: int)
  // pre-conditions-start
  requires 0 <= i <= i + n <= a.Length
  requires forall p, q | i <= p < q < i + n :: a[p] <= a[q]
  requires Is2Pow(n + 1)
  // pre-conditions-end
  // post-conditions-start
  ensures i <= k <= i + n
  ensures forall r | i <= r < k :: a[r] < x
  ensures forall r | k <= r < i + n :: a[r] >= x
  decreases n
  // post-conditions-end
{
// impl-start
  if n == 0 {
    return i;
  }
  if a[i + n / 2] < x {
    k := Search2PowRecursive(a, i + n / 2 + 1, n / 2, x);
  } else {
    k := Search2PowRecursive(a, i, n / 2, x);
  }
// impl-end
}
