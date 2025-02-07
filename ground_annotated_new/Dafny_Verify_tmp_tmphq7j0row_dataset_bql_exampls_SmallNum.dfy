method add_small_numbers(a: array<int>, n: int, max: int)
    returns (r: int)
  // pre-conditions-start
  requires n > 0
  requires n <= a.Length
  requires forall i: int :: 0 <= i && i < n ==> a[i] <= max
  // pre-conditions-end
  // post-conditions-start
  ensures r <= max * n
  // post-conditions-end
{
// impl-start
  var i: int;
  i := 0;
  r := 0;
  while i < n
    // invariants-start

    invariant i <= n
    invariant r <= max * i
    // invariants-end

  {
    r := r + a[i];
    i := i + 1;
  }
// impl-end
}
