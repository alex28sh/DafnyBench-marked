method IsPerfectSquare(n: int) returns (result: bool)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == true ==> exists i: int :: 0 <= i <= n && i * i == n
  ensures result == false ==> forall a: int :: 0 < a * a < n ==> a * a != n
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i * i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> k * k < n
    // invariants-end

  {
    i := i + 1;
  }
  return i * i == n;
// impl-end
}
