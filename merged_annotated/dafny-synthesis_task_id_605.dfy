method IsPrime(n: int) returns (result: bool)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> forall k :: 2 <= k < n ==> n % k != 0
  // post-conditions-end
{
// impl-start
  result := true;
  var i := 2;
  while i <= n / 2
    // invariants-start

    invariant 2 <= i
    invariant result <==> forall k :: 2 <= k < i ==> n % k != 0
    // invariants-end

  {
    if n % i == 0 {
      result := false;
      break;
    }
    i := i + 1;
  }
// impl-end
}
