function divides(f: nat, i: nat): bool
  requires 1 <= f
{
  i % f == 0
}
// pure-end

function IsPrime(i: nat): bool
{
  1 < i &&
  forall f :: 
    1 < f < i ==>
      !divides(f, i)
}
// pure-end

method test_prime(i: nat) returns (result: bool)
  // pre-conditions-start
  requires 1 < i
  // pre-conditions-end
  // post-conditions-start
  ensures result == IsPrime(i)
  // post-conditions-end
{
// impl-start
  var f := 2;
  while f < i
    // invariants-start

    invariant forall g :: 1 < g < f ==> !divides(g, i)
    // invariants-end

  {
    if i % f == 0 {
      // assert-start
      assert divides(f, i);
      // assert-end

      return false;
    }
    f := f + 1;
  }
  return true;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := test_prime(3);
  // assert-start
  assert a;
  // assert-end

  var b := test_prime(4);
  // assert-start
  assert divides(2, 4);
  // assert-end

  // assert-start
  assert !b;
  // assert-end

  var c := test_prime(5);
  // assert-start
  assert c;
  // assert-end

// impl-end
}
