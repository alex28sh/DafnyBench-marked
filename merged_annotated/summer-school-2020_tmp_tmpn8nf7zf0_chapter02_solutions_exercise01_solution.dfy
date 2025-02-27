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

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert !IsPrime(0);
  // assert-end

  // assert-start
  assert !IsPrime(1);
  // assert-end

  // assert-start
  assert IsPrime(2);
  // assert-end

  // assert-start
  assert IsPrime(3);
  // assert-end

  // assert-start
  assert divides(2, 6);
  // assert-end

  // assert-start
  assert !IsPrime(6);
  // assert-end

  // assert-start
  assert IsPrime(7);
  // assert-end

  // assert-start
  assert divides(3, 9);
  // assert-end

  // assert-start
  assert !IsPrime(9);
  // assert-end

// impl-end
}
