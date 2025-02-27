method Ceiling7(n: nat) returns (k: nat)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures k == n - n % 7
  // post-conditions-end
{
// impl-start
  k := n - n % 7;
// impl-end
}

method test7()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var k: nat;
  k := Ceiling7(43);
  // assert-start
  assert k == 42;
  // assert-end

  k := Ceiling7(6);
  // assert-start
  assert k == 0;
  // assert-end

  k := Ceiling7(1000);
  // assert-start
  assert k == 994;
  // assert-end

  k := Ceiling7(7);
  // assert-start
  assert k == 7;
  // assert-end

  k := Ceiling7(70);
  // assert-start
  assert k == 70;
  // assert-end

// impl-end
}
