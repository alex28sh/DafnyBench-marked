function {:opaque} P(x: int): bool
// pure-end

method test(y: int)
  // pre-conditions-start
  requires forall x :: P(x)
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert P(y);
  // assert-end

// impl-end
}
