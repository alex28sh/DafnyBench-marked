function P(x: int): bool
// pure-end

method M(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert true || forall x: int | P(x) :: P(x + 1);
  // assert-end

  // assert-start
  assert true || forall x: int | P(x + 1) :: P(x);
  // assert-end

// impl-end
}
