function P(x: int): bool
// pure-end

function Q(x: int): bool
// pure-end

method test()
  // pre-conditions-start
  requires forall x {:trigger P(x)} :: P(x) && Q(x)
  // pre-conditions-end
  // post-conditions-start
  ensures Q(0)
  // post-conditions-end
{
// impl-start
  // assert-start
  assert P(0);
  // assert-end

// impl-end
}
