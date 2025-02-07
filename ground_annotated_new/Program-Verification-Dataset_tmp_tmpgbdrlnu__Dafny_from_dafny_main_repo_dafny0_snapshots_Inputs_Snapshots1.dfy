method M()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  N();
  // assert-start
  assert false;
  // assert-end

// impl-end
}

method N()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures P()
  // post-conditions-end

function P(): bool
{
  false
}
// pure-end
