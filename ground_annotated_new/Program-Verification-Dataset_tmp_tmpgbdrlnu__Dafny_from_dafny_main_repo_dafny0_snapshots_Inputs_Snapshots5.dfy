method M()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  N();
  if * {
  } else {
    // assert-start
    assert (forall b: bool :: b || !b) || 0 != 0;
    // assert-end

  }
  N();
  // assert-start
  assert (forall b: bool :: b || !b) || 3 != 3;
  // assert-end

  if * {
  } else {
    // assert-start
    assert (forall b: bool :: b || !b) || 1 != 1;
    // assert-end

  }
// impl-end
}

method N()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (forall b: bool :: b || !b) || 2 != 2
  // post-conditions-end
