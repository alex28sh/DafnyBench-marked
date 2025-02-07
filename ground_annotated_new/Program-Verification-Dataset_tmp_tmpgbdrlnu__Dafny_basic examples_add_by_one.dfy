method add_by_one(x: int, y: int) returns (r: int)
  // pre-conditions-start
  requires y >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == x + y
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  r := x;
  while i < y
    // invariants-start

    invariant i <= y
    invariant r == x + i
    decreases y - i
    // invariants-end

  {
    r := r + 1;
    i := i + 1;
  }
  return r;
// impl-end
}

method bar(x: int, y: int) returns (r: int)
  // pre-conditions-start
  requires y >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == x + y
  // post-conditions-end
{
// impl-start
  var i := 0;
  r := x;
  // assert-start
  assert i <= y && r == x + i;
  // assert-end

  // assert-start
  assert y - i >= 0;
  // assert-end

  i, r := *, *;
  // assert-start
  assume i <= y && r == x + i;
  // assert-end

  // assert-start
  assume y - i >= 0;
  // assert-end

  ghost var rank_before := y - i;
  if i < y {
    r := r + 1;
    i := i + 1;
    // assert-start
    assert i <= y && r == x + i;
    // assert-end

    // assert-start
    assert y - i >= 0;
    // assert-end

    // assert-start
    assert rank_before - (y - i) > 0;
    // assert-end

    // assert-start
    assume false;
    // assert-end

  }
  return r;
// impl-end
}
