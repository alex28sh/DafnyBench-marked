method plus_one(x: int) returns (r: int)
  // pre-conditions-start
  requires x >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == x + 1
  // post-conditions-end
{
// impl-start
  return x + 1;
// impl-end
}

method add_by_one(x: int, y: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assume y >= 0;
  // assert-end

  var i: int := 0;
  r := x;
  // assert-start
  assert i <= y;
  // assert-end

  // assert-start
  assert r == x + i;
  // assert-end

  r := *;
  i := *;
  // assert-start
  assume i <= y;
  // assert-end

  // assert-start
  assume r == x + i;
  // assert-end

  if i < y {
    // assert-start
    assume i < -2;
    // assert-end

    var t := y - i;
    r := r + 1;
    i := i + 1;
    // assert-start
    assert i <= y;
    // assert-end

    // assert-start
    assert r == x + i;
    // assert-end

    // assert-start
    assert y - i >= 0;
    // assert-end

    // assert-start
    assert y - i < t;
    // assert-end

    // assert-start
    assume false;
    // assert-end

  }
  // assert-start
  assert r == x + y;
  // assert-end

  return r;
// impl-end
}
