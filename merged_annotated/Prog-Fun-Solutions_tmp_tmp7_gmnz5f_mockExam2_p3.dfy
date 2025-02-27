method problem3(m: int, X: int) returns (r: int)
  // pre-conditions-start
  requires X >= 0 && (2 * m == 1 - X || m == X + 3)
  // pre-conditions-end
  // post-conditions-start
  ensures r == X
  // post-conditions-end
{
// impl-start
  // assert-start
  assert X >= 0 && (X == 1 - 2 * m || m - 3 == X);
  // assert-end

  r := m;
  // assert-start
  assert X >= 0 && (1 - 2 * r >= 0 || r - 3 >= 0);
  // assert-end

  if 1 - 2 * r >= 0 {
    // assert-start
    assert X >= 0 && 2 * r == 1 - X;
    // assert-end

    r := 2 * r;
    // assert-start
    assert X >= 0 && r == 1 - X;
    // assert-end

    r := -r + 1;
  } else {
    // assert-start
    assert r == X + 3;
    // assert-end

    r := r - 3;
  }
  // assert-start
  assert r == X;
  // assert-end

// impl-end
}
