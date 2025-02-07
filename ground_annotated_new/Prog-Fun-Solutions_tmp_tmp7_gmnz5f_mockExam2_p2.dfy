method problem2(p: int, q: int, X: int, Y: int)
    returns (r: int, s: int)
  // pre-conditions-start
  requires p == 2 * X + Y && q == X + 3
  // pre-conditions-end
  // post-conditions-start
  ensures r == X && s == Y
  // post-conditions-end
{
// impl-start
  // assert-start
  assert p == 2 * X + Y && q == X + 3;
  // assert-end

  r, s := p, q;
  // assert-start
  assert r == 2 * X + Y && s == X + 3;
  // assert-end

  r := r - 2 * s + 6;
  // assert-start
  assert r == 2 * X + Y - 2 * X - 6 + 6 && s == X + 3;
  // assert-end

  // assert-start
  assert r == Y && s == X + 3;
  // assert-end

  s := s - 3;
  // assert-start
  assert r == Y && s == X;
  // assert-end

  r, s := s, r;
  // assert-start
  assert s == Y && r == X;
  // assert-end

// impl-end
}
