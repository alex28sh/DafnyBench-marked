function f(x: int, y: int): int
// pure-end

lemma Associativity(x: int, y: int, z: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f(x, f(y, z)) == f(f(x, y), z)
  // post-conditions-end

lemma Monotonicity(y: int, z: int)
  // pre-conditions-start
  requires y <= z
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: f(x, y) <= f(x, z)
  // post-conditions-end

lemma DiagonalIdentity(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f(x, x) == x
  // post-conditions-end

method CalculationalStyleProof(a: int, b: int, c: int, x: int)
  // pre-conditions-start
  requires c <= x == f(a, b)
  // pre-conditions-end
  // post-conditions-start
  ensures f(a, f(b, c)) <= x
  // post-conditions-end
{
// impl-start
  calc {
    f(a, f(b, c));
  ==
    {
      Associativity(a, b, c);
    }
    f(f(a, b), c);
  ==
    {
      assert f(a, b) == x;
    }
    f(x, c);
  <=
    {
      assert c <= x;
      Monotonicity(c, x);
    }
    f(x, x);
  ==
    {
      DiagonalIdentity(x);
    }
    x;
  }
// impl-end
}

method DifferentStyleProof(a: int, b: int, c: int, x: int)
  // pre-conditions-start
  requires A: c <= x
  requires B: x == f(a, b)
  // pre-conditions-end
  // post-conditions-start
  ensures f(a, f(b, c)) <= x
  // post-conditions-end
{
// impl-start
  // assert-start
  assert 0: f(a, f(b, c)) == f(f(a, b), c) by {
    Associativity(a, b, c);
  }
  // assert-end

  // assert-start
  assert 1: f(f(a, b), c) == f(x, c) by {
    reveal B;
  }
  // assert-end

  // assert-start
  assert 2: f(x, c) <= f(x, x) by {
    assert c <= x by {
      reveal A;
    }
    Monotonicity(c, x);
  }
  // assert-end

  // assert-start
  assert 3: f(x, x) == x by {
    DiagonalIdentity(x);
  }
  // assert-end

  // assert-start
  assert 4: f(a, f(b, c)) == f(x, c) by {
    reveal 0, 1;
  }
  // assert-end

  // assert-start
  assert 5: f(x, c) <= x by {
    reveal 2, 3;
  }
  // assert-end

  // assert-start
  assert f(a, f(b, c)) <= x by {
    reveal 4, 5;
  }
  // assert-end

// impl-end
}
