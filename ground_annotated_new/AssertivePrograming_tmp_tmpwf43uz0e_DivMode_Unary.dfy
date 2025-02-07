function UnaryToNat(x: Unary): nat
{
  match x
  case Zero =>
    0
  case Suc(x') =>
    1 + UnaryToNat(x')
}
// pure-end

function NatToUnary(n: nat): Unary
{
  if n == 0 then
    Zero
  else
    Suc(NatToUnary(n - 1))
}
// pure-end

lemma NatUnaryCorrespondence(n: nat, x: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures UnaryToNat(NatToUnary(n)) == n
  ensures NatToUnary(UnaryToNat(x)) == x
  // post-conditions-end
{
// impl-start
// impl-end
}

function Less(x: Unary, y: Unary): bool
{
  y != Zero &&
  (x.Suc? ==>
    Less(x.pred, y.pred))
}
// pure-end

function LessAlt(x: Unary, y: Unary): bool
{
  y != Zero &&
  (x == Zero || Less(x.pred, y.pred))
}
// pure-end

lemma LessSame(x: Unary, y: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Less(x, y) == LessAlt(x, y)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma LessCorrect(x: Unary, y: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  // pre-conditions-start
  requires Less(x, y) && Less(y, z)
  // pre-conditions-end
  // post-conditions-start
  ensures Less(x, z)
  // post-conditions-end
{
// impl-start
// impl-end
}

function Add(x: Unary, y: Unary): Unary
{
  match y
  case Zero =>
    x
  case Suc(y') =>
    Suc(Add(x, y'))
}
// pure-end

lemma {:induction false} SucAdd(x: Unary, y: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Suc(Add(x, y)) == Add(Suc(x), y)
  // post-conditions-end
{
// impl-start
  match y
  case {:split false} Zero =>
  case {:split false} Suc(y') =>
    calc {
      Suc(Add(x, Suc(y')));
    ==
      Suc(Suc(Add(x, y')));
    ==
      {
        SucAdd(x, y');
      }
      Suc(Add(Suc(x), y'));
    ==
      Add(Suc(x), Suc(y'));
    }
// impl-end
}

lemma {:induction false} AddZero(x: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Zero, x) == x
  // post-conditions-end
{
// impl-start
  match x
  case {:split false} Zero =>
  case {:split false} Suc(x') =>
    calc {
      Add(Zero, Suc(x'));
    ==
      Suc(Add(Zero, x'));
    ==
      {
        AddZero(x');
      }
      Suc(x');
    }
// impl-end
}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{
  match y
  case Zero =>
    x
  case Suc(y') =>
    Sub(x.pred, y')
}
// pure-end

function Mul(x: Unary, y: Unary): Unary
{
  match x
  case Zero =>
    Zero
  case Suc(x') =>
    Add(Mul(x', y), y)
}
// pure-end

lemma SubStructurallySmaller(x: Unary, y: Unary)
  // pre-conditions-start
  requires !Less(x, y) && y != Zero
  // pre-conditions-end
  // post-conditions-start
  ensures Sub(x, y) < x
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AddSub(x: Unary, y: Unary)
  // pre-conditions-start
  requires !Less(x, y)
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Sub(x, y), y) == x
  // post-conditions-end
{
// impl-start
// impl-end
}

method {:verify false} IterativeDivMod'(x: Unary, y: Unary)
    returns (d: Unary, m: Unary)
  // pre-conditions-start
  requires y != Zero
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Mul(d, y), m) == x && Less(m, y)
  // post-conditions-end
{
// impl-start
  if Less(x, y) {
    d := Zero;
    m := x;
  } else {
    var x0: Unary := x;
    d := Zero;
    while !Less(x0, y)
      // invariants-start

      invariant Add(Mul(d, y), x0) == x
      decreases x0
      // invariants-end

    {
      d := Suc(d);
      x0 := Sub(x0, y);
    }
    m := x0;
  }
// impl-end
}

method IterativeDivMod(x: Unary, y: Unary)
    returns (d: Unary, m: Unary)
  // pre-conditions-start
  requires y != Zero
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Mul(d, y), m) == x && Less(m, y)
  // post-conditions-end
{
// impl-start
  if Less(x, y) {
    // assert-start
    assert Less(x, y);
    // assert-end

    // assert-start
    AddZero(x);
    // assert-end

    // assert-start
    assert Add(Zero, x) == x;
    // assert-end

    // assert-start
    assert Mul(Zero, y) == Zero;
    // assert-end

    // assert-start
    assert Add(Mul(Zero, y), x) == x;
    // assert-end

    d := Zero;
    m := x;
    // assert-start
    assert Add(Mul(d, y), m) == m;
    // assert-end

    // assert-start
    assert Less(m, y);
    // assert-end

    // assert-start
    assert Add(Mul(d, y), m) == x && Less(m, y);
    // assert-end

  } else {
    // assert-start
    assert !Less(x, y);
    // assert-end

    // assert-start
    assert y != Zero;
    // assert-end

    var x0: Unary := x;
    // assert-start
    assert Mul(Zero, y) == Zero;
    // assert-end

    d := Zero;
    // assert-start
    assert Mul(d, y) == Zero;
    // assert-end

    // assert-start
    AddZero(x);
    // assert-end

    // assert-start
    assert Add(Zero, x) == x;
    // assert-end

    // assert-start
    assert Add(Mul(d, y), x) == x;
    // assert-end

    // assert-start
    assert Add(Mul(d, y), x0) == x;
    // assert-end

    while !Less(x0, y)
      // invariants-start

      invariant Add(Mul(d, y), x0) == x
      decreases x0
      // invariants-end

    {
      // assert-start
      assert Add(Mul(d, y), x0) == x;
      // assert-end

      // assert-start
      assert !Less(x0, y);
      // assert-end

      // assert-start
      assert y != Zero;
      // assert-end

      // assert-start
      AddMulSucSubEqAddMul(d, y, x0);
      // assert-end

      // assert-start
      assert Add(Mul(Suc(d), y), Sub(x0, y)) == Add(Mul(d, y), x0);
      // assert-end

      // assert-start
      assert Add(Mul(Suc(d), y), Sub(x0, y)) == x;
      // assert-end

      d := Suc(d);
      // assert-start
      assert !Less(x0, y) && y != Zero;
      // assert-end

      // assert-start
      SubStructurallySmaller(x0, y);
      // assert-end

      // assert-start
      assert Sub(x0, y) < x0;
      // assert-end

      x0 := Sub(x0, y);
      // assert-start
      assert Add(Mul(d, y), x0) == x;
      // assert-end

    }
    // assert-start
    assert Add(Mul(d, y), x0) == x;
    // assert-end

    m := x0;
    // assert-start
    assert Add(Mul(d, y), m) == x;
    // assert-end

  }
  // assert-start
  assert Add(Mul(d, y), m) == x;
  // assert-end

// impl-end
}

lemma AddMulEqMulSuc(a: Unary, b: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Mul(Suc(a), b) == Add(Mul(a, b), b)
  // post-conditions-end
{
// impl-start
  calc {
    Mul(Suc(a), b);
  ==
    Add(Mul(a, b), b);
  }
// impl-end
}

lemma AddMulSucSubEqAddMul(d: Unary, y: Unary, x0: Unary)
  // pre-conditions-start
  requires !Less(x0, y)
  requires y != Zero
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Mul(Suc(d), y), Sub(x0, y)) == Add(Mul(d, y), x0)
  // post-conditions-end
{
// impl-start
  calc {
    Add(Mul(Suc(d), y), Sub(x0, y));
  ==
    {
      AddMulEqMulSuc(d, y);
      assert Mul(Suc(d), y) == Add(Mul(d, y), y);
    }
    Add(Add(Mul(d, y), y), Sub(x0, y));
  ==
    {
      AddTransitive(Mul(d, y), y, Sub(x0, y));
      assert Add(Mul(d, y), Add(y, Sub(x0, y))) == Add(Add(Mul(d, y), y), Sub(x0, y));
    }
    Add(Mul(d, y), Add(y, Sub(x0, y)));
  ==
    {
      AddCommutative(Sub(x0, y), y);
      assert Add(Sub(x0, y), y) == Add(y, Sub(x0, y));
    }
    Add(Mul(d, y), Add(Sub(x0, y), y));
  ==
    {
      assert !Less(x0, y);
      AddSub(x0, y);
      assert Add(Sub(x0, y), y) == x0;
    }
    Add(Mul(d, y), x0);
  }
// impl-end
}

lemma AddTransitive(a: Unary, b: Unary, c: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(a, Add(b, c)) == Add(Add(a, b), c)
  // post-conditions-end
{
// impl-start
  match c
  case {:split false} Zero =>
    calc {
      Add(a, Add(b, c));
    ==
      Add(a, Add(b, Zero));
    ==
      Add(a, b);
    ==
      Add(Add(a, b), Zero);
    ==
      Add(Add(a, b), c);
    }
  case {:split false} Suc(c') =>
    match b
    case {:split false} Zero =>
      calc {
        Add(a, Add(b, c));
      ==
        Add(a, Add(Zero, Suc(c')));
      ==
        {
          AddZero(Suc(c'));
          assert Add(Zero, Suc(c')) == Suc(c');
        }
        Add(a, Suc(c'));
      ==
        Add(Add(a, Zero), Suc(c'));
      ==
        Add(Add(a, b), Suc(c'));
      ==
        Add(Add(a, b), c);
      }
    case {:split false} Suc(b') =>
      match a
      case {:split false} Zero =>
        calc {
          Add(a, Add(b, c));
        ==
          Add(Zero, Add(Suc(b'), Suc(c')));
        ==
          {
            AddZero(Add(Suc(b'), Suc(c')));
            assert Add(Zero, Add(Suc(b'), Suc(c'))) == Add(Suc(b'), Suc(c'));
          }
          Add(Suc(b'), Suc(c'));
        ==
          {
            AddZero(Suc(b'));
            assert Add(Zero, Suc(b')) == Suc(b');
          }
          Add(Add(Zero, Suc(b')), Suc(c'));
        ==
          Add(Add(a, b), c);
        }
      case {:split false} Suc(a') =>
        calc {
          Add(a, Add(b, c));
        ==
          Add(Suc(a'), Add(Suc(b'), Suc(c')));
        ==
          Add(Suc(a'), Suc(Add(Suc(b'), c')));
        ==
          Suc(Add(Suc(a'), Add(Suc(b'), c')));
        ==
          {
            SucAdd(a', Add(Suc(b'), c'));
            assert Suc(Add(a', Add(Suc(b'), c'))) == Add(Suc(a'), Add(Suc(b'), c'));
          }
          Suc(Suc(Add(a', Add(Suc(b'), c'))));
        ==
          {
            SucAdd(b', c');
            assert Suc(Add(b', c')) == Add(Suc(b'), c');
          }
          Suc(Suc(Add(a', Suc(Add(b', c')))));
        ==
          Suc(Suc(Suc(Add(a', Add(b', c')))));
        ==
          {
            AddTransitive(a', b', c');
            assert Add(a', Add(b', c')) == Add(Add(a', b'), c');
          }
          Suc(Suc(Suc(Add(Add(a', b'), c'))));
        ==
          Suc(Suc(Add(Add(a', b'), Suc(c'))));
        ==
          {
            SucAdd(Add(a', b'), Suc(c'));
            assert Suc(Add(Add(a', b'), Suc(c'))) == Add(Suc(Add(a', b')), Suc(c'));
          }
          Suc(Add(Suc(Add(a', b')), Suc(c')));
        ==
          {
            SucAdd(a', b');
            assert Suc(Add(a', b')) == Add(Suc(a'), b');
          }
          Suc(Add(Add(Suc(a'), b'), Suc(c')));
        ==
          {
            SucAdd(Add(Suc(a'), b'), Suc(c'));
            assert Suc(Add(Add(Suc(a'), b'), Suc(c'))) == Add(Suc(Add(Suc(a'), b')), Suc(c'));
          }
          Add(Suc(Add(Suc(a'), b')), Suc(c'));
        ==
          Add(Add(Suc(a'), Suc(b')), Suc(c'));
        ==
          Add(Add(a, b), c);
        }
// impl-end
}

lemma AddCommutative(a: Unary, b: Unary)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(a, b) == Add(b, a)
  // post-conditions-end
{
// impl-start
  match b
  case {:split false} Zero =>
    calc {
      Add(a, b);
    ==
      Add(a, Zero);
    ==
      a;
    ==
      {
        AddZero(a);
        assert Add(Zero, a) == a;
      }
      Add(Zero, a);
    ==
      Add(b, a);
    }
  case {:split false} Suc(b') =>
    calc {
      Add(a, b);
    ==
      Add(a, Suc(b'));
    ==
      Suc(Add(a, b'));
    ==
      {
        AddCommutative(a, b');
        assert Add(a, b') == Add(b', a);
      }
      Suc(Add(b', a));
    ==
      {
        SucAdd(b', a);
        assert Suc(Add(b', a)) == Add(Suc(b'), a);
      }
      Add(Suc(b'), a);
    ==
      Add(b, a);
    }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var U3 := Suc(Suc(Suc(Zero)));
  // assert-start
  assert UnaryToNat(U3) == 3;
  // assert-end

  var U7 := Suc(Suc(Suc(Suc(U3))));
  // assert-start
  assert UnaryToNat(U7) == 7;
  // assert-end

  var d, m := IterativeDivMod(U7, U3);
  // assert-start
  assert Add(Mul(d, U3), m) == U7 && Less(m, U3);
  // assert-end

  print "Just as 7 divided by 3 is 2 with a remainder of 1, IterativeDivMod(", U7, ", ", U3, ") is ", d, " with a remainder of ", m;
// impl-end
}

datatype Unary = Zero | Suc(pred: Unary)
