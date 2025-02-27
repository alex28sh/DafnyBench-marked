method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x - 10 else 91
  // post-conditions-end
{
// impl-start
  var y1 := x;
  var y2 := 1;
  while true
    // invariants-start

    invariant proveFunctionalPostcondition ==> 100 < x ==> y1 == x
    invariant proveFunctionalPostcondition ==> x <= 100 < y1 && y2 == 1 ==> y1 == 101
    invariant (y1 <= 111 && y2 >= 1) || (y1 == x && y2 == 1)
    decreases -2 * y1 + 21 * y2 + 2 * if x < 111 then 111 else x
    // invariants-end

  {
    if y1 > 100 {
      if y2 == 1 {
        break;
      } else {
        y1 := y1 - 10;
        y2 := y2 - 1;
      }
    } else {
      y1 := y1 + 11;
      y2 := y2 + 1;
    }
  }
  z := y1 - 10;
// impl-end
}

method Gcd(x1: int, x2: int)
  // pre-conditions-start
  requires 1 <= x1 && 1 <= x2
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var y1 := x1;
  var y2 := x2;
  while y1 != y2
    // invariants-start

    invariant 1 <= y1 && 1 <= y2
    decreases y1 + y2
    // invariants-end

  {
    while y1 > y2
      // invariants-start

      invariant 1 <= y1 && 1 <= y2
      // invariants-end

    {
      y1 := y1 - y2;
    }
    while y2 > y1
      // invariants-start

      invariant 1 <= y1 && 1 <= y2
      // invariants-end

    {
      y2 := y2 - y1;
    }
  }
// impl-end
}

method Determinant(X: array2<int>, M: int) returns (z: int)
  // pre-conditions-start
  requires 1 <= M
  requires X != null && M == X.Length0 && M == X.Length1
  // pre-conditions-end
  // post-conditions-start
  modifies X
  // post-conditions-end
{
// impl-start
  var y := X[1 - 1, 1 - 1];
  var a := 1;
  while a != M
    // invariants-start

    invariant 1 <= a <= M
    // invariants-end

  {
    var b := a + 1;
    while b != M + 1
      // invariants-start

      invariant a + 1 <= b <= M + 1
      // invariants-end

    {
      var c := M;
      while c != a
        // invariants-start

        invariant a <= c <= M
        // invariants-end

      {
        // assert-start
        assume X[a - 1, a - 1] != 0;
        // assert-end

        X[b - 1, c - 1] := X[b - 1, c - 1] - X[b - 1, a - 1] / X[a - 1, a - 1] * X[a - 1, c - 1];
        c := c - 1;
      }
      b := b + 1;
    }
    a := a + 1;
    y := y * X[a - 1, a - 1];
  }
  z := y;
// impl-end
}
