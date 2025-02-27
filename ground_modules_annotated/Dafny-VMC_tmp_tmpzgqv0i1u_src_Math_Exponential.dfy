// Dafny-VMC_tmp_tmpzgqv0i1u_src_Math_Exponential.dfy


module Exponential {
  ghost function {:axiom} Exp(x: real): real
  // pure-end

  lemma {:axiom} FunctionalEquation(x: real, y: real)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Exp(x + y) == Exp(x) * Exp(y)
    // post-conditions-end

  lemma {:axiom} Increasing(x: real, y: real)
    // pre-conditions-start
    requires x < y
    // pre-conditions-end
    // post-conditions-start
    ensures Exp(x) < Exp(y)
    // post-conditions-end

  lemma {:axiom} EvalOne()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures 2.718281828 <= Exp(1.0) <= 2.718281829
    // post-conditions-end

  lemma Positive(x: real)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Exp(x) > 0.0
    // post-conditions-end
  {
  // impl-start
    assert Exp(x) >= 0.0 by {
      var sqrt := Exp(x / 2.0);
      calc {
        Exp(x);
        {
          FunctionalEquation(x / 2.0, x / 2.0);
        }
        sqrt * sqrt;
      >=
        0.0;
      }
    }
    if Exp(x) == 0.0 {
      calc {
        0.0;
        Exp(x);
      <
        {
          Increasing(x, x + 1.0);
        }
        Exp(x + 1.0);
        {
          FunctionalEquation(x, 1.0);
        }
        Exp(x) * Exp(1.0);
      ==
        0.0;
      }
    }
  // impl-end
  }

  lemma EvalZero()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Exp(0.0) == 1.0
    // post-conditions-end
  {
  // impl-start
    var one := Exp(0.0);
    assert one > 0.0 by {
      Positive(0.0);
    }
    assert one * one == one by {
      FunctionalEquation(0.0, 0.0);
    }
  // impl-end
  }
}
