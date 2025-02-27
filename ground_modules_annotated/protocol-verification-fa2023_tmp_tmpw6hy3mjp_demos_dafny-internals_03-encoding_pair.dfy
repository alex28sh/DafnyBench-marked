// protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_dafny-internals_03-encoding_pair.dfy


module DafnyVersion {
  function pair_x(p: Pair): int
  {
    p.x
  }
  // pure-end

  function pair_y(p: Pair): int
  {
    p.y
  }
  // pure-end

  lemma UsePair()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert Pair(1, 2) != Pair(2, 1);
    var p := Pair(1, 2);
    assert pair_x(p) + pair_y(p) == 3;
    assert forall p1, p2 :: pair_x(p1) == pair_x(p2) && pair_y(p1) == pair_y(p2) ==> p1 == p2;
  // impl-end
  }

  datatype Pair = Pair(x: int, y: int)
}

module Encoding {
  function pair(x: int, y: int): Pair
  // pure-end

  function pair_x(p: Pair): int
  // pure-end

  function pair_y(p: Pair): int
  // pure-end

  lemma {:axiom} x_defn()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures forall x, y :: pair_x(pair(x, y)) == x
    // post-conditions-end

  lemma {:axiom} y_defn()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures forall x, y :: pair_y(pair(x, y)) == y
    // post-conditions-end

  lemma {:axiom} bijection()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures forall p: Pair :: pair(pair_x(p), pair_y(p)) == p
    // post-conditions-end

  lemma UseEncoding()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    x_defn();
    y_defn();
    bijection();
    assert pair(1, 2) != pair(2, 1) by {
      x_defn();
    }
    assert pair_y(pair(1, 2)) == 2 by {
      y_defn();
    }
    assert forall p1, p2 | pair_x(p1) == pair_x(p2) && pair_y(p1) == pair_y(p2) :: p1 == p2 by {
      bijection();
    }
  // impl-end
  }

  type Pair(==)
}
