// eth2-dafny_tmp_tmpcrgexrgb_src_dafny_utils_SetHelpers.dfy


module SetHelpers {
  lemma interSmallest<T>(x: set<T>, y: set<T>)
    // pre-conditions-start
    requires x <= y
    // pre-conditions-end
    // post-conditions-start
    ensures x * y == x
    decreases y
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma unionCardBound(x: set<nat>, y: set<nat>, k: nat)
    // pre-conditions-start
    requires forall e :: e in x ==> e < k
    requires forall e :: e in y ==> e < k
    // pre-conditions-end
    // post-conditions-start
    ensures forall e :: e in x + y ==> e < k
    ensures |x + y| <= k
    // post-conditions-end
  {
  // impl-start
    natSetCardBound(x + y, k);
  // impl-end
  }

  lemma natSetCardBound(x: set<nat>, k: nat)
    // pre-conditions-start
    requires forall e :: e in x ==> e < k
    // pre-conditions-end
    // post-conditions-start
    ensures |x| <= k
    decreases k
    // post-conditions-end
  {
  // impl-start
    if k == 0 {
      assert x == {};
    } else {
      natSetCardBound(x - {k - 1}, k - 1);
    }
  // impl-end
  }

  lemma {:induction k} successiveNatSetCardBound(x: set<nat>, k: nat)
    // pre-conditions-start
    requires x == set x: nat | 0 <= x < k :: x
    // pre-conditions-end
    // post-conditions-start
    ensures |x| == k
    // post-conditions-end
  {
  // impl-start
    if k == 0 {
    } else {
      successiveNatSetCardBound(x - {k - 1}, k - 1);
    }
  // impl-end
  }

  lemma cardIsMonotonic<T>(x: set<T>, y: set<T>)
    // pre-conditions-start
    requires x <= y
    // pre-conditions-end
    // post-conditions-start
    ensures |x| <= |y|
    decreases y
    // post-conditions-end
  {
  // impl-start
    if |y| == 0 {
    } else {
      var e :| e in y;
      var y' := y - {e};
      cardIsMonotonic(if e in x then x - {e} else x, y');
    }
  // impl-end
  }

  lemma pigeonHolePrinciple<T>(x: set<T>, y: set<T>, z: set<T>)
    // pre-conditions-start
    requires x <= z
    requires y <= z
    requires |x| >= 2 * |z| / 3 + 1
    requires |y| >= 2 * |z| / 3 + 1
    // pre-conditions-end
    // post-conditions-start
    ensures |x * y| >= |z| / 3 + 1
    // post-conditions-end
  {
  // impl-start
    assert |x| >= 2 * |z| / 3 + 1 <==> 2 * |z| < 3 * |x|;
    assert |y| >= 2 * |z| / 3 + 1 <==> 2 * |z| < 3 * |y|;
    if |x * y| < |z| / 3 + 1 {
      calc == {
        |x + y|;
        |x| + |y| - |x * y|;
      }
      cardIsMonotonic(x + y, z);
    }
    assert 3 * |x * y| > |z| <==> |x * y| >= |z| / 3 + 1;
  // impl-end
  }
}
