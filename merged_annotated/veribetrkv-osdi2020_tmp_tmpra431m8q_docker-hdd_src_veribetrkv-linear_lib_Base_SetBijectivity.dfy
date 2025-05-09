// veribetrkv-osdi2020_tmp_tmpra431m8q_docker-hdd_src_veribetrkv-linear_lib_Base_SetBijectivity.dfy


module SetBijectivity {
  lemma BijectivityImpliesEqualCardinality<A, B>(setA: set<A>, setB: set<B>, relation: iset<(A, B)>)
    // pre-conditions-start
    requires forall a :: a in setA ==> exists b :: b in setB && (a, b) in relation
    requires forall a1, a2, b :: a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation ==> a1 == a2
    requires forall b :: b in setB ==> exists a :: a in setA && (a, b) in relation
    requires forall a, b1, b2 :: b1 in setB && b2 in setB && a in setA && (a, b1) in relation && (a, b2) in relation ==> b1 == b2
    // pre-conditions-end
    // post-conditions-start
    ensures |setA| == |setB|
    // post-conditions-end
  {
  // impl-start
    if |setA| == 0 {
    } else {
      var a :| a in setA;
      var b :| b in setB && (a, b) in relation;
      var setA' := setA - {a};
      var setB' := setB - {b};
      BijectivityImpliesEqualCardinality(setA', setB', relation);
    }
  // impl-end
  }

  lemma CrossProductCardinality<A, B>(setA: set<A>, setB: set<B>, cp: set<(A, B)>)
    // pre-conditions-start
    requires cp == set a, b | a in setA && b in setB :: (a, b)
    // pre-conditions-end
    // post-conditions-start
    ensures |cp| == |setA| * |setB|
    // post-conditions-end
  {
  // impl-start
    if |setA| == 0 {
      assert setA == {};
      assert cp == {};
    } else {
      var x :| x in setA;
      var setA' := setA - {x};
      var cp' := set a, b | a in setA' && b in setB :: (a, b);
      var line := set a, b | a == x && b in setB :: (a, b);
      assert |line| == |setB| by {
        var relation := iset p: ((A, B), B) | p.0.1 == p.1;
        forall b | b in setB
          ensures exists p :: p in line && (p, b) in relation
        {
          var p := (x, b);
          assert p in line && (p, b) in relation;
        }
        BijectivityImpliesEqualCardinality(line, setB, relation);
      }
      CrossProductCardinality(setA', setB, cp');
      assert cp == cp' + line;
      assert cp' !! line;
      assert |cp'| == |setA'| * |setB|;
      assert |setA'| == |setA| - 1;
      assert |cp| == |cp' + line| == |cp'| + |line| == (|setA| - 1) * |setB| + |setB| == |setA| * |setB|;
    }
  // impl-end
  }
}
