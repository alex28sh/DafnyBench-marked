// veribetrkv-osdi2020_tmp_tmpra431m8q_docker-hdd_src_veribetrkv-linear_lib_Base_Sets.dfy


module Sets {
  lemma {:opaque} ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    // pre-conditions-start
    requires a < b
    // pre-conditions-end
    // post-conditions-start
    ensures |a| < |b|
    // post-conditions-end
  {
  // impl-start
    assert |b| == |a| + |b - a|;
  // impl-end
  }

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    // pre-conditions-start
    requires a <= b
    // pre-conditions-end
    // post-conditions-start
    ensures |a| <= |b|
    // post-conditions-end
  {
  // impl-start
    assert b == a + (b - a);
  // impl-end
  }

  lemma {:opaque} SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    // pre-conditions-start
    requires a < b
    // pre-conditions-end
    // post-conditions-start
    ensures |a| < |b|
    // post-conditions-end
  {
  // impl-start
    assert b == a + (b - a);
  // impl-end
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    // pre-conditions-start
    requires a <= b
    requires |a| == |b|
    // pre-conditions-end
    // post-conditions-start
    ensures a == b
    // post-conditions-end
  {
  // impl-start
    assert b == a + (b - a);
  // impl-end
  }

  function SetRange(n: int): set<int>
  {
    set i | 0 <= i < n
  }
  // pure-end

  lemma CardinalitySetRange(n: int)
    // pre-conditions-start
    requires n >= 0
    // pre-conditions-end
    // post-conditions-start
    ensures |SetRange(n)| == n
    // post-conditions-end
  {
  // impl-start
    if n == 0 {
    } else {
      CardinalitySetRange(n - 1);
      assert SetRange(n) == SetRange(n - 1) + {n - 1};
    }
  // impl-end
  }
}
