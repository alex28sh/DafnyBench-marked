// SiLemma_tmp_tmpfxtryv2w_utils.dfy


module Utils {
  lemma AllBelowBoundSize(bound: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures var below := set n: nat | n < bound :: n; |below| == bound
    decreases bound
    // post-conditions-end
  {
  // impl-start
    if bound == 0 {
    } else {
      AllBelowBoundSize(bound - 1);
      var belowminus := set n: nat | n < bound - 1 :: n;
      var below := set n: nat | n < bound :: n;
      assert below == belowminus + {bound - 1};
    }
  // impl-end
  }

  lemma SizeOfContainedSet(a: set<nat>, b: set<nat>)
    // pre-conditions-start
    requires forall n: nat :: n in a ==> n in b
    // pre-conditions-end
    // post-conditions-start
    ensures |a| <= |b|
    decreases |a|
    // post-conditions-end
  {
  // impl-start
    if |a| == 0 {
    } else {
      var y :| y in a;
      var new_a := a - {y};
      var new_b := b - {y};
      SizeOfContainedSet(new_a, new_b);
    }
  // impl-end
  }

  lemma BoundedSetSize(bound: nat, values: set<nat>)
    // pre-conditions-start
    requires forall n :: n in values ==> n < bound
    // pre-conditions-end
    // post-conditions-start
    ensures |values| <= bound
    // post-conditions-end
  {
  // impl-start
    var all_below_bound := set n: nat | n < bound :: n;
    AllBelowBoundSize(bound);
    assert |all_below_bound| == bound;
    assert forall n :: n in values ==> n in all_below_bound;
    SizeOfContainedSet(values, all_below_bound);
  // impl-end
  }

  lemma MappedSetSize<T, U>(s: set<T>, f: T -> U, t: set<U>)
    // pre-conditions-start
    requires forall n: T, m: T :: m != n ==> f(n) != f(m)
    requires t == set n | n in s :: f(n)
    // pre-conditions-end
    // post-conditions-start
    ensures |s| == |t|
    decreases |s|
    // post-conditions-end
  {
  // impl-start
    var t := set n | n in s :: f(n);
    if |s| == 0 {
    } else {
      var y :| y in s;
      var new_s := s - {y};
      var new_t := t - {f(y)};
      assert new_t == set n | n in new_s :: f(n);
      MappedSetSize(new_s, f, new_t);
    }
  // impl-end
  }

  lemma SetSizes<T>(a: set<T>, b: set<T>, c: set<T>)
    // pre-conditions-start
    requires c == a + b
    requires forall t: T :: t in a ==> t !in b
    requires forall t: T :: t in b ==> t !in a
    // pre-conditions-end
    // post-conditions-start
    ensures |c| == |a| + |b|
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }
}
