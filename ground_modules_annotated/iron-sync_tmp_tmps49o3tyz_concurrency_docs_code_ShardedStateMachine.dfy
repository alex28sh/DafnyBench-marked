// iron-sync_tmp_tmps49o3tyz_concurrency_docs_code_ShardedStateMachine.dfy


abstract module ShardedStateMachine {
  predicate valid_shard(a: Shard)
  // pure-end

  function glue(a: Shard, b: Shard): Shard
  // pure-end

  lemma glue_commutative(a: Shard, b: Shard)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures glue(a, b) == glue(b, a)
    // post-conditions-end

  lemma glue_associative(a: Shard, b: Shard, c: Shard)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures glue(glue(a, b), c) == glue(a, glue(b, c))
    // post-conditions-end

  function unit(): Shard
    ensures valid_shard(unit())
  // pure-end

  lemma glue_unit(a: Shard)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures glue(a, unit()) == a
    // post-conditions-end

  predicate Inv(s: Shard)
  // pure-end

  predicate Next(shard: Shard, shard': Shard)
  // pure-end

  lemma NextPreservesValid(s: Shard, s': Shard)
    // pre-conditions-start
    requires valid_shard(s)
    requires Next(s, s')
    // pre-conditions-end
    // post-conditions-start
    ensures valid_shard(s')
    // post-conditions-end

  lemma NextAdditive(s: Shard, s': Shard, t: Shard)
    // pre-conditions-start
    requires Next(s, s')
    requires valid_shard(glue(s, t))
    requires Next(glue(s, t), glue(s', t))
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end

  lemma NextPreservesInv(s: Shard, s': Shard)
    // pre-conditions-start
    requires Inv(s)
    requires Next(s, s')
    // pre-conditions-end
    // post-conditions-start
    ensures Inv(s')
    // post-conditions-end

  type Shard
}
