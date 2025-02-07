function Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|
{
  if s == t then
    0
  else
    Count(a, s, t - 1, x) + if a[t - 1] == x then 1 else 0
}
// pure-end

function HasMajority<T>(a: seq<T>, s: int, t: int, x: T): bool
  requires 0 <= s <= t <= |a|
{
  2 * Count(a, s, t, x) > t - s
}
// pure-end

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  // pre-conditions-start
  requires HasMajority(a, 0, |a|, K)
  // pre-conditions-end
  // post-conditions-start
  ensures k == K
  // post-conditions-end
{
// impl-start
  k := a[0];
  var n, c, s := 1, 1, 0;
  while n < |a|
    // invariants-start
    invariant 0 <= s <= n <= |a|
    invariant 2 * Count(a, s, |a|, K) > |a| - s
    invariant 2 * Count(a, s, n, k) > n - s
    invariant c == Count(a, s, n, k)
    // invariants-end
  {
    if a[n] == k {
      n, c := n + 1, c + 1;
    } else if 2 * c > n + 1 - s {
      n := n + 1;
    } else {
      n := n + 1;
      Lemma_Unique(a, s, n, K, k);
      Lemma_Split(a, s, n, |a|, K);
      k, n, c, s := a[n], n + 1, 1, n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);
// impl-end
}

method DetermineElection<Candidate(==,0,!new)>(a: seq<Candidate>) returns (result: Result<Candidate>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result.Winner? ==> 2 * Count(a, 0, |a|, result.cand) > |a|
  ensures result.NoWinner? ==> forall c :: 2 * Count(a, 0, |a|, c) <= |a|
  // post-conditions-end
{
// impl-start
  if |a| == 0 {
    return NoWinner;
  }
  ghost var b := exists c :: 2 * Count(a, 0, |a|, c) > |a|;
  ghost var w :| b ==> 2 * Count(a, 0, |a|, w) > |a|;
  var cand := SearchForWinner(a, b, w);
  return if 2 * Count(a, 0, |a|, cand) > |a| then Winner(cand) else NoWinner;
// impl-end
}

method SearchForWinner<Candidate(==)>(a: seq<Candidate>, ghost hasWinner: bool, ghost K: Candidate)
    returns (k: Candidate)
  // pre-conditions-start
  requires |a| != 0
  requires hasWinner ==> 2 * Count(a, 0, |a|, K) > |a|
  // pre-conditions-end
  // post-conditions-start
  ensures hasWinner ==> k == K
  // post-conditions-end
{
// impl-start
  k := a[0];
  var n, c, s := 1, 1, 0;
  while n < |a|
    // invariants-start
    invariant 0 <= s <= n <= |a|
    invariant hasWinner ==> 2 * Count(a, s, |a|, K) > |a| - s
    invariant 2 * Count(a, s, n, k) > n - s
    invariant c == Count(a, s, n, k)
    // invariants-end
  {
    if a[n] == k {
      n, c := n + 1, c + 1;
    } else if 2 * c > n + 1 - s {
      n := n + 1;
    } else {
      n := n + 1;
      Lemma_Unique(a, s, n, K, k);
      Lemma_Split(a, s, n, |a|, K);
      if |a| == n {
        return;
      }
      k, n, c, s := a[n], n + 1, 1, n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);
// impl-end
}

lemma Lemma_Split<T>(a: seq<T>, s: int, t: int, u: int, x: T)
  // pre-conditions-start
  requires 0 <= s <= t <= u <= |a|
  // pre-conditions-end
  // post-conditions-start
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma Lemma_Unique<T>(a: seq<T>, s: int, t: int, x: T, y: T)
  // pre-conditions-start
  requires 0 <= s <= t <= |a|
  // pre-conditions-end
  // post-conditions-start
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s
  // post-conditions-end
{
// impl-start
// impl-end
}

method FindWinner'<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  // pre-conditions-start
  requires HasMajority(a, 0, |a|, K)
  // pre-conditions-end
  // post-conditions-start
  ensures k == K
  // post-conditions-end
{
// impl-start
  k := a[0];
  var lo, up, c := 0, 1, 1;
  while up < |a|
    // invariants-start
    invariant 0 <= lo < up <= |a|
    invariant HasMajority(a, lo, |a|, K)
    invariant HasMajority(a, lo, up, k)
    invariant c == Count(a, lo, up, k)
    // invariants-end
  {
    if a[up] == k {
      up, c := up + 1, c + 1;
    } else if 2 * c > up + 1 - lo {
      up := up + 1;
    } else {
      calc {
        true;
      ==
        2 * c <= up + 1 - lo;
      ==
        2 * Count(a, lo, up, k) <= up + 1 - lo;
      ==
        calc {
          true;
        ==
          HasMajority(a, lo, up, k);
        ==
          2 * Count(a, lo, up, k) > up - lo;
        ==
          2 * Count(a, lo, up, k) >= up + 1 - lo;
        }
        2 * Count(a, lo, up, k) == up + 1 - lo;
      }
      up := up + 1;
      // assert-start
      assert 2 * Count(a, lo, up, k) == up - lo;
      // assert-end

      calc {
        2 * Count(a, up, |a|, K);
      ==
        {
          Lemma_Split(a, lo, up, |a|, K);
        }
        2 * Count(a, lo, |a|, K) - 2 * Count(a, lo, up, K);
      >
        {
          assert HasMajority(a, lo, |a|, K);
        }
        |a| - lo - 2 * Count(a, lo, up, K);
      >=
        {
          if k == K {
            calc {
              2 * Count(a, lo, up, K);
            ==
              2 * Count(a, lo, up, k);
            ==
              {
                assert 2 * Count(a, lo, up, k) == up - lo;
              }
              up - lo;
            }
          } else {
            calc {
              2 * Count(a, lo, up, K);
            <=
              {
                Lemma_Unique(a, lo, up, k, K);
              }
              2 * (up - lo - Count(a, lo, up, k));
            ==
              {
                assert 2 * Count(a, lo, up, k) == up - lo;
              }
              up - lo;
            }
          }
          assert 2 * Count(a, lo, up, K) <= up - lo;
        }
        |a| - lo - (up - lo);
      ==
        |a| - up;
      }
      // assert-start
      assert HasMajority(a, up, |a|, K);
      // assert-end

      k, lo, up, c := a[up], up, up + 1, 1;
      // assert-start
      assert HasMajority(a, lo, |a|, K);
      // assert-end

    }
  }
  Lemma_Unique(a, lo, |a|, K, k);
// impl-end
}

method FindWinner''<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  // pre-conditions-start
  requires HasMajority(a, 0, |a|, K)
  // pre-conditions-end
  // post-conditions-start
  ensures k == K
  // post-conditions-end
{
// impl-start
  k := a[0];
  var lo, up, c := 0, 1, 1;
  while up < |a|
    // invariants-start
    invariant 0 <= lo < up <= |a|
    invariant HasMajority(a, lo, |a|, K)
    invariant HasMajority(a, lo, up, k)
    invariant c == Count(a, lo, up, k)
    // invariants-end
  {
    if a[up] == k {
      up, c := up + 1, c + 1;
    } else if 2 * c > up + 1 - lo {
      up := up + 1;
    } else {
      calc {
        true;
      ==
        2 * c <= up + 1 - lo;
      ==
        2 * Count(a, lo, up, k) <= up + 1 - lo;
      ==
        calc {
          true;
        ==
          HasMajority(a, lo, up, k);
        ==
          2 * Count(a, lo, up, k) > up - lo;
        ==
          2 * Count(a, lo, up, k) >= up + 1 - lo;
        }
        2 * Count(a, lo, up, k) == up + 1 - lo;
      }
      up := up + 1;
      // assert-start
      assert 2 * Count(a, lo, up, k) == up - lo;
      // assert-end

      calc {
        true;
      ==
        HasMajority(a, lo, |a|, K);
      ==
        2 * Count(a, lo, |a|, K) > |a| - lo;
      ==
        {
          Lemma_Split(a, lo, up, |a|, K);
        }
        2 * Count(a, lo, up, K) + 2 * Count(a, up, |a|, K) > |a| - lo;
      ==>
        {
          if k == K {
            calc {
              2 * Count(a, lo, up, K);
            ==
              2 * Count(a, lo, up, k);
            ==
              {
                assert 2 * Count(a, lo, up, k) == up - lo;
              }
              up - lo;
            }
          } else {
            calc {
              true;
            ==
              {
                Lemma_Unique(a, lo, up, k, K);
              }
              Count(a, lo, up, K) + Count(a, lo, up, k) <= up - lo;
            ==
              2 * Count(a, lo, up, K) + 2 * Count(a, lo, up, k) <= 2 * (up - lo);
            ==
              {
                assert 2 * Count(a, lo, up, k) == up - lo;
              }
              2 * Count(a, lo, up, K) <= up - lo;
            }
          }
          assert 2 * Count(a, lo, up, K) <= up - lo;
        }
        2 * Count(a, up, |a|, K) > |a| - lo - (up - lo);
      ==
        2 * Count(a, up, |a|, K) > |a| - up;
      ==
        HasMajority(a, up, |a|, K);
      }
      k, lo, up, c := a[up], up, up + 1, 1;
      // assert-start
      assert HasMajority(a, lo, |a|, K);
      // assert-end

    }
  }
  Lemma_Unique(a, lo, |a|, K, k);
// impl-end
}

datatype Result<Candidate> = NoWinner | Winner(cand: Candidate)
