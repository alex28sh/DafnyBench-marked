function length(iv: interval): int
{
  iv.1 - iv.0
}
// pure-end

function valid_interval(s: string, iv: interval): bool
{
  0 <= iv.0 <= iv.1 <= |s| &&
  forall i, j | iv.0 <= i < j < iv.1 :: 
    s[i] != s[j]
}
// pure-end

method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures valid_interval(s, best_iv) && length(best_iv) == n
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n
  // post-conditions-end
{
// impl-start
  var lo, hi := 0, 0;
  var char_set: set<char> := {};
  n, best_iv := 0, (0, 0);
  while hi < |s|
    // invariants-start

    invariant 0 <= lo <= hi <= |s|
    invariant valid_interval(s, (lo, hi))
    invariant char_set == set i | lo <= i < hi :: s[i]
    invariant valid_interval(s, best_iv) && length(best_iv) == n
    invariant forall iv: interval | iv.1 <= hi && valid_interval(s, iv) :: length(iv) <= n
    invariant forall iv: interval | iv.1 > hi && iv.0 < lo :: !valid_interval(s, iv)
    decreases |s| - hi, |s| - lo
    // invariants-end

  {
    if s[hi] !in char_set {
      char_set := char_set + {s[hi]};
      hi := hi + 1;
      if hi - lo > n {
        n := hi - lo;
        best_iv := (lo, hi);
      }
    } else {
      char_set := char_set - {s[lo]};
      lo := lo + 1;
    }
  }
// impl-end
}

method lengthOfLongestSubstring'(s: string) returns (n: int, ghost best_iv: interval)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures valid_interval(s, best_iv) && length(best_iv) == n
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n
  // post-conditions-end
{
// impl-start
  var lo, hi := 0, 0;
  var char_to_index: map<char, int> := map[];
  n, best_iv := 0, (0, 0);
  while |s| - lo > n
    // invariants-start

    invariant 0 <= lo <= hi <= |s|
    invariant valid_interval(s, (lo, hi))
    invariant forall i | 0 <= i < hi :: s[i] in char_to_index
    invariant forall c | c in char_to_index :: var i := char_to_index[c]; 0 <= i < hi && s[i] == c && forall i' | i < i' < hi :: s[i'] != c
    invariant valid_interval(s, best_iv) && length(best_iv) == n
    invariant forall iv: interval | iv.1 <= hi && valid_interval(s, iv) :: length(iv) <= n
    invariant forall iv: interval | iv.1 > hi && iv.0 < lo :: !valid_interval(s, iv)
    decreases |s| - hi
    // invariants-end

  {
    if s[hi] in char_to_index && char_to_index[s[hi]] >= lo {
      lo := char_to_index[s[hi]] + 1;
    }
    char_to_index := char_to_index[s[hi] := hi];
    hi := hi + 1;
    if hi - lo > n {
      n := hi - lo;
      best_iv := (lo, hi);
    }
  }
// impl-end
}

type interval = iv: (int, int)
  | iv.0 <= iv.1
  witness (0, 0)
