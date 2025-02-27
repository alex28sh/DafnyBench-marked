lemma max(a: int, b: int) returns (m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures m >= a
  ensures m >= b
  ensures m == a || m == b
  // post-conditions-end
{
// impl-start
  if a > b {
    m := a;
  } else {
    m := b;
  }
// impl-end
}

function post_max(a: int, b: int, m: int): bool
{
  m >= a &&
  m >= b &&
  (m == a || m == b)
}
// pure-end

lemma post_max_point_1(a: int, b: int, m: int)
  // pre-conditions-start
  requires a > b
  requires m != a
  // pre-conditions-end
  // post-conditions-start
  ensures !post_max(a, b, m)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_point_1'(a: int, b: int, m: int)
  // pre-conditions-start
  requires a > b
  requires post_max(a, b, m)
  // pre-conditions-end
  // post-conditions-start
  ensures m == a
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_point_2(a: int, b: int, m: int)
  // pre-conditions-start
  requires a == b
  requires m != a || m != b
  // pre-conditions-end
  // post-conditions-start
  ensures !post_max(a, b, m)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_point_3(a: int, b: int, m: int)
  // pre-conditions-start
  requires a < b
  requires m != b
  // pre-conditions-end
  // post-conditions-start
  ensures !post_max(a, b, m)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_vertical_1(a: int, b: int, m: int)
  // pre-conditions-start
  requires m != a && m != b
  // pre-conditions-end
  // post-conditions-start
  ensures !post_max(a, b, m)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_vertical_1'(a: int, b: int, m: int)
  // pre-conditions-start
  requires post_max(a, b, m)
  // pre-conditions-end
  // post-conditions-start
  ensures m == a || m == b
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_realistic_1(a: int, b: int, m: int)
  // pre-conditions-start
  requires a > b
  requires m == a
  // pre-conditions-end
  // post-conditions-start
  ensures post_max(a, b, m)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_realistic_2(a: int, b: int, m: int)
  // pre-conditions-start
  requires a < b
  requires m == b
  // pre-conditions-end
  // post-conditions-start
  ensures post_max(a, b, m)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma post_max_realistic_3(a: int, b: int, m: int)
  // pre-conditions-start
  requires a == b
  requires m == a
  // pre-conditions-end
  // post-conditions-start
  ensures post_max(a, b, m)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma max_deterministic(a: int, b: int, m: int, m': int)
  // pre-conditions-start
  requires post_max(a, b, m)
  requires post_max(a, b, m')
  // pre-conditions-end
  // post-conditions-start
  ensures m == m'
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma max_deterministic'(a: int, b: int, m: int, m': int)
  // pre-conditions-start
  requires m != m'
  // pre-conditions-end
  // post-conditions-start
  ensures !post_max(a, b, m) || !post_max(a, b, m')
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper<T>(s: seq<int>, b: int, i: nat)
  // pre-conditions-start
  requires |s| > i
  requires b == s[i]
  // pre-conditions-end
  // post-conditions-start
  ensures s[..i] + [b] == s[..i + 1]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma multisetEquality(m1: multiset<int>, m2: multiset<int>, m3: multiset<int>, m4: multiset<int>)
  // pre-conditions-start
  requires m1 > m2 + m3
  requires m1 == m2 + m4
  // pre-conditions-end
  // post-conditions-start
  ensures m3 < m4
  // post-conditions-end
{
// impl-start
  assert m3 < m1 - m2;
// impl-end
}
