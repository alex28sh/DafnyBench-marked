
ghost predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
  decreases j - i
{
  j - i < 2 || (s[i] == s[j - 1] && palindromic(s, i + 1, j - 1))
}
// pure-end

lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  // pre-conditions-start
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s, lo, hi)
  // pre-conditions-end
  // post-conditions-start
  ensures palindromic(s, lo', hi')
  decreases lo' - lo
  // post-conditions-end
{
// impl-start
  if lo < lo' {
    lemma_palindromic_contains(s, lo + 1, hi - 1, lo', hi');
  }
// impl-end
}

method expand_from_center(s: string, i0: int, j0: int)
    returns (lo: int, hi: int)
  // pre-conditions-start
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 :: j - i <= hi - lo
  // post-conditions-end
{
// impl-start
  lo, hi := i0, j0;
  while lo - 1 >= 0 && hi < |s| && s[lo - 1] == s[hi]
    // invariants-start

    invariant 0 <= lo <= hi <= |s| && lo + hi == i0 + j0
    invariant palindromic(s, lo, hi)
    // invariants-end

  {
    lo, hi := lo - 1, hi + 1;
  }
  forall i, j | 0 <= i <= j <= |s| && i + j == i0 + j0 && j - i > hi - lo
    ensures !palindromic(s, i, j)
  {
    if palindromic(s, i, j) {
      // assert-start
      lemma_palindromic_contains(s, i, j, lo - 1, hi + 1);
      // assert-end

    }
  }
// impl-end
}

method longestPalindrome(s: string)
    returns (ans: string, lo: int, hi: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= lo <= hi <= |s| && ans == s[lo .. hi]
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
  // post-conditions-end
{
// impl-start
  lo, hi := 0, 0;
  for k := 0 to |s|
    // invariants-start

    invariant 0 <= lo <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant forall i, j | 0 <= i <= j <= |s| && i + j < 2 * k && palindromic(s, i, j) :: j - i <= hi - lo
    // invariants-end

  {
    var a, b := expand_from_center(s, k, k);
    if b - a > hi - lo {
      lo, hi := a, b;
    }
    var c, d := expand_from_center(s, k, k + 1);
    if d - c > hi - lo {
      lo, hi := c, d;
    }
  }
  return s[lo .. hi], lo, hi;
// impl-end
}

method {:vcs_split_on_every_assert} longestPalindrome'(s: string)
    returns (ans: string, lo: int, hi: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= lo <= hi <= |s| && ans == s[lo .. hi]
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
  // post-conditions-end
{
// impl-start
  var bogus: char :| true;
  var s' := insert_bogus_chars(s, bogus);
  var radii := new int[|s'|];
  var center, radius := 0, 0;
  ghost var loop_counter_outer, loop_counter_inner1, loop_counter_inner2 := 0, 0, 0;
  while center < |s'|
    // invariants-start

    invariant 0 <= center <= |s'|
    invariant forall c | 0 <= c < center :: max_radius(s', c, radii[c])
    invariant center < |s'| ==> inbound_radius(s', center, radius) && palindromic_radius(s', center, radius)
    invariant center == |s'| ==> radius == 0
    invariant loop_counter_outer <= center
    invariant loop_counter_inner1 <= center + radius && loop_counter_inner2 <= center
    // invariants-end

  {
    loop_counter_outer := loop_counter_outer + 1;
    while center - (radius + 1) >= 0 && center + (radius + 1) < |s'| && s'[center - (radius + 1)] == s'[center + (radius + 1)]
      // invariants-start

      invariant inbound_radius(s', center, radius) && palindromic_radius(s', center, radius)
      invariant loop_counter_inner1 <= center + radius
      decreases center - radius
      // invariants-end

    {
      loop_counter_inner1 := loop_counter_inner1 + 1;
      radius := radius + 1;
    }
    // assert-start
    lemma_end_of_expansion(s', center, radius);
    // assert-end

    radii[center] := radius;
    var old_center, old_radius := center, radius;
    center := center + 1;
    radius := 0;
    while center <= old_center + old_radius
      // invariants-start

      invariant 0 <= center <= |s'|
      invariant forall c | 0 <= c < center :: max_radius(s', c, radii[c])
      invariant center < |s'| ==> inbound_radius(s', center, radius) && palindromic_radius(s', center, radius)
      invariant loop_counter_inner2 <= center - 1
      // invariants-end

    {
      loop_counter_inner2 := loop_counter_inner2 + 1;
      var mirrored_center := old_center - (center - old_center);
      var max_mirrored_radius := old_center + old_radius - center;
      // assert-start
      lemma_mirrored_palindrome(s', old_center, old_radius, mirrored_center, radii[mirrored_center], center);
      // assert-end

      if radii[mirrored_center] < max_mirrored_radius {
        radii[center] := radii[mirrored_center];
        center := center + 1;
      } else if radii[mirrored_center] > max_mirrored_radius {
        radii[center] := max_mirrored_radius;
        center := center + 1;
      } else {
        radius := max_mirrored_radius;
        break;
      }
    }
  }
  // assert-start
  assert |s'| == 2 * |s| + 1;
  // assert-end

  // assert-start
  assert loop_counter_outer <= |s'|;
  // assert-end

  // assert-start
  assert loop_counter_inner1 <= |s'|;
  // assert-end

  // assert-start
  assert loop_counter_inner2 <= |s'|;
  // assert-end

  var (c, r) := argmax(radii, 0);
  lo, hi := (c - r) / 2, (c + r) / 2;
  // assert-start
  lemma_result_transfer(s, s', bogus, radii, c, r, hi, lo);
  // assert-end

  return s[lo .. hi], lo, hi;
// impl-end
}

function {:opaque} insert_bogus_chars(s: string, bogus: char): (s': string)
  ensures |s'| == 2 * |s| + 1
  ensures forall i | 0 <= i <= |s| :: s'[i * 2] == bogus
  ensures forall i | 0 <= i < |s| :: s'[i * 2 + 1] == s[i]
{
  if s == "" then
    [bogus]
  else
    var s'_old := insert_bogus_chars(s[1..], bogus); var s'_new := [bogus] + [s[0]] + s'_old; assert forall i | 1 <= i <= |s| :: s'_new[i * 2] == s'_old[(i - 1) * 2]; s'_new
}
// pure-end

function {:opaque} argmax(a: array<int>, start: int): (res: (int, int))
  requires 0 <= start < a.Length
  reads a
  ensures start <= res.0 < a.Length && a[res.0] == res.1
  ensures forall i | start <= i < a.Length :: a[i] <= res.1
  decreases a.Length - start
{
  if start == a.Length - 1 then
    (start, a[start])
  else
    var (i, v) := argmax(a, start + 1); if a[start] >= v then (start, a[start]) else (i, v)
}
// pure-end

ghost predicate inbound_radius(s': string, c: int, r: int)
{
  r >= 0 &&
  0 <= c - r &&
  c + r < |s'|
}
// pure-end

ghost predicate palindromic_radius(s': string, c: int, r: int)
  requires inbound_radius(s', c, r)
{
  palindromic(s', c - r, c + r + 1)
}
// pure-end

ghost predicate max_radius(s': string, c: int, r: int)
{
  inbound_radius(s', c, r) &&
  palindromic_radius(s', c, r) &&
  forall r' | r' > r && inbound_radius(s', c, r') :: 
    !palindromic_radius(s', c, r')
}
// pure-end

lemma lemma_palindromic_radius_contains(s': string, c: int, r: int, r': int)
  // pre-conditions-start
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires 0 <= r' <= r
  // pre-conditions-end
  // post-conditions-start
  ensures inbound_radius(s', c, r') && palindromic_radius(s', c, r')
  // post-conditions-end
{
// impl-start
  lemma_palindromic_contains(s', c - r, c + r + 1, c - r', c + r' + 1);
// impl-end
}

lemma lemma_end_of_expansion(s': string, c: int, r: int)
  // pre-conditions-start
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires inbound_radius(s', c, r + 1) ==> s'[c - (r + 1)] != s'[c + (r + 1)]
  // pre-conditions-end
  // post-conditions-start
  ensures max_radius(s', c, r)
  // post-conditions-end
{
// impl-start
  forall r' | r' > r && inbound_radius(s', c, r')
    ensures !palindromic_radius(s', c, r')
  {
    if palindromic_radius(s', c, r') {
      lemma_palindromic_radius_contains(s', c, r', r + 1);
    }
  }
// impl-end
}

lemma lemma_mirrored_palindrome(s': string, c: int, r: int, c1: int, r1: int, c2: int)
  // pre-conditions-start
  requires max_radius(s', c, r) && max_radius(s', c1, r1)
  requires c - r <= c1 < c < c2 <= c + r
  requires c2 - c == c - c1
  // pre-conditions-end
  // post-conditions-start
  ensures c2 + r1 < c + r ==> max_radius(s', c2, r1)
  ensures c2 + r1 > c + r ==> max_radius(s', c2, c + r - c2)
  ensures c2 + r1 == c + r ==> palindromic_radius(s', c2, c + r - c2)
  // post-conditions-end
{
// impl-start
  if c2 + r1 < c + r {
    for r2 := 0 to r1
      invariant palindromic_radius(s', c2, r2)
    {
      var r2' := r2 + 1;
      assert s'[c1 + r2'] == s'[c2 - r2'] by {
        lemma_palindromic_radius_contains(s', c, r, abs(c - c1 - r2'));
      }
      assert s'[c1 - r2'] == s'[c2 + r2'] by {
        lemma_palindromic_radius_contains(s', c, r, abs(c - c1 + r2'));
      }
      assert s'[c1 - r2'] == s'[c1 + r2'] by {
        lemma_palindromic_radius_contains(s', c1, r1, r2');
      }
    }
    var r2' := r1 + 1;
    assert s'[c1 + r2'] == s'[c2 - r2'] by {
      lemma_palindromic_radius_contains(s', c, r, abs(c - c1 - r2'));
    }
    assert s'[c1 - r2'] == s'[c2 + r2'] by {
      lemma_palindromic_radius_contains(s', c, r, abs(c - c1 + r2'));
    }
    assert s'[c1 - r2'] != s'[c1 + r2'] by {
      assert !palindromic_radius(s', c1, r2');
    }
    lemma_end_of_expansion(s', c2, r1);
  } else {
    for r2 := 0 to c + r - c2
      invariant palindromic_radius(s', c2, r2)
    {
      var r2' := r2 + 1;
      assert s'[c1 + r2'] == s'[c2 - r2'] by {
        lemma_palindromic_radius_contains(s', c, r, abs(c - c1 - r2'));
      }
      assert s'[c1 - r2'] == s'[c2 + r2'] by {
        lemma_palindromic_radius_contains(s', c, r, abs(c - c1 + r2'));
      }
      assert s'[c1 - r2'] == s'[c1 + r2'] by {
        lemma_palindromic_radius_contains(s', c1, r1, r2');
      }
    }
    if c2 + r1 > c + r {
      var r2' := c + r - c2 + 1;
      if inbound_radius(s', c, r + 1) {
        assert s'[c1 + r2'] == s'[c2 - r2'] by {
          lemma_palindromic_radius_contains(s', c, r, abs(c - c1 - r2'));
        }
        assert s'[c1 - r2'] != s'[c2 + r2'] by {
          assert !palindromic_radius(s', c, r + 1);
        }
        assert s'[c1 - r2'] == s'[c1 + r2'] by {
          lemma_palindromic_radius_contains(s', c1, r1, r2');
        }
        lemma_end_of_expansion(s', c2, c + r - c2);
      }
    }
  }
// impl-end
}

ghost function abs(x: int): int
{
  if x >= 0 then
    x
  else
    -x
}
// pure-end

lemma lemma_result_transfer(s: string, s': string, bogus: char, radii: array<int>, c: int, r: int, hi: int, lo: int)
  // pre-conditions-start
  requires s' == insert_bogus_chars(s, bogus)
  requires radii.Length == |s'|
  requires forall i | 0 <= i < radii.Length :: max_radius(s', i, radii[i])
  requires (c, r) == argmax(radii, 0)
  requires lo == (c - r) / 2 && hi == (c + r) / 2
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= lo <= hi <= |s|
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
  // post-conditions-end
{
// impl-start
  forall k | 0 <= k < radii.Length
    ensures max_interval_for_same_center(s, k, (k - radii[k]) / 2, (k + radii[k]) / 2)
  {
    if (k + radii[k]) % 2 == 1 {
      lemma_palindrome_bogus(s, s', bogus, k, radii[k]);
    }
    var lo, hi := (k - radii[k]) / 2, (k + radii[k]) / 2;
    lemma_palindrome_isomorph(s, s', bogus, lo, hi);
    forall i, j | 0 <= i <= j <= |s| && i + j == k && j - i > radii[k]
      ensures !palindromic(s, i, j)
    {
      lemma_palindrome_isomorph(s, s', bogus, i, j);
    }
  }
  for k := 0 to radii.Length - 1
    invariant forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j <= k :: j - i <= hi - lo
  {
    forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k + 1
      ensures j - i <= hi - lo
    {
      var k := k + 1;
      assert max_interval_for_same_center(s, k, (k - radii[k]) / 2, (k + radii[k]) / 2);
    }
  }
// impl-end
}

ghost predicate max_interval_for_same_center(s: string, k: int, lo: int, hi: int)
{
  0 <= lo <= hi <= |s| &&
  lo + hi == k &&
  palindromic(s, lo, hi) &&
  forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k :: 
    j - i <= hi - lo
}
// pure-end

lemma lemma_palindrome_isomorph(s: string, s': string, bogus: char, lo: int, hi: int)
  // pre-conditions-start
  requires s' == insert_bogus_chars(s, bogus)
  requires 0 <= lo <= hi <= |s|
  // pre-conditions-end
  // post-conditions-start
  ensures palindromic(s, lo, hi) <==> palindromic_radius(s', lo + hi, hi - lo)
  // post-conditions-end
{
// impl-start
  if palindromic(s, lo, hi) {
    for r := 0 to hi - lo
      invariant palindromic_radius(s', lo + hi, r)
    {
      if (lo + hi - r) % 2 == 1 {
        lemma_palindrome_bogus(s, s', bogus, lo + hi, r);
      } else {
        var i', j' := lo + hi - (r + 1), lo + hi + (r + 1);
        var i, j := i' / 2, j' / 2;
        assert s[i] == s[j] by {
          lemma_palindromic_contains(s, lo, hi, i, j + 1);
        }
      }
    }
  }
  if palindromic_radius(s', lo + hi, hi - lo) {
    var lo', hi' := lo, hi;
    while lo' + 1 <= hi' - 1
      invariant lo <= lo' <= hi' <= hi
      invariant lo' + hi' == lo + hi
      invariant palindromic_radius(s', lo + hi, hi' - lo')
      invariant palindromic(s, lo', hi') ==> palindromic(s, lo, hi)
    {
      assert palindromic_radius(s', lo + hi, hi' - lo' - 1);
      lo', hi' := lo' + 1, hi' - 1;
    }
  }
// impl-end
}

lemma lemma_palindrome_bogus(s: string, s': string, bogus: char, c: int, r: int)
  // pre-conditions-start
  requires s' == insert_bogus_chars(s, bogus)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires (c + r) % 2 == 1
  // pre-conditions-end
  // post-conditions-start
  ensures inbound_radius(s', c, r + 1) && palindromic_radius(s', c, r + 1)
  // post-conditions-end
{
// impl-start
  var left, right := c - (r + 1), c + (r + 1);
  assert left == left / 2 * 2;
  assert right == right / 2 * 2;
  assert s'[left] == s'[right] == bogus;
// impl-end
}
