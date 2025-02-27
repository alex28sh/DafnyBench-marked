function strictNegative(v: array<int>, i: int, j: int): bool
  requires 0 <= i <= j <= v.Length
  reads v
{
  forall u | i <= u < j :: 
    v[u] < 0
}
// pure-end

function positive(s: seq<int>): bool
{
  forall u :: 
    0 <= u < |s| ==>
      s[u] >= 0
}
// pure-end

function isPermutation(s: seq<int>, t: seq<int>): bool
{
  multiset(s) == multiset(t)
}
// pure-end

method separate(v: array<int>) returns (i: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies v
  ensures 0 <= i <= v.Length
  ensures positive(v[0 .. i]) && strictNegative(v, i, v.Length)
  ensures isPermutation(v[0 .. v.Length], old(v[0 .. v.Length]))
  // post-conditions-end
{
// impl-start
  i := 0;
  var j := v.Length - 1;
  while i <= j
    // invariants-start

    invariant 0 <= i <= j + 1 <= v.Length
    invariant strictNegative(v, j + 1, v.Length)
    invariant positive(v[0 .. i])
    invariant isPermutation(v[0 .. v.Length], old(v[0 .. v.Length]))
    decreases j - i
    // invariants-end

  {
    if v[i] >= 0 {
      i := i + 1;
    } else if v[j] >= 0 {
      // assert-start
      assert v[i] < 0;
      // assert-end

      v[i], v[j] := v[j], v[i];
      j := j - 1;
      i := i + 1;
    } else if v[j] < 0 {
      j := j - 1;
    }
  }
// impl-end
}
