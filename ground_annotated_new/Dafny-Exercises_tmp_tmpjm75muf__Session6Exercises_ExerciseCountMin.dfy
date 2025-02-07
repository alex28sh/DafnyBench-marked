function min(v: array<int>, i: int): int
  requires 1 <= i <= v.Length
  reads v
  ensures forall k :: 0 <= k < i ==> v[k] >= min(v, i)
  decreases i
{
  if i == 1 then
    v[0]
  else if v[i - 1] <= min(v, i - 1) then
    v[i - 1]
  else
    min(v, i - 1)
}
// pure-end

function countMin(v: array<int>, x: int, i: int): int
  requires 0 <= i <= v.Length
  reads v
  ensures !(x in v[0 .. i]) ==> countMin(v, x, i) == 0
  decreases i
{
  if i == 0 then
    0
  else if v[i - 1] == x then
    1 + countMin(v, x, i - 1)
  else
    countMin(v, x, i - 1)
}
// pure-end

method mCountMin(v: array<int>) returns (c: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures c == countMin(v, min(v, v.Length), v.Length)
  // post-conditions-end
{
// impl-start
  var i := 1;
  c := 1;
  var mini := v[0];
  while i < v.Length
    // invariants-start

    invariant 0 < i <= v.Length
    invariant mini == min(v, i)
    invariant c == countMin(v, mini, i)
    decreases v.Length - i
    // invariants-end

  {
    if v[i] == mini {
      c := c + 1;
    } else if v[i] < mini {
      c := 1;
      mini := v[i];
    }
    i := i + 1;
  }
// impl-end
}
