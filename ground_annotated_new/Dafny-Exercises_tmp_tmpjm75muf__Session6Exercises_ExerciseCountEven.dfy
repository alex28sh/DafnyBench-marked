function positive(s: seq<int>): bool
{
  forall u :: 
    0 <= u < |s| ==>
      s[u] >= 0
}
// pure-end

function isEven(i: int): bool
  requires i >= 0
{
  i % 2 == 0
}
// pure-end

function CountEven(s: seq<int>): int
  requires positive(s)
  decreases s
{
  if s == [] then
    0
  else
    (if s[|s| - 1] % 2 == 0 then 1 else 0) + CountEven(s[..|s| - 1])
}
// pure-end

lemma ArrayFacts<T>()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall v: array<T> :: v[..v.Length] == v[..]
  ensures forall v: array<T> :: v[0..] == v[..]
  ensures forall v: array<T> :: v[0 .. v.Length] == v[..]
  ensures forall v: array<T> :: |v[0 .. v.Length]| == v.Length
  ensures forall v: array<T> | v.Length >= 1 :: |v[1 .. v.Length]| == v.Length - 1
  ensures forall v: array<T> :: forall k: nat | k < v.Length :: v[..k + 1][..k] == v[..k]
  // post-conditions-end
{
// impl-start
// impl-end
}

method mcountEven(v: array<int>) returns (n: int)
  // pre-conditions-start
  requires positive(v[..])
  // pre-conditions-end
  // post-conditions-start
  ensures n == CountEven(v[..])
  // post-conditions-end
{
// impl-start
  // assert-start
  ArrayFacts<int>();
  // assert-end

  n := 0;
  var i: int;
  i := 0;
  while i < v.Length
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant n == CountEven(v[..i])
    decreases v.Length - i
    // invariants-end

  {
    if v[i] % 2 == 0 {
      n := n + 1;
    }
    i := i + 1;
  }
// impl-end
}
