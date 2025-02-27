function SomaAte(a: array<nat>, i: nat): nat
  requires 0 <= i <= a.Length
  reads a
{
  if i == 0 then
    0
  else
    a[i - 1] + SomaAte(a, i - 1)
}
// pure-end

method Somatorio(a: array<nat>) returns (s: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == SomaAte(a, a.Length)
  // post-conditions-end
{
// impl-start
  var i := 0;
  s := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i && i <= a.Length
    invariant s == SomaAte(a, i)
    // invariants-end

  {
    s := s + a[i];
    i := i + 1;
  }
// impl-end
}
