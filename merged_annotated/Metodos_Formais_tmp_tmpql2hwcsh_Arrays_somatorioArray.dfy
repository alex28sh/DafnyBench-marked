function soma(a: array<nat>, i: nat): nat
  requires i <= a.Length
  reads a
{
  if i == 0 then
    0
  else
    a[i - 1] + soma(a, i - 1)
}
// pure-end

method somatorio(a: array<nat>) returns (s: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == soma(a, a.Length)
  // post-conditions-end
{
// impl-start
  s := 0;
  for i := 0 to a.Length
    // invariants-start

    invariant s == soma(a, i)
    // invariants-end

  {
    s := s + a[i];
  }
// impl-end
}
