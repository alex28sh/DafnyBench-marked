function {:opaque} f(x: int): int
{
  x
}
// pure-end

lemma L()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x: int :: f(x) == x
  // post-conditions-end
{
// impl-start
  forall x: int | true
    ensures f(x) == x
  {
    reveal f();
  }
  assert forall x: int :: f(x) == x;
// impl-end
}
