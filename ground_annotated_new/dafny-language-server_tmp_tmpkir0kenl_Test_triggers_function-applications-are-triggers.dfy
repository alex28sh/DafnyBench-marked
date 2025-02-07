method M(P: (int -> int) -> bool, g: int -> int)
  // pre-conditions-start
  requires P.requires(g)
  requires P(g)
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assume forall f: int -> int :: P.requires(f);
  // assert-end

  // assert-start
  assume forall f: int -> int :: P(f) ==> f.requires(10) && f(10) == 0;
  // assert-end

  // assert-start
  assert forall f: int -> int :: (forall x :: f.requires(x) && g.requires(x) ==> f(x) == g(x)) ==> f.requires(10) ==> f(10) == 0;
  // assert-end

// impl-end
}
