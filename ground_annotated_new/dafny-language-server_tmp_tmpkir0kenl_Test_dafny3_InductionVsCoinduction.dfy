function Up(n: int): Stream<int>
{
  SCons(n, Up(n + 1))
}
// pure-end

function FivesUp(n: int): Stream<int>
  decreases 4 - (n - 1) % 5
{
  if n % 5 == 0 then
    SCons(n, FivesUp(n + 1))
  else
    FivesUp(n + 1)
}
// pure-end

greatest predicate Pos(s: Stream<int>)
{
  match s
  case SNil =>
    true
  case SCons(x, rest) =>
    x > 0 &&
    Pos(rest)
}
// pure-end

function SAppend(xs: Stream, ys: Stream): Stream
{
  match xs
  case SNil =>
    ys
  case SCons(x, rest) =>
    SCons(x, SAppend(rest, ys))
}
// pure-end

lemma {:induction false} SAppendIsAssociativeK(k: nat, a: Stream, b: Stream, c: Stream)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c))
  decreases k
  // post-conditions-end
{
// impl-start
  match a {
    case {:split false} SNil =>
    case {:split false} SCons(h, t) =>
      if k > 0 {
        SAppendIsAssociativeK(k - 1, t, b, c);
      }
  }
// impl-end
}

lemma SAppendIsAssociative(a: Stream, b: Stream, c: Stream)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c))
  // post-conditions-end
{
// impl-start
  forall k: nat | true {
    SAppendIsAssociativeK(k, a, b, c);
  }
  assert forall k: nat {:autotriggers false} :: SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c));
// impl-end
}

greatest lemma {:induction false} SAppendIsAssociativeC(a: Stream, b: Stream, c: Stream)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c))
  // post-conditions-end
{
// impl-start
  match a {
    case {:split false} SNil =>
    case {:split false} SCons(h, t) =>
      SAppendIsAssociativeC(t, b, c);
  }
// impl-end
}

greatest lemma SAppendIsAssociative_Auto(a: Stream, b: Stream, c: Stream)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c))
  // post-conditions-end
{
// impl-start
// impl-end
}

greatest lemma {:induction false} UpPos(n: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures Pos(Up(n))
  // post-conditions-end
{
// impl-start
  UpPos(n + 1);
// impl-end
}

greatest lemma UpPos_Auto(n: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures Pos(Up(n))
  // post-conditions-end
{
// impl-start
// impl-end
}

greatest lemma {:induction false} FivesUpPos(n: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures Pos(FivesUp(n))
  decreases 4 - (n - 1) % 5
  // post-conditions-end
{
// impl-start
  if n % 5 == 0 {
    FivesUpPos#[_k - 1](n + 1);
  } else {
    FivesUpPos#[_k](n + 1);
  }
// impl-end
}

greatest lemma FivesUpPos_Auto(n: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures Pos(FivesUp(n))
  decreases 4 - (n - 1) % 5
  // post-conditions-end
{
// impl-start
// impl-end
}

codatatype Stream<T> = SNil | SCons(head: T, tail: Stream<T>)
