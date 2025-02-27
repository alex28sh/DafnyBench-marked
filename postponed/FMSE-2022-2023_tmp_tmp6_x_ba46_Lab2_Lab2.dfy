
lemma SIsInjective(x: Nat, y: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures S(x) == S(y) ==> x == y
  // post-conditions-end
{
// impl-start
  assume S(x) == S(y);
  assert S(x).Pred == S(y).Pred;
  assert x == y;
// impl-end
}

lemma ZeroIsDifferentFromSuccessor(n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures S(n) != Zero
  // post-conditions-end
{
// impl-start
  assert S(n).Zero? == false;
// impl-end
}

function Add(x: Nat, y: Nat): Nat
  decreases y
{
  match y
  case Zero =>
    x
  case S(y') =>
    S(Add(x, y'))
}
// pure-end

lemma {:induction n} ZeroAddNeutral(n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(n, Zero) == Add(Zero, n) == n
  // post-conditions-end
{
// impl-start
  match n
  case {:split false} Zero =>
    {
      assert Add(n, Zero) == Add(Zero, Zero) == Add(Zero, n) == n;
    }
  case {:split false} S(n') =>
    {
      assert Add(n, Zero) == Add(S(n'), Zero) == S(n') == Add(Zero, S(n')) == Add(Zero, n) == n;
    }
// impl-end
}

lemma {:induction n} ZeroAddCommutative(n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Zero, n) == Add(n, Zero)
  // post-conditions-end
{
// impl-start
  assert Add(Zero, n) == n == Add(n, Zero);
// impl-end
}

lemma {:induction x, y} AddCommutative(x: Nat, y: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(x, y) == Add(y, x)
  decreases x, y
  // post-conditions-end
{
// impl-start
  match x
  case {:split false} Zero =>
    ZeroAddCommutative(y);
  case {:split false} S(x') =>
    AddCommutative(x', y);
// impl-end
}

lemma {:induction x, y} ZeroAddAssociative(x: Nat, y: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Add(Zero, x), y) == Add(Zero, Add(x, y))
  // post-conditions-end
{
// impl-start
  ZeroAddNeutral(x);
  assert Add(Add(Zero, x), y) == Add(x, y) == Add(Zero, Add(x, y));
// impl-end
}

lemma {:induction x, y} AddAssociative(x: Nat, y: Nat, z: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Add(Add(x, y), z) == Add(x, Add(y, z))
  decreases z
  // post-conditions-end
{
// impl-start
  match z
  case {:split false} Zero =>
    ZeroAddAssociative(Add(x, y), Zero);
  case {:split false} S(z') =>
    AddAssociative(x, y, z');
// impl-end
}

predicate LessThan(x: Nat, y: Nat)
  decreases x, y
{
  (x.Zero? && y.S?) || (x.S? && y.S? && LessThan(x.Pred, y.Pred))
}
// pure-end

lemma {:induction y, z} LessThanIsTransitiveWithZero(y: Nat, z: Nat)
  // pre-conditions-start
  requires LessThan(Zero, y)
  requires LessThan(y, z)
  // pre-conditions-end
  // post-conditions-start
  ensures LessThan(Zero, z)
  // post-conditions-end
{
// impl-start
  if !LessThan(Zero, z) {
    assert z != Zero;
    assert Zero.S?;
    assert false;
  }
// impl-end
}

lemma {:induction x, y, z} LessThanIsTransitive(x: Nat, y: Nat, z: Nat)
  // pre-conditions-start
  requires LessThan(x, y)
  requires LessThan(y, z)
  // pre-conditions-end
  // post-conditions-start
  ensures LessThan(x, z)
  decreases x
  // post-conditions-end
{
// impl-start
  match x
  case {:split false} Zero =>
    LessThanIsTransitiveWithZero(y, z);
  case {:split false} S(x') =>
    match y
    case {:split false} S(y') =>
      match z
      case {:split false} S(z') =>
        LessThanIsTransitive(x', y', z');
// impl-end
}

function Size(l: List<Nat>): Nat
  decreases l
{
  if l.Nil? then
    Zero
  else
    S(Size(l.tail))
}
// pure-end

function Concatenation(l1: List<Nat>, l2: List<Nat>): List<Nat>
  decreases l1, l2
{
  match l1
  case Nil =>
    l2
  case Append(head1, tail1) =>
    match l2
    case Nil =>
      l1
    case Append(_ /* _v0 */, _ /* _v1 */) =>
      Append(head1, Concatenation(tail1, l2))
}
// pure-end

lemma {:induction l1, l2} SizeOfConcatenationIsSumOfSizes(l1: List<Nat>, l2: List<Nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Size(Concatenation(l1, l2)) == Add(Size(l1), Size(l2))
  decreases l1, l2
  // post-conditions-end
{
// impl-start
  match l1
  case {:split false} Nil =>
    {
      ZeroAddNeutral(Size(l2));
      assert Size(Concatenation(l1, l2)) == Size(Concatenation(Nil, l2)) == Size(l2) == Add(Zero, Size(l2)) == Add(Size(l1), Size(l2));
    }
  case {:split false} Append(_ /* _v2 */, tail1) =>
    match l2
    case {:split false} Nil =>
      {
        assert Size(Concatenation(l1, l2)) == Size(Concatenation(l1, Nil)) == Size(l1) == Add(Size(l1), Zero) == Add(Size(l1), Size(l2));
      }
    case {:split false} Append(_ /* _v3 */, tail2) =>
      SizeOfConcatenationIsSumOfSizes(tail1, tail2);
// impl-end
}

function ReverseList(l: List<Nat>): List<Nat>
  decreases l
{
  if l.Nil? then
    Nil
  else
    Concatenation(ReverseList(l.tail), Append(l.head, Nil))
}
// pure-end

lemma {:induction l, n} ReversalOfConcatenationWithHead(l: List<Nat>, n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures ReverseList(Concatenation(l, Append(n, Nil))) == Append(n, ReverseList(l))
  decreases l, n
  // post-conditions-end
{
// impl-start
  match l
  case {:split false} Nil =>
    {
      assert ReverseList(Concatenation(l, Append(n, Nil))) == ReverseList(Concatenation(Nil, Append(n, Nil))) == ReverseList(Append(n, Nil)) == Concatenation(ReverseList(Append(n, Nil).tail), Append(Append(n, Nil).head, Nil)) == Concatenation(ReverseList(Nil), Append(n, Nil)) == Concatenation(Nil, Append(n, Nil)) == Append(n, Nil) == Append(n, l) == Append(n, ReverseList(l));
    }
  case {:split false} Append(head, tail) =>
    ReversalOfConcatenationWithHead(tail, n);
// impl-end
}

lemma {:induction l} DoubleReversalResultsInInitialList(l: List<Nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures l == ReverseList(ReverseList(l))
  // post-conditions-end
{
// impl-start
  match l
  case {:split false} Nil =>
    {
      assert ReverseList(ReverseList(l)) == ReverseList(ReverseList(Nil)) == ReverseList(Nil) == Nil;
      assert l == ReverseList(ReverseList(l));
    }
  case {:split false} Append(head, tail) =>
    {
      ReversalOfConcatenationWithHead(ReverseList(tail), head);
      assert ReverseList(ReverseList(l)) == ReverseList(ReverseList(Append(head, tail))) == ReverseList(Concatenation(ReverseList(tail), Append(head, Nil))) == Append(head, ReverseList(ReverseList(tail))) == Append(head, tail) == l;
    }
// impl-end
}

datatype Nat = Zero | S(Pred: Nat)

datatype List<T> = Nil | Append(head: T, tail: List)
