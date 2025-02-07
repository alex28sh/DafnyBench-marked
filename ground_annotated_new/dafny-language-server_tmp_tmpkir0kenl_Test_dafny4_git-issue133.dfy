lemma Test(s: State)
  // pre-conditions-start
  requires 42 in s.m
  // pre-conditions-end
  // post-conditions-start
  ensures s.(m := s.m[42 := s.m[42]]) == s
  // post-conditions-end
{
// impl-start
  var s' := s.(m := s.m[42 := s.m[42]]);
  assert s'.m == s.m;
// impl-end
}

lemma AnotherTest(a: MyDt, b: MyDt, c: bool)
  // pre-conditions-start
  requires a.MakeB? && b.MakeB?
  requires a.s == multiset(a.t.m.Keys) && |b.s| == 0
  requires a.t.m == map[] && |b.t.m| == 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert a == b;
// impl-end
}

method ChangeGen(g: GenDt)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  match g
  case {:split false} Left(_ /* _v5 */) =>
  case {:split false} Middle(_ /* _v6 */, _ /* _v7 */, _ /* _v8 */) =>
  case {:split false} Right(u) =>
    var h := g.(y := u);
    // assert-start
    assert g == h;
    // assert-end

// impl-end
}

lemma RecLem(r: Recursive) returns (s: Recursive)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == s
  // post-conditions-end
{
// impl-start
  match r
  case {:split false} Red =>
    s := Red;
  case {:split false} Green(next, m) =>
    var n := RecLem(next);
    s := Green(n, m + m);
// impl-end
}

datatype State = State(m: map<int, bool>)

datatype MyDt = MakeA(x: int, bool) | MakeB(s: multiset<int>, t: State)

datatype GenDt<X, Y> = Left(X) | Middle(X, int, Y) | Right(y: Y)

datatype Recursive<X> = Red | Green(next: Recursive, m: set)
