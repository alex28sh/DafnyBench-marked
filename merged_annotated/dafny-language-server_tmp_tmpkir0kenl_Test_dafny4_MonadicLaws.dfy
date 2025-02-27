function append(xs: List, ys: List): List
{
  match xs
  case Nil =>
    ys
  case Cons(x, xs') =>
    Cons(x, append(xs', ys))
}
// pure-end

lemma AppendNil(xs: List)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures append(xs, Nil) == xs
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AppendAssoc(xs: List, ys: List, zs: List)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures append(append(xs, ys), zs) == append(xs, append(ys, zs))
  // post-conditions-end
{
// impl-start
// impl-end
}

function Return<T>(a: T): List
{
  Cons(a, Nil)
}
// pure-end

function Bind<T, U>(xs: List<T>, f: T -> List<U>): List<U>
{
  match xs
  case Nil =>
    Nil
  case Cons(x, xs') =>
    append(f(x), Bind(xs', f))
}
// pure-end

lemma LeftIdentity<T>(a: T, f: T -> List)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Bind(Return(a), f) == f(a)
  // post-conditions-end
{
// impl-start
  AppendNil(f(a));
// impl-end
}

lemma RightIdentity<T>(m: List)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Bind(m, Return) == m
  // post-conditions-end
{
// impl-start
  match m
  case {:split false} Nil =>
    assert Bind<T, T>(Nil, Return) == Nil;
  case {:split false} Cons(x, m') =>
    calc {
      Bind(Cons(x, m'), Return);
      append(Return(x), Bind(m', Return));
      Cons(x, Bind(m', Return));
    }
// impl-end
}

lemma Associativity<T>(m: List, f: T -> List, g: T -> List)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Bind(Bind(m, f), g) == Bind(m, x => Bind(f(x), g))
  // post-conditions-end
{
// impl-start
  match m
  case {:split false} Nil =>
    assert Bind(m, x => Bind(f(x), g)) == Nil;
  case {:split false} Cons(x, xs) =>
    match f(x)
    case {:split false} Nil =>
      calc {
        Bind(xs, y => Bind(f(y), g));
        Bind(Cons(x, xs), y => Bind(f(y), g));
      }
    case {:split false} Cons(y, ys) =>
      calc {
        append(g(y), Bind(append(ys, Bind(xs, f)), g));
        {
          BindOverAppend(ys, Bind(xs, f), g);
        }
        append(g(y), append(Bind(ys, g), Bind(Bind(xs, f), g)));
        {
          AppendAssoc(g(y), Bind(ys, g), Bind(Bind(xs, f), g));
        }
        append(append(g(y), Bind(ys, g)), Bind(Bind(xs, f), g));
        Bind(Cons(x, xs), z => Bind(f(z), g));
      }
// impl-end
}

lemma BindOverAppend<T>(xs: List, ys: List, g: T -> List)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Bind(append(xs, ys), g) == append(Bind(xs, g), Bind(ys, g))
  // post-conditions-end
{
// impl-start
  match xs
  case {:split false} Nil =>
  case {:split false} Cons(x, xs') =>
    AppendAssoc(g(x), Bind(xs', g), Bind(ys, g));
// impl-end
}

datatype List<T> = Nil | Cons(head: T, tail: List)
