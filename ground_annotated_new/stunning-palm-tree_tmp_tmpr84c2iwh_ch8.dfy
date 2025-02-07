function Length<T>(xs: List<T>): int
  ensures Length(xs) >= 0
{
  match xs
  case Nil =>
    0
  case Cons(_ /* _v0 */, tl) =>
    1 + Length(tl)
}
// pure-end

function At<T>(xs: List, i: nat): T
  requires i < Length(xs)
{
  if i == 0 then
    xs.head
  else
    At(xs.tail, i - 1)
}
// pure-end

function Ordered(xs: List<int>): bool
{
  match xs
  case Nil =>
    true
  case Cons(_ /* _v1 */, Nil) =>
    true
  case Cons(hd0, Cons(hd1, _ /* _v2 */)) =>
    hd0 <= hd1 &&
    Ordered(xs.tail)
}
// pure-end

lemma AllOrdered(xs: List<int>, i: nat, j: nat)
  // pre-conditions-start
  requires Ordered(xs) && i <= j < Length(xs)
  // pre-conditions-end
  // post-conditions-start
  ensures At(xs, i) <= At(xs, j)
  // post-conditions-end
{
// impl-start
  if i != 0 {
    AllOrdered(xs.tail, i - 1, j - 1);
  } else if i == j {
    assert i == 0 && j == 0;
  } else {
    assert i == 0 && i < j;
    assert xs.head <= xs.tail.head;
    AllOrdered(xs.tail, 0, j - 1);
  }
// impl-end
}

function Count<T(==)>(xs: List<T>, p: T): int
  ensures Count(xs, p) >= 0
{
  match xs
  case Nil =>
    0
  case Cons(hd, tl) =>
    (if hd == p then 1 else 0) + Count(tl, p)
}
// pure-end

function Project<T(==)>(xs: List<T>, p: T): List<T>
{
  match xs
  case Nil =>
    Nil
  case Cons(hd, tl) =>
    if hd == p then
      Cons(hd, Project(tl, p))
    else
      Project(tl, p)
}
// pure-end

lemma {:induction false} CountProject<T(==)>(xs: List<T>, ys: List<T>, p: T)
  // pre-conditions-start
  requires Project(xs, p) == Project(ys, p)
  // pre-conditions-end
  // post-conditions-start
  ensures Count(xs, p) == Count(ys, p)
  // post-conditions-end
{
// impl-start
  match xs
  case {:split false} Nil =>
    {
      match ys
      case {:split false} Nil =>
        {
        }
      case {:split false} Cons(yhd, ytl) =>
        {
          assert Count(xs, p) == 0;
          assert Project(xs, p) == Nil;
          assert Project(ys, p) == Nil;
          assert yhd != p;
          CountProject(xs, ytl, p);
        }
    }
  case {:split false} Cons(xhd, xtl) =>
    {
      match ys
      case {:split false} Nil =>
        {
          assert Count(ys, p) == 0;
          CountProject(xtl, ys, p);
        }
      case {:split false} Cons(yhd, ytl) =>
        {
          if xhd == p && yhd == p {
            assert Count(xs, p) == 1 + Count(xtl, p);
            assert Count(ys, p) == 1 + Count(ytl, p);
            assert Project(xtl, p) == Project(ytl, p);
            CountProject(xtl, ytl, p);
          } else if xhd != p && yhd == p {
            assert Count(xs, p) == Count(xtl, p);
            assert Count(ys, p) == 1 + Count(ytl, p);
            CountProject(xtl, ys, p);
          } else if xhd == p && yhd != p {
            assert Count(ys, p) == Count(ytl, p);
            assert Count(xs, p) == 1 + Count(xtl, p);
            CountProject(xs, ytl, p);
          } else {
            CountProject(xtl, ytl, p);
          }
        }
    }
// impl-end
}

function InsertionSort(xs: List<int>): List<int>
{
  match xs
  case Nil =>
    Nil
  case Cons(x, rest) =>
    Insert(x, InsertionSort(rest))
}
// pure-end

function Insert(x: int, xs: List<int>): List<int>
{
  match xs
  case Nil =>
    Cons(x, Nil)
  case Cons(hd, tl) =>
    if x < hd then
      Cons(x, xs)
    else
      Cons(hd, Insert(x, tl))
}
// pure-end

lemma InsertionSortOrdered(xs: List<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Ordered(InsertionSort(xs))
  // post-conditions-end
{
// impl-start
  match xs
  case {:split false} Nil =>
  case {:split false} Cons(hd, tl) =>
    {
      InsertionSortOrdered(tl);
      InsertOrdered(hd, InsertionSort(tl));
    }
// impl-end
}

lemma InsertOrdered(y: int, xs: List<int>)
  // pre-conditions-start
  requires Ordered(xs)
  // pre-conditions-end
  // post-conditions-start
  ensures Ordered(Insert(y, xs))
  // post-conditions-end
{
// impl-start
  match xs
  case {:split false} Nil =>
  case {:split false} Cons(hd, tl) =>
    {
      if y < hd {
        assert Ordered(Cons(y, xs));
      } else {
        InsertOrdered(y, tl);
        assert Ordered(Cons(hd, Insert(y, tl)));
      }
    }
// impl-end
}

lemma InsertionSortSameElements(xs: List<int>, p: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
  // post-conditions-end
{
// impl-start
  match xs
  case {:split false} Nil =>
  case {:split false} Cons(hd, tl) =>
    {
      InsertSameElements(hd, InsertionSort(tl), p);
    }
// impl-end
}

lemma InsertSameElements(y: int, xs: List<int>, p: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
  // post-conditions-end
{
// impl-start
// impl-end
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
