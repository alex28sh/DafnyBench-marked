// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Fstar-QuickSort.dfy

function length(list: List): nat
{
  match list
  case Nil =>
    0
  case Cons(_ /* _v2 */, tl) =>
    1 + length(tl)
}
// pure-end

function In(x: int, list: List<int>): nat
{
  match list
  case Nil =>
    0
  case Cons(y, tl) =>
    (if x == y then 1 else 0) + In(x, tl)
}
// pure-end

predicate SortedRange(m: int, n: int, list: List<int>)
  decreases list
{
  match list
  case Nil =>
    m <= n
  case Cons(hd, tl) =>
    m <= hd <= n &&
    SortedRange(hd, n, tl)
}
// pure-end

function append(n0: int, n1: int, n2: int, n3: int, i: List<int>, j: List<int>): List<int>
  requires n0 <= n1 <= n2 <= n3
  requires SortedRange(n0, n1, i) && SortedRange(n2, n3, j)
  ensures SortedRange(n0, n3, append(n0, n1, n2, n3, i, j))
  ensures forall x :: In(x, append(n0, n1, n2, n3, i, j)) == In(x, i) + In(x, j)
  decreases i
{
  match i
  case Nil =>
    j
  case Cons(hd, tl) =>
    Cons(hd, append(hd, n1, n2, n3, tl, j))
}
// pure-end

function partition(x: int, l: List<int>): (List<int>, List<int>)
  ensures var (lo, hi) := partition(x, l); (forall y :: In(y, lo) == if y <= x then In(y, l) else 0) && (forall y :: In(y, hi) == if x < y then In(y, l) else 0) && length(l) == length(lo) + length(hi)
{
  match l
  case Nil =>
    (Nil, Nil)
  case Cons(hd, tl) =>
    var (lo, hi) := partition(x, tl);
    if hd <= x then
      (Cons(hd, lo), hi)
    else
      (lo, Cons(hd, hi))
}
// pure-end

function sort(min: int, max: int, i: List<int>): List<int>
  requires min <= max
  requires forall x :: In(x, i) != 0 ==> min <= x <= max
  ensures SortedRange(min, max, sort(min, max, i))
  ensures forall x :: In(x, i) == In(x, sort(min, max, i))
  decreases length(i)
{
  match i
  case Nil =>
    Nil
  case Cons(hd, tl) =>
    assert In(hd, i) != 0;
    var (lo, hi) := partition(hd, tl);
    assert forall y :: In(y, lo) <= In(y, i);
    var i' := sort(min, hd, lo);
    var j' := sort(hd, max, hi);
    append(min, hd, hd, max, i', Cons(hd, j'))
}
// pure-end

datatype List<T> = Nil | Cons(T, List)
