function length<T>(l: List<T>): nat
{
  match l
  case Nil =>
    0
  case Cons(_ /* _v0 */, t) =>
    1 + length(t)
}
// pure-end

function mem<T(==)>(l: List<T>, x: T): bool
{
  match l
  case Nil =>
    false
  case Cons(h, t) =>
    if h == x then
      true
    else
      mem(t, x)
}
// pure-end

function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
{
  if i == 0 then
    l.head
  else
    at(l.tail, i - 1)
}
// pure-end

method from_array<T>(a: array<T>) returns (l: List<T>)
  // pre-conditions-start
  requires a.Length >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
  // post-conditions-end
{
// impl-start
  l := Nil;
  var i: int := a.Length - 1;
  while i >= 0
    // invariants-start

    invariant -1 <= i <= a.Length - 1
    invariant length(l) == a.Length - 1 - i
    invariant forall j: int :: i < j < a.Length ==> at(l, j - i - 1) == a[j]
    invariant forall x :: mem(l, x) ==> exists k: int :: i < k < a.Length && a[k] == x
    // invariants-end

  {
    l := Cons(a[i], l);
    i := i - 1;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var l: List<int> := List.Cons(1, List.Cons(2, List.Cons(3, Nil)));
  var arr: array<int> := new int[3] (i => i + 1);
  var t: List<int> := from_array(arr);
  print l;
  print "\n";
  print t;
  print "\n";
  print t == l;
// impl-end
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
