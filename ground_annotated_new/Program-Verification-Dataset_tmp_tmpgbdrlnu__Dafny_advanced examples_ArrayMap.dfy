method ArrayMap<A>(f: int -> A, a: array<A>)
  // pre-conditions-start
  requires a != null
  requires forall j :: 0 <= j < a.Length ==> f.requires(j)
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j)
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j)
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == f(j)
    // invariants-end

  {
    a[i] := f(i);
    i := i + 1;
  }
// impl-end
}
