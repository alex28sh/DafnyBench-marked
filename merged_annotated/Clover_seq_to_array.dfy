method ToArray<T>(xs: seq<T>) returns (a: array<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures fresh(a)
  ensures a.Length == |xs|
  ensures forall i :: 0 <= i < |xs| ==> a[i] == xs[i]
  // post-conditions-end
{
// impl-start
  a := new T[|xs|] (i requires 0 <= i < |xs| => xs[i]);
// impl-end
}
