function sorted(s: seq<int>): bool
{
  forall u, w :: 
    0 <= u < w < |s| ==>
      s[u] <= s[w]
}
// pure-end

method binarySearch(v: array<int>, elem: int) returns (p: int)
  // pre-conditions-start
  requires sorted(v[0 .. v.Length])
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= p < v.Length
  ensures (forall u :: 0 <= u <= p ==> v[u] <= elem) && forall w :: p < w < v.Length ==> v[w] > elem
  // post-conditions-end
{
// impl-start
  var c, f := 0, v.Length - 1;
  while c <= f
    // invariants-start

    invariant 0 <= c <= v.Length && -1 <= f <= v.Length - 1 && c <= f + 1
    invariant (forall u :: 0 <= u < c ==> v[u] <= elem) && forall w :: f < w < v.Length ==> v[w] > elem
    decreases f - c
    // invariants-end

  {
    var m := (c + f) / 2;
    if v[m] <= elem {
      c := m + 1;
    } else {
      f := m - 1;
    }
  }
  p := c - 1;
// impl-end
}

method search(v: array<int>, elem: int) returns (b: bool)
  // pre-conditions-start
  requires sorted(v[0 .. v.Length])
  // pre-conditions-end
  // post-conditions-start
  ensures b == (elem in v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var p := binarySearch(v, elem);
  if p == -1 {
    b := false;
  } else {
    b := v[p] == elem;
  }
// impl-end
}

method {:tailrecursion false} binarySearchRec(v: array<int>, elem: int, c: int, f: int)
    returns (p: int)
  // pre-conditions-start
  requires sorted(v[0 .. v.Length])
  requires 0 <= c <= f + 1 <= v.Length
  requires forall k :: 0 <= k < c ==> v[k] <= elem
  requires forall k :: f < k < v.Length ==> v[k] > elem
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= p < v.Length
  ensures (forall u :: 0 <= u <= p ==> v[u] <= elem) && forall w :: p < w < v.Length ==> v[w] > elem
  decreases f - c
  // post-conditions-end
{
// impl-start
  if c == f + 1 {
    p := c - 1;
  } else {
    var m := (c + f) / 2;
    if v[m] <= elem {
      p := binarySearchRec(v, elem, m + 1, f);
    } else {
      p := binarySearchRec(v, elem, c, m - 1);
    }
  }
// impl-end
}

method otherbSearch(v: array<int>, elem: int)
    returns (b: bool, p: int)
  // pre-conditions-start
  requires sorted(v[0 .. v.Length])
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= p <= v.Length
  ensures b == (elem in v[0 .. v.Length])
  ensures b ==> p < v.Length && v[p] == elem
  ensures !b ==> (forall u :: 0 <= u < p ==> v[u] < elem) && forall w :: p <= w < v.Length ==> v[w] > elem
  // post-conditions-end
{
// impl-start
  p := binarySearch(v, elem);
  if p == -1 {
    b := false;
    p := p + 1;
  } else {
    b := v[p] == elem;
    p := p + if b then 0 else 1;
  }
// impl-end
}
