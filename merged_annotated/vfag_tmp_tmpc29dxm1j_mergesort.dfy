method ordenar_mergesort(V: array?<int>)
  // pre-conditions-start
  requires V != null
  // pre-conditions-end
  // post-conditions-start
  modifies V
  // post-conditions-end
{
// impl-start
  mergesort(V, 0, V.Length - 1);
// impl-end
}

method mergesort(V: array?<int>, c: int, f: int)
  // pre-conditions-start
  requires V != null
  requires c >= 0 && f <= V.Length
  // pre-conditions-end
  // post-conditions-start
  modifies V
  decreases f - c
  // post-conditions-end
{
// impl-start
  if c < f {
    var m: int;
    m := c + (f - c) / 2;
    mergesort(V, c, m);
    mergesort(V, m + 1, f);
    mezclar(V, c, m, f);
  }
// impl-end
}

method mezclar(V: array?<int>, c: int, m: int, f: int)
  // pre-conditions-start
  requires V != null
  requires c <= m <= f
  requires 0 <= c <= V.Length
  requires 0 <= m <= V.Length
  requires 0 <= f <= V.Length
  // pre-conditions-end
  // post-conditions-start
  modifies V
  // post-conditions-end
{
// impl-start
  var V1: array?<int>;
  var j: nat;
  V1 := new int[m - c + 1];
  j := 0;
  while j < V1.Length && c + j < V.Length
    // invariants-start

    invariant 0 <= j <= V1.Length
    invariant 0 <= c + j <= V.Length
    decreases V1.Length - j
    // invariants-end

  {
    V1[j] := V[c + j];
    j := j + 1;
  }
  var V2: array?<int>;
  var k: nat;
  V2 := new int[f - m];
  k := 0;
  while k < V2.Length && m + k + 1 < V.Length
    // invariants-start

    invariant 0 <= k <= V2.Length
    invariant 0 <= m + k <= V.Length
    decreases V2.Length - k
    // invariants-end

  {
    V2[k] := V[m + k + 1];
    k := k + 1;
  }
  var i: nat;
  i := 0;
  j := 0;
  k := 0;
  while i < f - c + 1 && j <= V1.Length && k <= V2.Length && c + i < V.Length
    // invariants-start

    invariant 0 <= i <= f - c + 1
    decreases f - c - i
    // invariants-end

  {
    if j >= V1.Length && k >= V2.Length {
      break;
    } else if j >= V1.Length {
      V[c + i] := V2[k];
      k := k + 1;
    } else if k >= V2.Length {
      V[c + i] := V1[j];
      j := j + 1;
    } else {
      if V1[j] <= V2[k] {
        V[c + i] := V1[j];
        j := j + 1;
      } else if V1[j] > V2[k] {
        V[c + i] := V2[k];
        k := k + 1;
      }
    }
    i := i + 1;
  }
// impl-end
}
