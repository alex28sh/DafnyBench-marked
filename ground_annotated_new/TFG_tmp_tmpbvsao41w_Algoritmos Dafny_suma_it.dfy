method suma_it(V: array<int>) returns (x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x == suma_vector(V, 0)
  // post-conditions-end
{
// impl-start
  var n := V.Length;
  x := 0;
  while n != 0
    // invariants-start

    invariant 0 <= n <= V.Length && x == suma_vector(V, n)
    decreases n
    // invariants-end

  {
    x := x + V[n - 1];
    n := n - 1;
  }
// impl-end
}

function suma_vector(V: array<int>, n: nat): int
  requires 0 <= n <= V.Length
  reads V
  decreases V.Length - n
{
  if n == V.Length then
    0
  else
    V[n] + suma_vector(V, n + 1)
}
// pure-end

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var v := new int[] [-1, 2, 5, -5, 8];
  var w := new int[] [1, 0, 5, 5, 8];
  var s1 := suma_it(v);
  var s2 := suma_it(w);
  print "La suma del vector v es: ", s1, "\n";
  print "La suma del vector w es: ", s2;
// impl-end
}
