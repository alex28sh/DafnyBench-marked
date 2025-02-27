method suma_componentes(V: array?<int>) returns (suma: int)
  // pre-conditions-start
  requires V != null
  // pre-conditions-end
  // post-conditions-start
  ensures suma == suma_aux(V, 0)
  // post-conditions-end
{
// impl-start
  var n: int;
  // assert-start
  assert V != null;
  // assert-end

  // assert-start
  assert 0 <= V.Length <= V.Length && 0 == suma_aux(V, V.Length);
  // assert-end

  n := V.Length;
  suma := 0;
  // assert-start
  assert 0 <= n <= V.Length && suma == suma_aux(V, n);
  // assert-end

  while n != 0
    // invariants-start

    invariant 0 <= n <= V.Length && suma == suma_aux(V, n)
    decreases n
    // invariants-end

  {
    // assert-start
    assert 0 <= n <= V.Length && suma == suma_aux(V, n) && n != 0;
    // assert-end

    // assert-start
    assert 0 <= n - 1 <= V.Length;
    // assert-end

    // assert-start
    assert suma + V[n - 1] == suma_aux(V, n - 1);
    // assert-end

    suma := suma + V[n - 1];
    // assert-start
    assert 0 <= n - 1 <= V.Length && suma == suma_aux(V, n - 1);
    // assert-end

    n := n - 1;
    // assert-start
    assert 0 <= n <= V.Length && suma == suma_aux(V, n);
    // assert-end

  }
  // assert-start
  assert 0 <= n <= V.Length && suma == suma_aux(V, n) && n == 0;
  // assert-end

  // assert-start
  assert suma == suma_aux(V, 0);
  // assert-end

// impl-end
}

function suma_aux(V: array?<int>, n: int): int
  requires V != null
  requires 0 <= n <= V.Length
  reads V
  decreases V.Length - n
{
  if n == V.Length then
    0
  else
    V[n] + suma_aux(V, n + 1)
}
// pure-end
