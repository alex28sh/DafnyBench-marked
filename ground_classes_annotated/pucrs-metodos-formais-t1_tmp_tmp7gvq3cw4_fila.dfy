// pucrs-metodos-formais-t1_tmp_tmp7gvq3cw4_fila.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var fila := new Fila();
  fila.enfileira(1);
  fila.enfileira(2);
  fila.enfileira(3);
  fila.enfileira(4);
  // assert-start
  assert fila.Conteudo == [1, 2, 3, 4];
  // assert-end

  var q := fila.tamanho();
  // assert-start
  assert q == 4;
  // assert-end

  var e := fila.desenfileira();
  // assert-start
  assert e == 1;
  // assert-end

  // assert-start
  assert fila.Conteudo == [2, 3, 4];
  // assert-end

  // assert-start
  assert fila.tamanho() == 3;
  // assert-end

  // assert-start
  assert fila.Conteudo == [2, 3, 4];
  // assert-end

  var r := fila.contem(1);
  // assert-start
  assert r == false;
  // assert-end

  // assert-start
  assert fila.a[0] == 2;
  // assert-end

  var r2 := fila.contem(2);
  // assert-start
  assert r2 == true;
  // assert-end

  var vazia := fila.estaVazia();
  // assert-start
  assert vazia == false;
  // assert-end

  var outraFila := new Fila();
  vazia := outraFila.estaVazia();
  // assert-start
  assert vazia == true;
  // assert-end

  // assert-start
  assert fila.Conteudo == [2, 3, 4];
  // assert-end

  outraFila.enfileira(5);
  outraFila.enfileira(6);
  outraFila.enfileira(7);
  // assert-start
  assert outraFila.Conteudo == [5, 6, 7];
  // assert-end

  var concatenada := fila.concat(outraFila);
  // assert-start
  assert concatenada.Conteudo == [2, 3, 4, 5, 6, 7];
  // assert-end

// impl-end
}

class {:autocontracts} Fila {
  var a: array<int>
  var cauda: nat
  const defaultSize: nat
  ghost var Conteudo: seq<int>

  ghost predicate Valid()
  {
    this.defaultSize > 0 &&
    this.a.Length >= this.defaultSize &&
    0 <= this.cauda <= this.a.Length &&
    this.Conteudo == this.a[0 .. this.cauda]
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.Conteudo == []
    ensures this.defaultSize == 3
    ensures this.a.Length == 3
    ensures fresh(this.a)
    // post-conditions-end
  {
  // impl-start
    this.defaultSize := 3;
    this.a := new int[3];
    this.cauda := 0;
    this.Conteudo := [];
  // impl-end
  }

  function tamanho(): nat
    ensures this.tamanho() == |this.Conteudo|
  {
    this.cauda
  }
  // pure-end

  function estaVazia(): bool
    ensures this.estaVazia() <==> |this.Conteudo| == 0
  {
    this.cauda == 0
  }
  // pure-end

  method enfileira(e: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.Conteudo == old(this.Conteudo) + [e]
    // post-conditions-end
  {
  // impl-start
    if this.cauda == this.a.Length {
      var novoArray := new int[this.cauda + this.defaultSize];
      var i := 0;
      forall i | 0 <= i < this.a.Length {
        novoArray[i] := this.a[i];
      }
      this.a := novoArray;
    }
    this.a[this.cauda] := e;
    this.cauda := this.cauda + 1;
    this.Conteudo := this.Conteudo + [e];
  // impl-end
  }

  method desenfileira() returns (e: int)
    // pre-conditions-start
    requires |this.Conteudo| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures e == old(this.Conteudo)[0]
    ensures this.Conteudo == old(this.Conteudo)[1..]
    // post-conditions-end
  {
  // impl-start
    e := this.a[0];
    this.cauda := this.cauda - 1;
    forall i | 0 <= i < this.cauda {
      this.a[i] := this.a[i + 1];
    }
    this.Conteudo := this.a[0 .. this.cauda];
  // impl-end
  }

  method contem(e: int) returns (r: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures r <==> exists i :: 0 <= i < this.cauda && e == this.a[i]
    // post-conditions-end
  {
  // impl-start
    var i := 0;
    r := false;
    while i < this.cauda
      // invariants-start

      invariant 0 <= i <= this.cauda
      invariant forall j: nat :: j < i ==> this.a[j] != e
      // invariants-end

    {
      if this.a[i] == e {
        r := true;
        return;
      }
      i := i + 1;
    }
    return r;
  // impl-end
  }

  method concat(f2: Fila) returns (r: Fila)
    // pre-conditions-start
    requires this.Valid()
    requires f2.Valid()
    // pre-conditions-end
    // post-conditions-start
    ensures r.Conteudo == this.Conteudo + f2.Conteudo
    // post-conditions-end
  {
  // impl-start
    r := new Fila();
    var i := 0;
    while i < this.cauda
      // invariants-start

      invariant 0 <= i <= this.cauda
      invariant 0 <= i <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == this.Conteudo[0 .. i]
      // invariants-end

    {
      var valor := this.a[i];
      r.enfileira(valor);
      i := i + 1;
    }
    var j := 0;
    while j < f2.cauda
      // invariants-start

      invariant 0 <= j <= f2.cauda
      invariant 0 <= j <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == this.Conteudo + f2.Conteudo[0 .. j]
      // invariants-end

    {
      var valor := f2.a[j];
      r.enfileira(valor);
      j := j + 1;
    }
  // impl-end
  }
}
