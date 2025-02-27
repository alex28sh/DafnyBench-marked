    /*
    OK fila de tamanho ilimitado com arrays circulares
    OK representação ghost: coleção de elementos da fila e qualquer outra informação necessária
    OK predicate: invariante da representação abstrata associada à coleção do tipo fila

    Operações
      - OK construtor inicia fila fazia
      - OK adicionar novo elemento na fila -> enfileira()
      - OK remover um elemento da fila e retornar seu valor caso a fila contenha elementos  -> desenfileira()
      - OK verificar se um elemento pertence a fila  -> contem()
      - OK retornar numero de elementos da fila -> tamanho()
      - OK verificar se a fila é vazia ou não -> estaVazia()
      - OK concatenar duas filas retornando uma nova fila sem alterar nenhuma das outras -> concat()

    OK criar método main testando a implementação 
    OK transformar uso de naturais para inteiros
    */

    class {:autocontracts}  Fila
    {
      var a: array<int>;
      var cauda: nat;
      const defaultSize: nat;

      ghost var Conteudo: seq<int>;

      // invariante
      ghost predicate Valid()  {
      this.defaultSize > 0
      && this.a.Length >= this.defaultSize
      && 0 <= this.cauda <= this.a.Length
      && this.Conteudo == this.a[0..this.cauda]
      }

      // inicia fila com 3 elementos
      constructor ()
      ensures this.Conteudo == []
      ensures this.defaultSize == 3
      ensures this.a.Length == 3
      ensures fresh(this.a)
      {
      this.defaultSize := 3;
      this.a := new int[3];
      this.cauda := 0;
      this.Conteudo := [];
      }

      function tamanho():nat
      ensures this.tamanho() == |this.Conteudo|
      {
      this.cauda
      }

      function estaVazia(): bool
      ensures this.estaVazia() <==> |this.Conteudo| == 0
      {
      this.cauda == 0
      }

      method enfileira(e:int)
      ensures this.Conteudo == old(this.Conteudo) + [e]
      {
      if (this.cauda == this.a.Length) {
        var novoArray := new int[this.cauda + this.defaultSize];
        var i := 0;

        forall i | 0 <= i < this.a.Length
        {
        novoArray[i] := this.a[i];
        }
        this.a := novoArray;
      }

      this.a[this.cauda] := e;
      this.cauda := this.cauda + 1;
      this.Conteudo := this.Conteudo + [e];
      }

      method desenfileira() returns (e:int)
      requires |this.Conteudo| > 0
      ensures e == old(this.Conteudo)[0]
      ensures this.Conteudo == old(this.Conteudo)[1..]
      {
      e := this.a[0];
      this.cauda := this.cauda - 1;
      forall i | 0 <= i < this.cauda
      {
        this.a[i] := this.a[i+1];
      }
      this.Conteudo := this.a[0..this.cauda];
      }

      method contem(e: int) returns (r:bool)
      ensures r <==> exists i :: 0 <= i < this.cauda && e == this.a[i]
      {
      var i := 0;
      r := false;

      while i < this.cauda
        invariant 0 <= i <= this.cauda
        invariant forall j: nat :: j < i ==> this.a[j] != e
      {
        if (this.a[i] == e) {
        r := true;
        return;
        }

        i := i + 1;
      }

      return r;
      }

      method concat(f2: Fila) returns (r: Fila)
      requires this.Valid()
      requires f2.Valid()
      ensures r.Conteudo == this.Conteudo + f2.Conteudo
      {
      r := new Fila();

      var i := 0;

      while i < this.cauda
        invariant 0 <= i <= this.cauda
        invariant 0 <= i <= r.cauda
        invariant r.cauda <= r.a.Length
        invariant fresh(r.Repr)
        invariant r.Valid()
        invariant r.Conteudo == this.Conteudo[0..i]
      {
        var valor := this.a[i];
        r.enfileira(valor);
        i := i + 1;
      }

      var j := 0;
      while j < f2.cauda
        invariant 0 <= j <= f2.cauda
        invariant 0 <= j <= r.cauda
        invariant r.cauda <= r.a.Length
        invariant fresh(r.Repr)
        invariant r.Valid()
        invariant r.Conteudo == this.Conteudo + f2.Conteudo[0..j]
      {
        var valor := f2.a[j];
        r.enfileira(valor);
        j := j + 1;
      }
      }
    }

    method Main()
    {
      var fila := new Fila();

      // enfileira deve alocar mais espaço
      fila.enfileira(1);
      fila.enfileira(2);
      fila.enfileira(3);
      fila.enfileira(4);
      assert fila.Conteudo == [1, 2, 3, 4];

      // tamanho
      var q := fila.tamanho();
      assert q == 4;

      // desenfileira
      var e := fila.desenfileira();
      assert e == 1;
      assert fila.Conteudo == [2, 3, 4];
      assert fila.tamanho() == 3;

      // contem
      assert fila.Conteudo == [2, 3, 4];
      var r := fila.contem(1);
      assert r == false;
      assert fila.a[0] == 2;
      var r2 := fila.contem(2);
      assert r2 == true;

      // estaVazia
      var vazia := fila.estaVazia();
      assert vazia == false;
      var outraFila := new Fila();
      vazia := outraFila.estaVazia();
      assert vazia == true;

      // concat
      assert fila.Conteudo == [2, 3, 4];
      outraFila.enfileira(5);
      outraFila.enfileira(6);
      outraFila.enfileira(7);
      assert outraFila.Conteudo == [5, 6, 7];
      var concatenada := fila.concat(outraFila);
      assert concatenada.Conteudo == [2, 3, 4, 5, 6, 7];
    }
