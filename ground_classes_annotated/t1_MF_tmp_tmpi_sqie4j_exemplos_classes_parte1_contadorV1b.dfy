// t1_MF_tmp_tmpi_sqie4j_exemplos_classes_parte1_contadorV1b.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var c := new Contador();
  var c2 := new Contador.Init(10);
  var v := c.GetValor();
  // assert-start
  assert v == 0;
  // assert-end

  var v2 := c2.GetValor();
  // assert-start
  assert v2 == 10;
  // assert-end

  c.Incrementa();
  v := c.GetValor();
  // assert-start
  assert v == 1;
  // assert-end

  c.Decrementa();
  v := c.GetValor();
  // assert-start
  assert v == 0;
  // assert-end

// impl-end
}

class Contador {
  var valor: int

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.valor == 0
    // post-conditions-end
  {
  // impl-start
    this.valor := 0;
  // impl-end
  }

  constructor Init(v: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.valor == v
    // post-conditions-end
  {
  // impl-start
    this.valor := v;
  // impl-end
  }

  method Incrementa()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.valor == old(this.valor) + 1
    // post-conditions-end
  {
  // impl-start
    this.valor := this.valor + 1;
  // impl-end
  }

  method Decrementa()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.valor == old(this.valor) - 1
    // post-conditions-end
  {
  // impl-start
    this.valor := this.valor - 1;
  // impl-end
  }

  method GetValor() returns (v: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures v == this.valor
    // post-conditions-end
  {
  // impl-start
    return this.valor;
  // impl-end
  }
}
