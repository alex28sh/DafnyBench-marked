class Contador
{
  var valor: int;

  //construtor anônimo
  constructor ()
    ensures this.valor == 0
  {
    this.valor := 0;
  }

  //construtor com nome
  constructor Init(v:int)
    ensures this.valor == v
  {
    this.valor := v;
  }

  method Incrementa()
    modifies this
    ensures this.valor == old(this.valor) + 1
  {
    this.valor := this.valor + 1;
  }

  method Decrementa()
    modifies this
    ensures this.valor == old(this.valor) - 1
  {
    this.valor := this.valor - 1;
  }

  method GetValor() returns (v:int)
    ensures v == this.valor
  {
    return this.valor;
  }
}

method Main()
{
  var c := new Contador(); //cria um novo objeto no heap via construtor anônimo
  var c2 := new Contador.Init(10); //cria um novo objeto no heap via construtor nomeado
  var v := c.GetValor();
  assert v == 0;
  var v2 := c2.GetValor();
  assert v2 == 10;
  c.Incrementa();
  v := c.GetValor();
  assert v == 1;
  c.Decrementa();
  v := c.GetValor();
  assert v == 0;
}
