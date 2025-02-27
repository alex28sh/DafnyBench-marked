class Counter {

  var value : int ;

  constructor init() 
  ensures this.value == 0;
  {
    this.value := 0 ;
  }

  method getValue() returns (x:int)
  ensures x == this.value;
  {
    x := this.value ;
  }

  method inc()
  modifies `value
  requires this.value >= 0;
  ensures this.value == old(this.value) + 1; 
  {
    this.value := this.value + 1;
  }

  method dec()
  modifies `value
  requires this.value > 0;
  ensures this.value == old(this.value) - 1; 
  {  
    this.value := this.value - 1 ;
  }

  method Main ()
  {
    var count := new Counter.init() ;
    count.inc();
    count.inc();
    count.dec();
    count.inc();
    var aux : int := count.getValue();
    assert (aux == 2) ;
  }
}
