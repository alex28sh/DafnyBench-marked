class A {
  var value: int
  constructor ()
     ensures this.value == 10
  {
     this.value := 10;
  }
}

class B {
   var a: A
   constructor () { this.a := new A(); }

   method m()
     requires this.a.value == 11
     modifies this, this.a
   {
     label L:
     this.a.value := 12;
     label M:
     this.a := new A(); // Line X
     label N:
     this.a.value := 20;
     label P:

     assert old(this.a.value) == 11;
     assert old(this.a).value == 12; // this.a is from pre-state,
                                     // but .value in current state
     assert old@L(this.a.value) == 11;
     assert old@L(this.a).value == 12; // same as above
     assert old@M(this.a.value) == 12; // .value in M state is 12
     assert old@M(this.a).value == 12;
     assert old@N(this.a.value) == 10; // this.a in N is the heap
                                       // reference at Line X
     assert old@N(this.a).value == 20; // .value in current state is 20
     assert old@P(this.a.value) == 20;
     assert old@P(this.a).value == 20;
  }
}
