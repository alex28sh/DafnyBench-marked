class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= this.counter <= this.circularQueue.Length &&
    0 <= this.front &&
    0 <= this.rear &&
    this.Content == this.circularQueue[..]
  }

  // Construtor
  constructor()
    ensures this.circularQueue.Length == 0
    ensures this.front == 0 && this.rear == 0
    ensures this.Content == [] // REVISAR
    ensures this.counter == 0
  {
    this.circularQueue := new int[0];
    this.rear := 0;
    this.front := 0;
    this.Content := [];
    this.counter := 0;
  } //[tam] ; [1, 2, 3, 4]

  method insert(item: int)
    // requires this.rear <= this.circularQueue.Length
    // ensures (this.front == 0 && this.rear == 0 && this.circularQueue.Length == 1) ==>
    //     (
    //       this.Content == [item] &&
    //       |this.Content| == 1
    //     )
    // ensures this.circularQueue.Length != 0 ==>
    // (
    //   (this.front == 0 && this.rear == 0 && this.circularQueue.Length == 1) ==>
    //     (
    //       this.Content == old(this.Content)  &&
    //       |this.Content| == old(|this.Content|)

    //     )
    // ||
    //   (this.front == 0 && this.rear == this.circularQueue.Length-1 ) ==> 
    //     (
    //       this.Content == old(this.Content) + [item] &&
    //       |this.Content| == old(|this.Content|) + 1
    //     )
    // ||
    //   (this.rear + 1 != this.front && this.rear != this.circularQueue.Length-1 && this.rear + 1 < this.circularQueue.Length - 1) ==> 
    //     (
    //       this.Content == old(this.Content[0..this.rear]) + [item] + old(this.Content[this.rear..this.circularQueue.Length])
    //     )
    // ||
    //   (this.rear + 1 == this.front) ==> 
    //   (
    //     this.Content[0..this.rear + 1] == old(this.Content[0..this.rear]) + [item] &&
    //     forall i :: this.rear + 2 <= i <= this.circularQueue.Length ==> this.Content[i] == old(this.Content[i-1])
    //   )
    // )
    {

      //this.counter := this.counter + 1;
      // if this.front == 0 && this.rear == 0 && this.circularQueue.Length == 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [this.circularQueue.Length + 1];
      //   queueInsert[0] := item;
      //   this.circularQueue := queueInsert;
      //   this.Content := [item];
      //   this.rear := this.rear + 1;
      // }   
      // else if this.front == 0 && this.rear == this.circularQueue.Length-1 && this.circularQueue.Length > 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [this.circularQueue.Length + 1];
      //   var i: nat := 0;
      //   while i < this.circularQueue.Length
      //   invariant this.circularQueue.Length + 1 == queueInsert.Length
      //   {
      //     queueInsert[i] := this.circularQueue[i];
      //     i := i + 1;
      //   }
      //   queueInsert[queueInsert.Length - 1] := item;
      //   this.Content := this.Content + [item];
      //   this.rear := this.rear + 1;
      //   this.circularQueue := queueInsert;
      // }
    }

  method auxInsertEmptyQueue(item:int)
    requires this.front == 0 && this.rear == 0 && this.circularQueue.Length == 0
    ensures this.circularQueue.Length == 1
    ensures this.Content == [item]
    ensures |this.Content| == 1
    ensures this.rear == 1
    ensures this.counter == old(this.counter) + 1
    ensures this.front == 0
  {
    this.counter := this.counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [this.circularQueue.Length + 1];
    queueInsert[0] := item;
    this.circularQueue := queueInsert;
    this.Content := [item];
    this.rear := this.rear + 1;
  }

  method auxInsertEndQueue(item:int)
    requires this.front == 0 && this.rear == this.circularQueue.Length && this.circularQueue.Length >= 1
    ensures this.Content == old(this.Content) + [item]
    ensures |this.Content| == old(|this.Content|) + 1
    ensures this.front == 0
    ensures this.rear == old(this.rear) + 1
    ensures this.counter == old(this.counter) + 1
  // {
  //   this.counter := this.counter + 1;
  //   var queueInsert: array<int>;
  //   queueInsert := new int [this.circularQueue.Length + 1];
  //   var i: nat := 0;
  //   while i < this.circularQueue.Length
  //   invariant this.circularQueue.Length + 1 == queueInsert.Length
  //   invariant 0 <= i <= this.circularQueue.Length
  //   invariant forall j :: 0 <= j < i ==> queueInsert[j] == this.circularQueue[j]
  //   {
  //     queueInsert[i] := this.circularQueue[i];
  //     i := i + 1;
  //   }
  //   queueInsert[queueInsert.Length - 1] := item;
  //   this.Content := this.Content + [item];
  //   this.rear := this.rear + 1;
  //   this.circularQueue := queueInsert;
  // }

  method auxInsertSpaceQueue(item:int)
    requires this.rear < this.front && this.front < this.circularQueue.Length
    ensures this.rear == old(this.rear) + 1
    ensures this.counter == old(this.counter) + 1
    ensures this.Content == old(this.Content[0..this.rear]) + [item] + old(this.Content[this.rear+1..this.circularQueue.Length])
    ensures |this.Content| == old(|this.Content|) + 1

  method auxInsertInitQueue(item:int)

  method auxInsertBetweenQueue(item:int)

  // remove apenas mudando o ponteiro
  // sem resetar o valor na posição, pois, provavelmente,
  // vai ser sobrescrito pela inserção
  method remove() returns (item: int)
    requires this.front < this.circularQueue.Length
    requires this.circularQueue.Length > 0
    ensures this.rear <= |old(this.Content)|
    ensures this.circularQueue.Length > 0
    ensures item == old(this.Content)[old(this.front)]
    ensures this.front == (old(this.front) + 1) % this.circularQueue.Length
    ensures old(this.front) < this.rear ==> this.Content == old(this.Content)[old(this.front)..this.rear]
    ensures old(this.front) > this.rear ==> this.Content == old(this.Content)[0 .. this.rear] + old(this.Content)[old(this.front)..|old(this.Content)|]
  /*{
    if this.counter == 0 {
      item := -1;

    } else {
      item := this.circularQueue[this.front];
      this.front := (this.front + 1) % this.circularQueue.Length;
      this.counter := this.counter - 1;
    }
  }*/

  method size() returns (size:nat)
    ensures size == this.counter
  {
    size := this.counter;
  }

  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == true ==> this.counter == 0;
    ensures isEmpty == false ==> this.counter != 0;
  {
    isEmpty := if this.counter == 0 then true else false;
  }

  method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in this.circularQueue[..]
    ensures contains == false ==> item !in this.circularQueue[..]
  {
    var i: nat := 0;
    contains := false;

    while (i < this.circularQueue.Length)
      decreases this.circularQueue.Length - i
      invariant 0 <= i <= this.circularQueue.Length
      invariant !contains ==> forall j :: 0 <= j < i ==> this.circularQueue[j] != item
    {
      if (this.circularQueue[i] == item) {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }

  // TODO
  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue) 
  {
    
    // queue1.merge(queue2)
    var newQueueSize : int := otherQueue.circularQueue.Length + this.circularQueue.Length;
    var newFront: int := this.front;
    var newRear: int := otherQueue.rear;

    var tmp: array<int> := new int[newQueueSize];

    forall i | 0 <= i < this.circularQueue.Length
    { 
      tmp[i] := this.circularQueue[i];
    }

    // vamos copiar valores vazios?
    // como identificamos os vazios? entre o rear e o front
    // como iteramos entre rear e front? front -> rear
    // [1, 3, 5, 7, 9] + [0, 2, 4, 6, 8] => [0, 2, 4, 6, 8, 1, 3, 5, 7, 9]
    // front => 8 
    // rear => 0
    
    mergedQueue := new Queue(); 
  }
}

method Main ()
{
  var circularQueue := new Queue();
  assert circularQueue.circularQueue.Length == 0;
  assert circularQueue.Content == [];
  assert circularQueue.Content != [1];

  var isQueueEmpty := circularQueue.isEmpty();
  assert isQueueEmpty == true;

  var queueSize := circularQueue.size();
  assert queueSize == 0;

  circularQueue.auxInsertEmptyQueue(2);
  assert circularQueue.Content == [2];
  assert circularQueue.counter == 1;
  assert circularQueue.circularQueue.Length == 1;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 1;
  assert circularQueue.rear != 2;
  assert circularQueue.front != 2;

  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2,4];
  assert circularQueue.counter == 2;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 2;

  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2,4,4];
  assert circularQueue.counter == 3;

  circularQueue.auxInsertEndQueue(56);
  assert circularQueue.Content == [2,4,4,56];
  assert circularQueue.counter == 4;

  var contains56 := circularQueue.contains(56);
  assert contains56 == true;

  var contains4 := circularQueue.contains(4);
  assert contains4 == true;

  var item := circularQueue.remove();
  assert item == 2;
  //assert circularQueue.Content == [2, 4, 4, 56];

  assert (0 + 1) % 6 == 1;
  assert (1 + 1) % 6 == 2;
  assert (2 + 1) % 6 == 3;
  assert (3 + 1) % 6 == 4;
  assert (4 + 1) % 6 == 5;
  assert (5 + 1) % 6 == 0;
  assert (0 + 1) % 6 == 1;

}
