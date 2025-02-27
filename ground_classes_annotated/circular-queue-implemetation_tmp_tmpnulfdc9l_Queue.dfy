// circular-queue-implemetation_tmp_tmpnulfdc9l_Queue.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var circularQueue := new Queue();
  // assert-start
  assert circularQueue.circularQueue.Length == 0;
  // assert-end

  // assert-start
  assert circularQueue.Content == [];
  // assert-end

  // assert-start
  assert circularQueue.Content != [1];
  // assert-end

  var isQueueEmpty := circularQueue.isEmpty();
  // assert-start
  assert isQueueEmpty == true;
  // assert-end

  var queueSize := circularQueue.size();
  // assert-start
  assert queueSize == 0;
  // assert-end

  circularQueue.auxInsertEmptyQueue(2);
  // assert-start
  assert circularQueue.Content == [2];
  // assert-end

  // assert-start
  assert circularQueue.counter == 1;
  // assert-end

  // assert-start
  assert circularQueue.circularQueue.Length == 1;
  // assert-end

  // assert-start
  assert circularQueue.front == 0;
  // assert-end

  // assert-start
  assert circularQueue.rear == 1;
  // assert-end

  // assert-start
  assert circularQueue.rear != 2;
  // assert-end

  // assert-start
  assert circularQueue.front != 2;
  // assert-end

  circularQueue.auxInsertEndQueue(4);
  // assert-start
  assert circularQueue.Content == [2, 4];
  // assert-end

  // assert-start
  assert circularQueue.counter == 2;
  // assert-end

  // assert-start
  assert circularQueue.front == 0;
  // assert-end

  // assert-start
  assert circularQueue.rear == 2;
  // assert-end

  circularQueue.auxInsertEndQueue(4);
  // assert-start
  assert circularQueue.Content == [2, 4, 4];
  // assert-end

  // assert-start
  assert circularQueue.counter == 3;
  // assert-end

  circularQueue.auxInsertEndQueue(56);
  // assert-start
  assert circularQueue.Content == [2, 4, 4, 56];
  // assert-end

  // assert-start
  assert circularQueue.counter == 4;
  // assert-end

  var contains56 := circularQueue.contains(56);
  // assert-start
  assert contains56 == true;
  // assert-end

  var contains4 := circularQueue.contains(4);
  // assert-start
  assert contains4 == true;
  // assert-end

  var item := circularQueue.remove();
  // assert-start
  assert item == 2;
  // assert-end

  // assert-start
  assert (0 + 1) % 6 == 1;
  // assert-end

  // assert-start
  assert (1 + 1) % 6 == 2;
  // assert-end

  // assert-start
  assert (2 + 1) % 6 == 3;
  // assert-end

  // assert-start
  assert (3 + 1) % 6 == 4;
  // assert-end

  // assert-start
  assert (4 + 1) % 6 == 5;
  // assert-end

  // assert-start
  assert (5 + 1) % 6 == 0;
  // assert-end

  // assert-start
  assert (0 + 1) % 6 == 1;
  // assert-end

// impl-end
}

class {:autocontracts} Queue {
  var circularQueue: array<int>
  var rear: nat
  var front: nat
  var counter: nat
  ghost var Content: seq<int>

  ghost predicate Valid()
  {
    0 <= this.counter <= this.circularQueue.Length &&
    0 <= this.front &&
    0 <= this.rear &&
    this.Content == this.circularQueue[..]
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.circularQueue.Length == 0
    ensures this.front == 0 && this.rear == 0
    ensures this.Content == []
    ensures this.counter == 0
    // post-conditions-end
  {
  // impl-start
    this.circularQueue := new int[0];
    this.rear := 0;
    this.front := 0;
    this.Content := [];
    this.counter := 0;
  // impl-end
  }

  method insert(item: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  method auxInsertEmptyQueue(item: int)
    // pre-conditions-start
    requires this.front == 0 && this.rear == 0 && this.circularQueue.Length == 0
    // pre-conditions-end
    // post-conditions-start
    ensures this.circularQueue.Length == 1
    ensures this.Content == [item]
    ensures |this.Content| == 1
    ensures this.rear == 1
    ensures this.counter == old(this.counter) + 1
    ensures this.front == 0
    // post-conditions-end
  {
  // impl-start
    this.counter := this.counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int[this.circularQueue.Length + 1];
    queueInsert[0] := item;
    this.circularQueue := queueInsert;
    this.Content := [item];
    this.rear := this.rear + 1;
  // impl-end
  }

  method auxInsertEndQueue(item: int)
    // pre-conditions-start
    requires this.front == 0 && this.rear == this.circularQueue.Length && this.circularQueue.Length >= 1
    // pre-conditions-end
    // post-conditions-start
    ensures this.Content == old(this.Content) + [item]
    ensures |this.Content| == old(|this.Content|) + 1
    ensures this.front == 0
    ensures this.rear == old(this.rear) + 1
    ensures this.counter == old(this.counter) + 1
    // post-conditions-end

  method auxInsertSpaceQueue(item: int)
    // pre-conditions-start
    requires this.rear < this.front && this.front < this.circularQueue.Length
    // pre-conditions-end
    // post-conditions-start
    ensures this.rear == old(this.rear) + 1
    ensures this.counter == old(this.counter) + 1
    ensures this.Content == old(this.Content[0 .. this.rear]) + [item] + old(this.Content[this.rear + 1 .. this.circularQueue.Length])
    ensures |this.Content| == old(|this.Content|) + 1
    // post-conditions-end

  method auxInsertInitQueue(item: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end

  method auxInsertBetweenQueue(item: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end

  method remove() returns (item: int)
    // pre-conditions-start
    requires this.front < this.circularQueue.Length
    requires this.circularQueue.Length > 0
    // pre-conditions-end
    // post-conditions-start
    ensures this.rear <= |old(this.Content)|
    ensures this.circularQueue.Length > 0
    ensures item == old(this.Content)[old(this.front)]
    ensures this.front == (old(this.front) + 1) % this.circularQueue.Length
    ensures old(this.front) < this.rear ==> this.Content == old(this.Content)[old(this.front) .. this.rear]
    ensures old(this.front) > this.rear ==> this.Content == old(this.Content)[0 .. this.rear] + old(this.Content)[old(this.front) .. |old(this.Content)|]
    // post-conditions-end

  method size() returns (size: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures size == this.counter
    // post-conditions-end
  {
  // impl-start
    size := this.counter;
  // impl-end
  }

  method isEmpty() returns (isEmpty: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures isEmpty == true ==> this.counter == 0
    ensures isEmpty == false ==> this.counter != 0
    // post-conditions-end
  {
  // impl-start
    isEmpty := if this.counter == 0 then true else false;
  // impl-end
  }

  method contains(item: int) returns (contains: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures contains == true ==> item in this.circularQueue[..]
    ensures contains == false ==> item !in this.circularQueue[..]
    // post-conditions-end
  {
  // impl-start
    var i: nat := 0;
    contains := false;
    while i < this.circularQueue.Length
      // invariants-start

      invariant 0 <= i <= this.circularQueue.Length
      invariant !contains ==> forall j :: 0 <= j < i ==> this.circularQueue[j] != item
      decreases this.circularQueue.Length - i
      // invariants-end

    {
      if this.circularQueue[i] == item {
        contains := true;
        break;
      }
      i := i + 1;
    }
  // impl-end
  }

  method mergeQueues(otherQueue: Queue) returns (mergedQueue: Queue)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var newQueueSize: int := otherQueue.circularQueue.Length + this.circularQueue.Length;
    var newFront: int := this.front;
    var newRear: int := otherQueue.rear;
    var tmp: array<int> := new int[newQueueSize];
    forall i | 0 <= i < this.circularQueue.Length {
      tmp[i] := this.circularQueue[i];
    }
    mergedQueue := new Queue();
  // impl-end
  }
}
