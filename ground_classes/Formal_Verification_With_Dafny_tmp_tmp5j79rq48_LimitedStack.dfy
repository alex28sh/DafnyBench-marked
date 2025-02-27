// A LIFO queue (aka a stack) with limited capacity.
class LimitedStack{
 
      var capacity : int; // capacity, max number of elements allowed on the stack.
      var arr : array<int>; // contents of stack.
      var top : int; // The index of the top of the stack, or -1 if the stack is empty

      // This predicate express a class invariant: All objects of this calls should satisfy this.
      predicate Valid()
      reads this;
      {
        this.arr != null && this.capacity > 0 && this.capacity == this.arr.Length &&  this.top >= -1 && this.top < this.capacity 
      }

      predicate Empty()
      reads `top;
      {
            this.top == -1
      }

      predicate Full()
      reads `top, `capacity;
      {
        this.top == (this.capacity - 1)
      }
  
      method Init(c : int)
      modifies this;
      requires c > 0
      ensures this.Valid() && this.Empty() && c == this.capacity
      ensures fresh(this.arr); // ensures arr is a newly created object.
      // Additional post-condition to be given here!
      {
        this.capacity := c;
        this.arr := new int[c];
        this.top := -1;
      }


      
      method isEmpty() returns (res : bool)
      ensures res == this.Empty()
      {
        if(this.top == -1)
        { return true; }
        else {
              return false;
        }
      }



      // Returns the top element of the stack, without removing it.
      method Peek() returns (elem : int) 
      requires this.Valid() && !this.Empty()
      ensures elem == this.arr[this.top]
      {
            return this.arr[this.top]; 
      }



      // Pushed an element to the top of a (non full) stack. 
      method Push(elem : int)
      modifies `top, this.arr 
      requires this.Valid()
      requires !this.Full() 
      ensures this.Valid() && this.top == old(this.top) + 1 && this.arr[this.top] == elem
      ensures !old(this.Empty()) ==> forall i : int :: 0 <= i <= old(this.top)  ==> this.arr[i] == old(this.arr[i]);
      {
            this.top := this.top + 1;
            this.arr[this.top] := elem;
      }

      // Pops the top element off the stack.

      method Pop() returns (elem : int)
      modifies   `top
      requires this.Valid() && !this.Empty()  
      ensures this.Valid()  && this.top == old(this.top) - 1 
      ensures elem == this.arr[old(this.top)] 
      {
            elem := this.arr[this.top];
            this.top := this.top - 1;
            return elem;
      }

 
      method Shift()
      requires this.Valid() && !this.Empty();
      ensures this.Valid();
      ensures forall i : int :: 0 <= i < this.capacity - 1 ==> this.arr[i] == old(this.arr[i + 1]);
      ensures this.top == old(this.top) - 1;
      modifies this.arr, `top;
      {
        var i : int := 0;
        while (i < this.capacity - 1 )
        invariant 0 <= i < this.capacity;
        invariant this.top == old(this.top);
        invariant forall j : int :: 0 <= j < i ==> this.arr[j] == old(this.arr[j + 1]);
        invariant forall j : int :: i <= j < this.capacity ==> this.arr[j] == old(this.arr[j]);
        {
          this.arr[i] := this.arr[i + 1];
          i := i + 1;
        }
        this.top := this.top - 1;
      }

 
      //Push onto full stack, oldest element is discarded.
      method Push2(elem : int)
      modifies this.arr, `top
      requires this.Valid()
      ensures this.Valid() && !this.Empty() 
      ensures this.arr[this.top] == elem
      ensures old(!this.Full()) ==> this.top == old(this.top) + 1 && old(this.Full()) ==> this.top == old(this.top)
      ensures ((old(this.Full()) ==> this.arr[this.capacity - 1] == elem)  && (old(!this.Full()) ==> (this.top == old(this.top) + 1 && this.arr[this.top] == elem) ))
      ensures old(this.Full()) ==> forall i : int :: 0 <= i < this.capacity - 1 ==> this.arr[i] == old(this.arr[i + 1]);
      {
            if(top == capacity - 1){
                  Shift();
                  top := top + 1;
                  this.arr[this.top] := elem;
            }
            else{
                  top := top + 1;
                  this.arr[this.top] := elem;
            }
      }
 

 

// When you are finished,  all the below assertions should be provable. 
// Feel free to add extra ones as well.
      method Main(){
           var s := new LimitedStack;
           s.Init(3);

           assert s.Empty() && !s.Full(); 

           s.Push(27);
           assert !s.Empty();

           var e := s.Pop();
           assert e == 27;

           assert s.top == -1; 
           assert s.Empty() && !s.Full(); 
           
           s.Push(5);

           assert s.top == 0;
           assert s.capacity == 3;
           s.Push(32);
           s.Push(9);
           assert s.Full();

           assert s.arr[0] == 5;

           var e2 := s.Pop();
           
           assert e2 == 9 && !s.Full(); 
           assert s.arr[0] == 5;

           s.Push(e2);
           s.Push2(99);

           var e3 := s.Peek();
           assert e3 == 99;
           assert s.arr[0] == 32;
                     
       }

}
