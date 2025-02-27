class BoundedQueue<T(0)>
{
   // abstract state
   ghost var contents: seq<T> // the contents of the bounded queue
   ghost var N: nat // the (maximum) size of the bounded queue
   ghost var Repr: set<object>
   // concrete state
   var data: array<T>
   var wr: nat
   var rd: nat
   
   ghost predicate Valid()
      reads this, this.Repr
      ensures this.Valid() ==> this in this.Repr && |this.contents| <= this.N 
   {
      this in this.Repr && this.data in this.Repr &&
      this.data.Length == this.N + 1 &&
      this.wr <= this.N && this.rd <= this.N &&
      this.contents == if this.rd <= this.wr then this.data[this.rd..this.wr] else this.data[this.rd..] + this.data[..this.wr]
   }

   constructor (N: nat)
      ensures this.Valid() && fresh(this.Repr)
      ensures this.contents == [] && this.N == N
   {
      this.contents := [];
      this.N := N;
      this.data := new T[N+1]; // requires T to have default initial value
      this.rd, this.wr := 0, 0;
      this.Repr := {this, this.data};
   }

   method Insert(x:T)
      requires this.Valid()
      requires |this.contents| != this.N
      modifies this.Repr
      ensures this.contents == old(this.contents) + [x]
      ensures this.N == old(this.N)
      ensures this.Valid() && fresh(this.Repr - old(this.Repr))
   {
      this.contents := old(this.contents) + [x];

      this.data[this.wr] := x;
      assert (this.wr == this.data.Length -1 ==> this.contents == if this.rd <= 0 then this.data[this.rd..0] else this.data[this.rd..] + this.data[..0])
         && (this.wr != this.data.Length -1 ==> this.contents == if this.rd <= this.wr+1 then this.data[this.rd..this.wr+1] else this.data[this.rd..] + this.data[..this.wr+1]);
      if this.wr == this.data.Length -1 {
         assert this.contents == if this.rd <= 0 then this.data[this.rd..0] else this.data[this.rd..] + this.data[..0];
         this.wr := 0;
         assert this.contents == if this.rd <= this.wr then this.data[this.rd..this.wr] else this.data[this.rd..] + this.data[..this.wr];
      } else {
         assert this.contents == if this.rd <= this.wr+1 then this.data[this.rd..this.wr+1] else this.data[this.rd..] + this.data[..this.wr+1];
         this.wr := this.wr + 1;
         assert this.contents == if this.rd <= this.wr then this.data[this.rd..this.wr] else this.data[this.rd..] + this.data[..this.wr];
      }
      assert this.contents == if this.rd <= this.wr then this.data[this.rd..this.wr] else this.data[this.rd..] + this.data[..this.wr];
   }

   method Remove() returns (x:T)
      requires this.Valid()
      requires |this.contents| != 0
      modifies this.Repr
      ensures this.contents == old(this.contents[1..]) && old(this.contents[0]) == x
      ensures this.N == old(this.N)
      ensures this.Valid() && fresh(this.Repr - old(this.Repr))
   {
      this.contents := this.contents[1..];
      x := this.data[this.rd];
      if this.rd == this.data.Length - 1 {
         this.rd := 0;
      } else {
         this.rd := this.rd + 1;
      }
   }
}
