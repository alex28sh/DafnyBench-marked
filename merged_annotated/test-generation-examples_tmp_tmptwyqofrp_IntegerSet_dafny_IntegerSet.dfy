

module IntegerSet {
  class Set {
    var elements: seq<int>

    constructor Set0()
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.elements == []
      ensures |this.elements| == 0
      // post-conditions-end
    {
    // impl-start
      this.elements := [];
    // impl-end
    }

    constructor Set(elements: seq<int>)
      // pre-conditions-start
      requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
      // pre-conditions-end
      // post-conditions-start
      ensures this.elements == elements
      ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && j != i :: this.elements[i] != this.elements[j]
      // post-conditions-end
    {
    // impl-start
      this.elements := elements;
    // impl-end
    }

    method size() returns (size: int)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures size == |this.elements|
      // post-conditions-end
    {
    // impl-start
      size := |elements|;
    // impl-end
    }

    method addElement(element: int)
      // pre-conditions-start
      requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && j != i :: this.elements[i] != this.elements[j]
      // pre-conditions-end
      // post-conditions-start
      modifies this`elements
      ensures element in old(this.elements) ==> this.elements == old(this.elements)
      ensures element !in old(this.elements) ==> |this.elements| == |old(this.elements)| + 1 && element in this.elements && forall i: int :: i in old(this.elements) ==> i in this.elements
      ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && j != i :: this.elements[i] != this.elements[j]
      // post-conditions-end
    {
    // impl-start
      if element !in elements {
        elements := elements + [element];
      }
    // impl-end
    }

    method removeElement(element: int)
      // pre-conditions-start
      requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && j != i :: this.elements[i] != this.elements[j]
      // pre-conditions-end
      // post-conditions-start
      modifies this`elements
      ensures element in old(this.elements) ==> |this.elements| == |old(this.elements)| - 1 && (forall i: int :: i in old(this.elements) && i != element <==> i in this.elements) && element !in this.elements
      ensures element !in old(this.elements) ==> this.elements == old(this.elements)
      ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && j != i :: this.elements[i] != this.elements[j]
      // post-conditions-end
    {
    // impl-start
      if element in elements {
        var i := 0;
        while 0 <= i < |elements|
          // invariants-start

          invariant 0 <= i < |elements|
          invariant forall j: int :: 0 <= j < i < |elements| ==> elements[j] != element
          decreases |elements| - i
          // invariants-end

        {
          if elements[i] == element {
            if i < |elements| - 1 && i != -1 {
              elements := elements[..i] + elements[i + 1..];
            } else if i == |elements| - 1 {
              elements := elements[..i];
            }
            break;
          }
          i := i + 1;
        }
      }
    // impl-end
    }

    method contains(element: int) returns (contains: bool)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures contains == (element in this.elements)
      ensures this.elements == old(this.elements)
      // post-conditions-end
    {
    // impl-start
      contains := false;
      if element in elements {
        contains := true;
      }
    // impl-end
    }

    function intersect_length(s1: seq<int>, s2: seq<int>, count: int, start: int, stop: int): int
      requires 0 <= start <= stop
      requires stop <= |s1|
      decreases stop - start
    {
      if start == stop then
        count
      else if s1[start] in s2 then
        intersect_length(s1, s2, count + 1, start + 1, stop)
      else
        intersect_length(s1, s2, count, start + 1, stop)
    }
    // pure-end

    function union_length(s1: seq<int>, s2: seq<int>, count: int, i: int, stop: int): int
      requires 0 <= i <= stop
      requires stop <= |s1|
      decreases stop - i
    {
      if i == stop then
        count
      else if s1[i] !in s2 then
        union_length(s1, s2, count + 1, i + 1, stop)
      else
        union_length(s1, s2, count, i + 1, stop)
    }
    // pure-end

    method intersect(s: Set) returns (intersection: Set)
      // pre-conditions-start
      requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
      requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
      // pre-conditions-end
      // post-conditions-start
      ensures forall i: int :: i in intersection.elements <==> i in s.elements && i in this.elements
      ensures forall i: int :: i !in intersection.elements <==> i !in s.elements || i !in this.elements
      ensures forall j, k | 0 <= j < |intersection.elements| && 0 <= k < |intersection.elements| && j != k :: intersection.elements[j] != intersection.elements[k]
      ensures fresh(intersection)
      // post-conditions-end
    {
    // impl-start
      intersection := new Set.Set0();
      var inter: seq<int> := [];
      var i := 0;
      while 0 <= i < |this.elements|
        // invariants-start

        invariant 0 <= i < |this.elements| || i == 0
        invariant forall j, k | 0 <= j < |inter| && 0 <= k < |inter| && j != k :: inter[j] != inter[k]
        invariant forall j :: 0 <= j < i < |this.elements| ==> (this.elements[j] in inter <==> this.elements[j] in s.elements)
        invariant forall j :: 0 <= j < |inter| ==> inter[j] in this.elements && inter[j] in s.elements
        invariant |inter| <= i <= |this.elements|
        decreases |this.elements| - i
        // invariants-end

      {
        var old_len := |inter|;
        if this.elements[i] in s.elements && this.elements[i] !in inter {
          inter := inter + [this.elements[i]];
        }
        if i == |this.elements| - 1 {
          // assert-start
          assert old_len + 1 == |inter| || old_len == |inter|;
          // assert-end

          break;
        }
        // assert-start
        assert old_len + 1 == |inter| || old_len == |inter|;
        // assert-end

        i := i + 1;
      }
      intersection.elements := inter;
    // impl-end
    }

    method union(s: Set) returns (union: Set)
      // pre-conditions-start
      requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
      requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
      // pre-conditions-end
      // post-conditions-start
      ensures forall i: int :: i in s.elements || i in this.elements <==> i in union.elements
      ensures forall i: int :: i !in s.elements && i !in this.elements <==> i !in union.elements
      ensures forall j, k | 0 <= j < |union.elements| && 0 <= k < |union.elements| && j != k :: union.elements[j] != union.elements[k]
      ensures fresh(union)
      // post-conditions-end
    {
    // impl-start
      var elems := s.elements;
      union := new Set.Set0();
      var i := 0;
      while 0 <= i < |this.elements|
        // invariants-start

        invariant 0 <= i < |this.elements| || i == 0
        invariant forall j: int :: 0 <= j < |s.elements| ==> s.elements[j] in elems
        invariant forall j: int :: 0 <= j < i < |this.elements| ==> (this.elements[j] in elems <==> this.elements[j] in s.elements || this.elements[j] in this.elements)
        invariant forall j :: 0 <= j < |elems| ==> elems[j] in this.elements || elems[j] in s.elements
        invariant forall j, k :: 0 <= j < |elems| && 0 <= k < |elems| && j != k ==> elems[j] != elems[k]
        decreases |this.elements| - i
        // invariants-end

      {
        if this.elements[i] !in elems {
          elems := elems + [this.elements[i]];
        }
        if i == |this.elements| - 1 {
          break;
        }
        i := i + 1;
      }
      union.elements := elems;
    // impl-end
    }
  }
}
