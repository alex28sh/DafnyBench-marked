// DafnyProjects_tmp_tmp2acw_s4s_Graph.dfy

method testGraph()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var G := new Graph<int>();
  // assert-start
  assert G.E == {} && G.V == {};
  // assert-end

  G.addVertex(1);
  G.addVertex(2);
  G.addVertex(3);
  G.addVertex(4);
  // assert-start
  assert G.V == {1, 2, 3, 4};
  // assert-end

  G.addEdge(1, 2);
  G.addEdge(1, 3);
  G.addEdge(2, 3);
  G.addEdge(4, 1);
  // assert-start
  assert G.E == {(1, 2), (1, 3), (2, 3), (4, 1)};
  // assert-end

  // assert-start
  assert G.getAdj(1) == {2, 3};
  // assert-end

  G.collapseVertices({1, 2, 3}, 3);
  // assert-start
  assert G.V == {3, 4} && G.E == {(4, 3)};
  // assert-end

// impl-end
}

class {:autocontracts} Graph<T(==)> {
  var V: set<T>
  var E: set<(T, T)>

  ghost predicate Valid()
  {
    forall e :: 
      e in this.E ==>
        e.0 in this.V &&
        e.1 in this.V &&
        e.0 != e.1
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.V == {} && this.E == {}
    // post-conditions-end
  {
  // impl-start
    this.V := {};
    this.E := {};
  // impl-end
  }

  method addVertex(v: T)
    // pre-conditions-start
    requires v !in this.V
    // pre-conditions-end
    // post-conditions-start
    ensures this.E == old(this.E) && this.V == old(this.V) + {v}
    // post-conditions-end
  {
  // impl-start
    this.V := this.V + {v};
  // impl-end
  }

  method addEdge(u: T, v: T)
    // pre-conditions-start
    requires u in this.V && v in this.V && (u, v) !in this.E && u != v
    // pre-conditions-end
    // post-conditions-start
    ensures this.V == old(this.V) && this.E == old(this.E) + {(u, v)}
    // post-conditions-end
  {
  // impl-start
    this.E := this.E + {(u, v)};
  // impl-end
  }

  function getAdj(v: T): set<T>
    requires v in this.V
  {
    set e | e in this.E && e.0 == v :: e.1
  }
  // pure-end

  method removeVertex(v: T)
    // pre-conditions-start
    requires v in this.V
    // pre-conditions-end
    // post-conditions-start
    ensures this.V == old(this.V) - {v}
    ensures this.E == set e | e in old(this.E) && e.0 != v && e.1 != v
    // post-conditions-end
  {
  // impl-start
    this.V := this.V - {v};
    this.E := set e | e in this.E && e.0 != v && e.1 != v;
  // impl-end
  }

  method collapseVertices(C: set<T>, v: T)
    // pre-conditions-start
    requires v in C && C <= this.V
    // pre-conditions-end
    // post-conditions-start
    ensures this.V == old(this.V) - C + {v}
    ensures this.E == set e | e in old(this.E) && (e.0 !in C || e.1 !in C) :: (if e.0 in C then v else e.0, if e.1 in C then v else e.1)
    // post-conditions-end
  {
  // impl-start
    this.V := this.V - C + {v};
    this.E := set e | e in this.E && (e.0 !in C || e.1 !in C) :: (if e.0 in C then v else e.0, if e.1 in C then v else e.1);
  // impl-end
  }
}
