// dafny_experiments_tmp_tmpz29_3_3i_circuit.dfy


module Base {
  function n_iports(node: Node): nat
  {
    match node {
      case Xor =>
        2
      case And =>
        2
      case Ident =>
        1
    }
  }
  // pure-end

  function n_oports(node: Node): nat
  {
    match node {
      case Xor =>
        1
      case And =>
        1
      case Ident =>
        1
    }
  }
  // pure-end

  predicate WellformedBackConns(c: Circuit)
  {
    forall inp :: 
      inp in c.backconns ==>
        WellformedINP(c, inp) &&
        WellformedONP(c, c.backconns[inp])
  }
  // pure-end

  predicate WellformedINP(c: Circuit, inp: INodePort)
  {
    0 <= inp.node_id < |c.nodes| &&
    inp.port_id < n_iports(c.nodes[inp.node_id])
  }
  // pure-end

  predicate WellformedONP(c: Circuit, onp: ONodePort)
  {
    0 <= onp.node_id < |c.nodes| &&
    onp.port_id < n_oports(c.nodes[onp.node_id])
  }
  // pure-end

  function AllINPs(c: Circuit): set<INodePort>
    ensures forall inp :: inp in AllINPs(c) ==> WellformedINP(c, inp)
  {
    set node_id: nat, port_id: nat | 0 <= node_id < |c.nodes| && port_id < n_iports(c.nodes[node_id]) :: inodeport(node_id, port_id)
  }
  // pure-end

  function AllONPs(c: Circuit): set<ONodePort>
    ensures forall onp :: onp in AllONPs(c) ==> WellformedONP(c, onp)
  {
    set node_id: nat, port_id: nat | 0 < node_id < |c.nodes| && port_id < n_oports(c.nodes[node_id]) :: onodeport(node_id, port_id)
  }
  // pure-end

  ghost predicate Wellformed(c: Circuit)
  {
    WellformedBackConns(c)
  }
  // pure-end

  datatype INodePort = inodeport(node_id: nat, port_id: nat)

  datatype ONodePort = onodeport(node_id: nat, port_id: nat)

  datatype Node = Xor | And | Ident

  datatype Circuit = Circ(nodes: seq<Node>, backconns: map<INodePort, ONodePort>)
}

module Utils {
  function UpdateMap<T(!new), U>(A: map<T, U>, f: T -> T, g: U -> U): (result: map<T, U>)
    requires forall x: T, y: T :: x != y ==> f(x) != f(y)
    ensures forall x :: x in A <==> f(x) in result
    ensures forall x :: x in A ==> g(A[x]) == result[f(x)]
  {
    map x | x in A :: f(x) := g(A[x])
  }
  // pure-end

  function CombineMaps<T(!new), U>(a: map<T, U>, b: map<T, U>): map<T, U>
    requires forall x :: x in a ==> x !in b
    requires forall x :: x in b ==> x !in a
    ensures var result := CombineMaps(a, b); (forall x :: x in a ==> a[x] == result[x]) && (forall x :: x in b ==> b[x] == result[x]) && forall x :: x in result ==> x in a || x in b
  {
    map x | x in a.Keys + b.Keys :: if x in a then a[x] else b[x]
  }
  // pure-end

  function sub(a: nat, b: nat): nat
    requires b <= a
  {
    a - b
  }
  // pure-end
}

module BackwardConnections {
  function CombineBackconns(offset: nat, bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>): (result: map<INodePort, ONodePort>)
    requires forall inp :: inp in bc1 ==> inp.node_id < offset
  {
    var f := (inp: INodePort) => inodeport(inp.node_id + offset, inp.port_id);
    var g := (onp: ONodePort) => onodeport(onp.node_id + offset, onp.port_id);
    var backconns2 := UpdateMap(bc2, f, g);
    CombineMaps(bc1, backconns2)
  }
  // pure-end

  lemma CombineBackconnsHelper(offset: nat, bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>)
    // pre-conditions-start
    requires forall inp :: inp in bc1 ==> inp.node_id < offset
    requires result == CombineBackconns(offset, bc1, bc2)
    // pre-conditions-end
    // post-conditions-start
    ensures forall inp :: inp in bc1 ==> inp in result && result[inp] == bc1[inp]
    ensures forall inp :: inp in bc2 ==> inodeport(inp.node_id + offset, inp.port_id) in result && result[inodeport(inp.node_id + offset, inp.port_id)] == onodeport(bc2[inp].node_id + offset, bc2[inp].port_id)
    // post-conditions-end
  {
  // impl-start
    var f := (inp: INodePort) => inodeport(inp.node_id + offset, inp.port_id);
    var g := (onp: ONodePort) => onodeport(onp.node_id + offset, onp.port_id);
    var backconns2 := UpdateMap(bc2, f, g);
    assert forall inp :: inp in bc2 ==> inodeport(inp.node_id + offset, inp.port_id) in backconns2;
    assert backconns2 == UpdateMap(bc2, f, g);
  // impl-end
  }

  lemma CombineBackconnsHelper2(offset: nat, bc1: map<INodePort, ONodePort>, bc2: map<INodePort, ONodePort>, result: map<INodePort, ONodePort>, inp: INodePort)
    // pre-conditions-start
    requires forall inp :: inp in bc1 ==> inp.node_id < offset
    requires result == CombineBackconns(offset, bc1, bc2)
    requires inp in bc2
    // pre-conditions-end
    // post-conditions-start
    ensures inodeport(inp.node_id + offset, inp.port_id) in result
    ensures result[inodeport(inp.node_id + offset, inp.port_id)] == onodeport(bc2[inp].node_id + offset, bc2[inp].port_id)
    // post-conditions-end
  {
  // impl-start
    CombineBackconnsHelper(offset, bc1, bc2, result);
  // impl-end
  }

  import opened Base

  import opened Utils
}

module CombineCircuits {
  function CombineCircuits(c1: Circuit, c2: Circuit): (r: Circuit)
    requires Wellformed(c1)
    requires Wellformed(c2)
  {
    var new_nodes := c1.nodes + c2.nodes;
    var new_backconns := BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns);
    Circ(new_nodes, new_backconns)
  }
  // pure-end

  predicate IsEquivalentCircuit(node_is_member: nat -> bool, node_map: nat --> nat, c1: Circuit, c2: Circuit)
    requires forall inp :: inp in c1.backconns && node_is_member(inp.node_id) ==> node_is_member(c1.backconns[inp].node_id)
    requires forall n :: node_is_member(n) ==> node_map.requires(n)
  {
    forall inp :: 
      inp in c1.backconns &&
      node_is_member(inp.node_id) ==>
        inodeport(node_map(inp.node_id), inp.port_id) in c2.backconns &&
        var inp2 := inodeport(node_map(inp.node_id), inp.port_id); var onp := c1.backconns[inp]; onodeport(node_map(onp.node_id), onp.port_id) == c2.backconns[inp2]
  }
  // pure-end

  predicate CanBackAssign(c1: Circuit, c2: Circuit, r: Circuit, is_in_c1: nat -> bool, is_in_c2: nat -> bool, map_r_to_c1: nat -> nat, map_r_to_c2: nat --> nat)
    requires forall a :: is_in_c1(a) ==> map_r_to_c1.requires(a)
    requires forall a :: is_in_c2(a) ==> map_r_to_c2.requires(a)
    requires Wellformed(c1)
    requires Wellformed(c2)
  {
    (forall inp :: 
      inp in AllINPs(r) ==>
        (is_in_c1(inp.node_id) || is_in_c2(inp.node_id)) &&
        if is_in_c1(inp.node_id) then WellformedINP(c1, inodeport(map_r_to_c1(inp.node_id), inp.port_id)) else WellformedINP(c2, inodeport(map_r_to_c2(inp.node_id), inp.port_id))) &&
    (forall onp :: 
      onp in AllONPs(r) ==>
        (is_in_c1(onp.node_id) || is_in_c2(onp.node_id)) &&
        if is_in_c1(onp.node_id) then WellformedONP(c1, onodeport(map_r_to_c1(onp.node_id), onp.port_id)) else WellformedONP(c2, onodeport(map_r_to_c2(onp.node_id), onp.port_id))) &&
    true
  }
  // pure-end

  lemma CombineCircuitsCorrectHelper(c1: Circuit, c2: Circuit, r: Circuit)
    // pre-conditions-start
    requires Wellformed(c1)
    requires Wellformed(c2)
    requires r_is_result: r == CombineCircuits(c1, c2)
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert r.backconns == BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns) by {
      reveal r_is_result;
    }
  // impl-end
  }

  lemma CombineCircuitsCorrectC1(c1: Circuit, c2: Circuit, r: Circuit)
    // pre-conditions-start
    requires Wellformed(c1)
    requires Wellformed(c2)
    requires r == CombineCircuits(c1, c2)
    // pre-conditions-end
    // post-conditions-start
    ensures var offset := |c1.nodes|; IsEquivalentCircuit(a => true, a => a, c1, r) && IsEquivalentCircuit(a => a < offset, a => a, r, c1)
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma CombineCircuitsCorrect(c1: Circuit, c2: Circuit, r: Circuit)
    // pre-conditions-start
    requires Wellformed(c1)
    requires Wellformed(c2)
    requires r_is_result: r == CombineCircuits(c1, c2)
    // pre-conditions-end
    // post-conditions-start
    ensures var offset := |c1.nodes|; IsEquivalentCircuit(a => true, a => a, c1, r) && IsEquivalentCircuit(a => a < offset, a => a, r, c1) && IsEquivalentCircuit(a => true, a => a + offset, c2, r) && true
    // post-conditions-end
  {
  // impl-start
    var offset := |c1.nodes|;
    var node_is_member := a => true;
    var node_map := a => a + offset;
    calc {
      IsEquivalentCircuit(node_is_member, node_map, c2, r);
      forall inp :: 
        inp in c2.backconns &&
        node_is_member(inp.node_id) ==>
          inodeport(node_map(inp.node_id), inp.port_id) in r.backconns &&
          var inp2 := inodeport(node_map(inp.node_id), inp.port_id); var onp := c2.backconns[inp]; onodeport(node_map(onp.node_id), onp.port_id) == r.backconns[inp2];
      forall inp :: 
        inp in c2.backconns ==>
          inodeport(inp.node_id + offset, inp.port_id) in r.backconns &&
          var inp2 := inodeport(inp.node_id + offset, inp.port_id); var onp := c2.backconns[inp]; onodeport(onp.node_id + offset, onp.port_id) == r.backconns[inp2];
    }
    assert basic_result: r.backconns == BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns) by {
      reveal r_is_result;
    }
    forall inp | inp in c2.backconns {
      calc {
        inodeport(inp.node_id + offset, inp.port_id) in r.backconns &&
        var inp2 := inodeport(inp.node_id + offset, inp.port_id); var onp := c2.backconns[inp]; onodeport(onp.node_id + offset, onp.port_id) == r.backconns[inp2];
        {
          reveal basic_result;
        }
        inodeport(inp.node_id + offset, inp.port_id) in BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns) &&
        var inp2 := inodeport(inp.node_id + offset, inp.port_id); var onp := c2.backconns[inp]; onodeport(onp.node_id + offset, onp.port_id) == BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns)[inp2];
        inodeport(inp.node_id + offset, inp.port_id) in BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns) &&
        var inp2 := inodeport(inp.node_id + offset, inp.port_id); var onp := c2.backconns[inp]; onodeport(onp.node_id + offset, onp.port_id) == BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns)[inp2];
        {
          var inp2 := inodeport(inp.node_id + offset, inp.port_id);
          BackwardConnections.CombineBackconnsHelper2(offset, c1.backconns, c2.backconns, BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns), inp);
          assert BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns)[inp2] == onodeport(c2.backconns[inp].node_id + offset, c2.backconns[inp].port_id);
          assert inodeport(inp.node_id + offset, inp.port_id) in BackwardConnections.CombineBackconns(|c1.nodes|, c1.backconns, c2.backconns);
        }
        true;
      }
    }
    reveal r_is_result;
    CombineCircuitsCorrectC1(c1, c2, r);
  // impl-end
  }

  import opened Base

  import BackwardConnections

  import opened Utils
}
