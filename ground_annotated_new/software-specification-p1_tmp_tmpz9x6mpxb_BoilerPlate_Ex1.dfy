function serialise<V>(t: Tree<V>): seq<Code<V>>
  decreases t
{
  match t {
    case Leaf(v) =>
      [CLf(v)]
    case SingleNode(v, t) =>
      serialise(t) + [CSNd(v)]
    case DoubleNode(v, t1, t2) =>
      serialise(t2) + serialise(t1) + [CDNd(v)]
  }
}
// pure-end

function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
  requires |codes| > 0 || |trees| > 0
  ensures |deserialiseAux(codes, trees)| >= 0
  decreases codes
{
  if |codes| == 0 then
    trees
  else
    match codes[0] { case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)]) case CSNd(v) => (if |trees| >= 1 then deserialiseAux(codes[1..], trees[..|trees| - 1] + [SingleNode(v, trees[|trees| - 1])]) else trees) case CDNd(v) => if |trees| >= 2 then deserialiseAux(codes[1..], trees[..|trees| - 2] + [DoubleNode(v, trees[|trees| - 1], trees[|trees| - 2])]) else trees }
}
// pure-end

function deserialise<T>(s: seq<Code<T>>): seq<Tree<T>>
  requires |s| > 0
{
  deserialiseAux(s, [])
}
// pure-end

method testSerializeWithASingleLeaf()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var tree := Leaf(42);
  var result := serialise(tree);
  // assert-start
  assert result == [CLf(42)];
  // assert-end

// impl-end
}

method testSerializeNullValues()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var tree := Leaf(null);
  var result := serialise(tree);
  // assert-start
  assert result == [CLf(null)];
  // assert-end

// impl-end
}

method testSerializeWithAllElements()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var tree: Tree<int> := DoubleNode(9, Leaf(6), DoubleNode(2, Leaf(5), SingleNode(4, Leaf(3))));
  var codes := serialise(tree);
  // assert-start
  assert |codes| == 6;
  // assert-end

  var expectedCodes := [CLf(3), CSNd(4), CLf(5), CDNd(2), CLf(6), CDNd(9)];
  // assert-start
  assert codes == expectedCodes;
  // assert-end

// impl-end
}

method testDeseraliseWithASingleLeaf()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var codes: seq<Code<int>> := [CLf(9)];
  var trees := deserialise(codes);
  // assert-start
  assert |trees| == 1;
  // assert-end

  var expectedTree := Leaf(9);
  // assert-start
  assert trees[0] == expectedTree;
  // assert-end

// impl-end
}

method testDeserializeWithASingleNode()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var codes: seq<Code<int>> := [CLf(3), CSNd(9), CLf(5)];
  var trees := deserialise(codes);
  // assert-start
  assert |trees| == 2;
  // assert-end

  var expectedTree1 := SingleNode(9, Leaf(3));
  var expectedTree2 := Leaf(5);
  // assert-start
  assert trees[0] == expectedTree1;
  // assert-end

  // assert-start
  assert trees[1] == expectedTree2;
  // assert-end

// impl-end
}

method testDeserialiseWithAllElements()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var codes: seq<Code<int>> := [CLf(3), CSNd(4), CLf(5), CDNd(2), CLf(6), CDNd(9)];
  var trees := deserialise(codes);
  // assert-start
  assert |trees| == 1;
  // assert-end

  var expectedTree := DoubleNode(9, Leaf(6), DoubleNode(2, Leaf(5), SingleNode(4, Leaf(3))));
  // assert-start
  assert trees[0] == expectedTree;
  // assert-end

// impl-end
}

lemma SerialiseLemma<V>(t: Tree<V>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures deserialise(serialise(t)) == [t]
  // post-conditions-end
{
// impl-start
  assert serialise(t) + [] == serialise(t);
  calc {
    deserialise(serialise(t));
  ==
    deserialise(serialise(t) + []);
  ==
    deserialiseAux(serialise(t) + [], []);
  ==
    {
      DeserialisetAfterSerialiseLemma(t, [], []);
    }
    deserialiseAux([], [] + [t]);
  ==
    deserialiseAux([], [t]);
  ==
    [t];
  }
// impl-end
}

lemma DeserialisetAfterSerialiseLemma<T>(t: Tree<T>, cds: seq<Code<T>>, ts: seq<Tree<T>>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t])
  // post-conditions-end
{
// impl-start
  match t {
    case {:split false} Leaf(x) =>
      calc {
        deserialiseAux(serialise(t) + cds, ts);
      ==
        deserialiseAux([CLf(x)] + cds, ts);
      ==
        deserialiseAux(cds, ts + [Leaf(x)]);
      ==
        deserialiseAux(cds, ts + [t]);
      }
    case {:split false} SingleNode(x, t1) =>
      assert serialise(t1) + [CSNd(x)] + cds == serialise(t1) + ([CSNd(x)] + cds);
      calc {
        deserialiseAux(serialise(t) + cds, ts);
      ==
        deserialiseAux(serialise(t1) + [CSNd(x)] + cds, ts);
      ==
        deserialiseAux(serialise(t1) + [CSNd(x)] + cds, ts);
      ==
        {
          DeserialisetAfterSerialiseLemma(t1, [CSNd(x)], ts);
        }
        deserialiseAux(serialise(t1) + [CSNd(x)] + cds, ts);
      ==
        deserialiseAux([CSNd(x)] + cds, ts + [t1]);
      ==
        deserialiseAux(cds, ts + [SingleNode(x, t1)]);
      ==
        deserialiseAux(cds, ts + [t]);
      }
    case {:split false} DoubleNode(x, t1, t2) =>
      assert serialise(t2) + serialise(t1) + [CDNd(x)] + cds == serialise(t2) + (serialise(t1) + [CDNd(x)] + cds);
      assert serialise(t1) + [CDNd(x)] + cds == serialise(t1) + ([CDNd(x)] + cds);
      assert ts + [t2] + [t1] == ts + [t2, t1];
      calc {
        deserialiseAux(serialise(t) + cds, ts);
      ==
        deserialiseAux(serialise(t2) + serialise(t1) + [CDNd(x)] + cds, ts);
      ==
        deserialiseAux(serialise(t2) + (serialise(t1) + [CDNd(x)] + cds), ts);
      ==
        {
          DeserialisetAfterSerialiseLemma(t2, serialise(t1) + [CDNd(x)], ts);
        }
        deserialiseAux(serialise(t1) + [CDNd(x)] + cds, ts + [t2]);
      ==
        deserialiseAux(serialise(t1) + ([CDNd(x)] + cds), ts + [t2]);
      ==
        {
          DeserialisetAfterSerialiseLemma(t1, [CDNd(x)] + cds, ts + [t2]);
        }
        deserialiseAux([CDNd(x)] + cds, ts + [t2] + [t1]);
      ==
        deserialiseAux([CDNd(x)] + cds, ts + [t2, t1]);
      ==
        deserialiseAux([CDNd(x)] + cds, ts + [t2, t1]);
      ==
        deserialiseAux(cds, ts + [DoubleNode(x, t1, t2)]);
      ==
        deserialiseAux(cds, ts + [t]);
      }
  }
// impl-end
}

datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)
