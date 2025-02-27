lemma NumPageElements()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists eltSet: set<HAlign> :: |eltSet| == 3
  ensures forall eltSet: set<HAlign> :: |eltSet| <= 3
  // post-conditions-end
{
// impl-start
  var maxSet := {Left, Center, Right};
  assert |maxSet| == 3;
  forall eltSet: set<HAlign> | true
    ensures |eltSet| <= 3
  {
    forall elt | elt in eltSet
      ensures elt in maxSet
    {
      if elt.Left? {
      }
    }
    subsetCardinality(eltSet, maxSet);
  }
// impl-end
}

lemma subsetCardinality<T>(a: set<T>, b: set<T>)
  // pre-conditions-start
  requires a <= b
  // pre-conditions-end
  // post-conditions-start
  ensures |a| <= |b|
  // post-conditions-end
{
// impl-start
  if a == {} {
    assert |a| <= |b|;
  } else {
    var e :| e in a;
    if e in b {
      subsetCardinality(a - {e}, b - {e});
      assert |a| <= |b|;
    } else {
      subsetCardinality(a - {e}, b);
      assert |a| <= |b|;
    }
  }
// impl-end
}

datatype HAlign = Left | Center | Right

datatype VAlign = Top | Middle | Bottom

datatype TextAlign = TextAlign(hAlign: HAlign, vAlign: VAlign)

datatype GraphicsAlign = Square | Round

datatype PageElement = Text(t: TextAlign) | Graphics(g: GraphicsAlign)
