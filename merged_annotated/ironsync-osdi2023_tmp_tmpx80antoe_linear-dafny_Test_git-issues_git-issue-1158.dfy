function F(s: set<Id>): int
// pure-end

lemma Test(x: Id)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var X := {x};
  var a := map i | i <= X :: F(i);
  var b := map[{} := F({}), X := F(X)];
  assert a.Keys == b.Keys by {
    forall i | true
      ensures i in a.Keys <==> i in b.Keys
    {
      calc {
        i in a.Keys;
      ==
        i <= X;
      ==
        {
          assert i <= X <==> i == {} || i == X;
        }
        i in b.Keys;
      }
    }
  }
// impl-end
}

type Id(==,!new)
