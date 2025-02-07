function Init(v: Variables): bool
// pure-end

function Next(v: Variables, v': Variables): bool
// pure-end

function Safety(v: Variables): bool
// pure-end

function Inv(v: Variables): bool
// pure-end

lemma InvHoldsTo(e: nat -> Variables, i: nat)
  // pre-conditions-start
  requires Inv(e(0))
  requires forall i: nat :: Next(e(i), e(i + 1))
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(e(i))
  // post-conditions-end
{
// impl-start
  if i == 0 {
    return;
  }
  InvHoldsTo(e, i - 1);
  assert Inv(e(i - 1));
  assert forall i: nat :: Inv(e(i)) ==> Inv(e(i + 1));
// impl-end
}

function IsBehavior(e: Behavior): bool
{
  Init(e(0)) &&
  forall i: nat :: 
    Next(e(i), e(i + 1))
}
// pure-end

lemma SafetyAlwaysHolds(e: Behavior)
  // pre-conditions-start
  requires forall v :: Init(v) ==> Inv(v)
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  requires forall v :: Inv(v) ==> Safety(v)
  // pre-conditions-end
  // post-conditions-start
  ensures IsBehavior(e) ==> forall i :: Safety(e(i))
  // post-conditions-end
{
// impl-start
  if IsBehavior(e) {
    assert Inv(e(0));
    forall i: nat | true
      ensures Safety(e(i))
    {
      InvHoldsTo(e, i);
    }
  }
// impl-end
}

type Variables(!new)

type Behavior = nat -> Variables
