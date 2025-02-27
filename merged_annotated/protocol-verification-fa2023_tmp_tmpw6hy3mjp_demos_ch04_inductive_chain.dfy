// protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_ch04_inductive_chain.dfy


module Ex {
  ghost predicate Init(v: Variables)
  {
    !v.p1 &&
    !v.p2 &&
    !v.p3 &&
    !v.p4
  }
  // pure-end

  ghost predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step {
      case Step1 =>
        !v.p1 &&
        v' == v.(p1 := true)
      case Step2 =>
        v.p1 &&
        v' == v.(p2 := true)
      case Step3 =>
        v.p2 &&
        v' == v.(p3 := true)
      case Step4 =>
        v.p3 &&
        v' == v.(p4 := true)
      case Noop =>
        v' == v
    }
  }
  // pure-end

  ghost predicate Next(v: Variables, v': Variables)
  {
    exists step: Step :: 
      NextStep(v, v', step)
  }
  // pure-end

  ghost predicate Safety(v: Variables)
  {
    v.p4 ==>
      v.p1
  }
  // pure-end

  ghost predicate Inv(v: Variables)
  {
    Safety(v) &&
    (v.p3 ==>
      v.p1) &&
    (v.p2 ==>
      v.p1)
  }
  // pure-end

  lemma InvInductive(v: Variables, v': Variables)
    // pre-conditions-start
    requires Inv(v) && Next(v, v')
    // pre-conditions-end
    // post-conditions-start
    ensures Inv(v')
    // post-conditions-end
  {
  // impl-start
    var step :| NextStep(v, v', step);
    assert NextStep(v, v', step);
    match step {
      case {:split false} Step1 =>
        {
          return;
        }
      case {:split false} Step2 =>
        {
          return;
        }
      case {:split false} Step3 =>
        {
          return;
        }
      case {:split false} Step4 =>
        {
          return;
        }
      case {:split false} Noop =>
        {
          return;
        }
    }
  // impl-end
  }

  lemma InvSafe(v: Variables)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Inv(v) ==> Safety(v)
    // post-conditions-end
  {
  // impl-start
    return;
  // impl-end
  }

  lemma SafetyHolds(v: Variables, v': Variables)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
    // post-conditions-end
  {
  // impl-start
    if Inv(v) && Next(v, v') {
      InvInductive(v, v');
    }
    InvSafe(v);
  // impl-end
  }

  predicate Inv2(v: Variables)
  {
    (v.p2 ==>
      v.p1) &&
    (v.p3 ==>
      v.p2) &&
    (v.p4 ==>
      v.p3)
  }
  // pure-end

  lemma Inv2Holds(v: Variables, v': Variables)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Init(v) ==> Inv2(v)
    ensures Inv2(v) && Next(v, v') ==> Inv2(v')
    // post-conditions-end
  {
  // impl-start
    assert Init(v) ==> Inv2(v);
    if Inv2(v) && Next(v, v') {
      var step :| NextStep(v, v', step);
      match step {
        case {:split false} Step1 =>
          {
            return;
          }
        case {:split false} Step2 =>
          {
            return;
          }
        case {:split false} Step3 =>
          {
            return;
          }
        case {:split false} Step4 =>
          {
            return;
          }
        case {:split false} Noop =>
          {
            return;
          }
      }
    }
  // impl-end
  }

  datatype Variables = Variables(p1: bool, p2: bool, p3: bool, p4: bool)

  datatype Step = Step1 | Step2 | Step3 | Step4 | Noop
}
