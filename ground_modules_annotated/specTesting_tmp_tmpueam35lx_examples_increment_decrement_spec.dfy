// specTesting_tmp_tmpueam35lx_examples_increment_decrement_spec.dfy


module OneSpec {
  predicate Init(v: Variables)
  {
    v.value == 0
  }
  // pure-end

  predicate IncrementOp(v: Variables, v': Variables)
  {
    true &&
    v'.value == v.value + 1
  }
  // pure-end

  predicate DecrementOp(v: Variables, v': Variables)
  {
    true &&
    v'.value == v.value - 1
  }
  // pure-end

  predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step
    case IncrementStep() =>
      IncrementOp(v, v')
    case DecrementStep() =>
      DecrementOp(v, v')
  }
  // pure-end

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: 
      NextStep(v, v', step)
  }
  // pure-end

  datatype Variables = Variables(value: int)

  datatype Step = IncrementStep | DecrementStep
}

module OneProtocol {
  predicate Init(v: Variables)
  {
    v.value == 0
  }
  // pure-end

  predicate IncrementOp(v: Variables, v': Variables)
  {
    true &&
    v'.value == v.value - 1
  }
  // pure-end

  predicate DecrementOp(v: Variables, v': Variables)
  {
    true &&
    v'.value == v.value + 1
  }
  // pure-end

  predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step
    case IncrementStep() =>
      IncrementOp(v, v')
    case DecrementStep() =>
      DecrementOp(v, v')
  }
  // pure-end

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: 
      NextStep(v, v', step)
  }
  // pure-end

  datatype Variables = Variables(value: int)

  datatype Step = IncrementStep | DecrementStep
}

module RefinementProof {
  function Abstraction(v: Variables): OneSpec.Variables
  {
    OneSpec.Variables(v.value)
  }
  // pure-end

  lemma RefinementInit(v: Variables)
    // pre-conditions-start
    requires Init(v)
    // pre-conditions-end
    // post-conditions-start
    ensures OneSpec.Init(Abstraction(v))
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma RefinementNext(v: Variables, v': Variables)
    // pre-conditions-start
    requires Next(v, v')
    // pre-conditions-end
    // post-conditions-start
    ensures OneSpec.Next(Abstraction(v), Abstraction(v'))
    // post-conditions-end
  {
  // impl-start
    var step :| NextStep(v, v', step);
    match step {
      case {:split false} IncrementStep() =>
        {
          assert OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.DecrementStep());
        }
      case {:split false} DecrementStep() =>
        {
          assert OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.IncrementStep());
        }
    }
  // impl-end
  }

  import OneSpec

  import opened OneProtocol
}
