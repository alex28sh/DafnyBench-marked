

module ModelingTM {
  method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
    // pre-conditions-start
    requires pid in input.txQueues
    requires pid in input.procStates
    requires input.validSystem()
    // pre-conditions-end
    // post-conditions-start
    ensures system.validSystem()
    // post-conditions-end
  {
  // impl-start
    system := input;
    var state: ProcessState := system.procStates[pid];
    // assert-start
    assert system.stateValid(pid, state);
    // assert-end

    var txs := system.txQueues[pid];
    if state.currentTx >= |txs| {
      return;
    }
    var tx := txs[state.currentTx];
    if state.currentOp == |tx.ops| {
      if state.currentSubOp == 0 {
        if !forall o :: o in state.readSet ==> o in state.writeSet || o !in system.lockedObjs {
          state := new ProcessState.abortTx(state);
          system := new TMSystem.updateState(system, pid, state);
          // assert-start
          assume system.validSystem();
          // assert-end

          return;
        }
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 1 {
        if !forall o :: o in state.readSet ==> state.readSet[o] == system.objTimeStamps[o] {
          state := new ProcessState.abortTx(state);
          system := new TMSystem.updateState(system, pid, state);
          // assert-start
          assume system.validSystem();
          // assert-end

          return;
        }
        system := new TMSystem.clearDirty(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 2 {
        system := new TMSystem.updateTimestamps(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 3 {
        system := new TMSystem.releaseLocks(system, state.writeSet);
        state := new ProcessState.nextTx(state);
      } else {
        // assert-start
        assert false;
        // assert-end

      }
    } else if state.currentOp == -1 {
      if state.currentSubOp == 0 {
        // assert-start
        assert state.currentTx < |system.txQueues[pid]|;
        // assert-end

        system := new TMSystem.clearDirty(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 1 {
        system := new TMSystem.updateTimestamps(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 2 {
        system := new TMSystem.releaseLocks(system, state.writeSet);
        state := new ProcessState.restartTx(state);
      } else {
        // assert-start
        assert false;
        // assert-end

      }
    } else if state.currentOp >= 0 && state.currentOp < |tx.ops| {
      var op := tx.ops[state.currentOp];
      var o := op.memObject;
      if o !in system.objTimeStamps {
        system := new TMSystem.initTimestamp(system, o);
      }
      // assert-start
      assert o in system.objTimeStamps;
      // assert-end

      if op.isWrite {
        if state.currentSubOp == 0 {
          if !(op.memObject in state.writeSet) {
            if o in system.lockedObjs {
              state := new ProcessState.abortTx(state);
            } else {
              system := new TMSystem.acquireLock(system, o);
              state := new ProcessState.addToWriteSet(state, o);
              state := new ProcessState.nextSubOp(state);
            }
          } else {
            state := new ProcessState.nextSubOp(state);
          }
        } else if state.currentSubOp == 1 {
          system := new TMSystem.markDirty(system, o);
          state := new ProcessState.nextOp(state);
        } else {
          // assert-start
          assert false;
          // assert-end

        }
      } else {
        if state.currentSubOp == 0 {
          if o in state.writeSet || o in state.readSet {
            state := new ProcessState.nextOp(state);
          } else {
            state := new ProcessState.addToReadSet(state, o, system.objTimeStamps[o]);
            state := new ProcessState.nextSubOp(state);
          }
        } else if state.currentSubOp == 1 {
          if o in system.lockedObjs {
            state := new ProcessState.abortTx(state);
          } else {
            state := new ProcessState.nextOp(state);
          }
        } else {
          // assert-start
          assert false;
          // assert-end

        }
      }
    } else {
      // assert-start
      assert false;
      // assert-end

    }
    system := new TMSystem.updateState(system, pid, state);
    // assert-start
    assume system.validSystem();
    // assert-end

  // impl-end
  }

  type ProcessId = nat

  type MemoryObject = nat

  type TimeStamp = nat

  class Operation {
    const isWrite: bool
    const memObject: MemoryObject
  }

  class Transaction {
    const ops: seq<Operation>
  }

  class ProcessState {
    const currentTx: nat
    const currentOp: int
    const currentSubOp: nat
    const readSet: map<MemoryObject, TimeStamp>
    const writeSet: set<MemoryObject>

    constructor ()
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end
    {
    // impl-start
      currentTx := 0;
      currentOp := 0;
      currentSubOp := 0;
      readSet := map[];
      writeSet := {};
    // impl-end
    }

    constructor nextSubOp(that: ProcessState)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == that.currentOp
      ensures this.currentSubOp == that.currentSubOp + 1
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet
      // post-conditions-end
    {
    // impl-start
      currentTx := that.currentTx;
      currentOp := that.currentOp;
      currentSubOp := that.currentSubOp + 1;
      readSet := that.readSet;
      writeSet := that.writeSet;
    // impl-end
    }

    constructor nextOp(that: ProcessState)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == that.currentOp + 1
      ensures this.currentSubOp == 0
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet
      // post-conditions-end
    {
    // impl-start
      currentTx := that.currentTx;
      currentOp := that.currentOp + 1;
      currentSubOp := 0;
      readSet := that.readSet;
      writeSet := that.writeSet;
    // impl-end
    }

    constructor abortTx(that: ProcessState)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == -1
      ensures this.currentSubOp == 0
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet
      // post-conditions-end
    {
    // impl-start
      currentTx := that.currentTx;
      currentOp := -1;
      currentSubOp := 0;
      readSet := that.readSet;
      writeSet := that.writeSet;
    // impl-end
    }

    constructor restartTx(that: ProcessState)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == 0
      ensures this.currentSubOp == 0
      ensures this.readSet == map[]
      ensures this.writeSet == {}
      // post-conditions-end
    {
    // impl-start
      currentTx := that.currentTx;
      currentOp := 0;
      currentSubOp := 0;
      readSet := map[];
      writeSet := {};
    // impl-end
    }

    constructor nextTx(that: ProcessState)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.currentTx == that.currentTx + 1
      ensures this.currentOp == 0
      ensures this.currentSubOp == 0
      ensures this.readSet == map[]
      ensures this.writeSet == {}
      // post-conditions-end
    {
    // impl-start
      currentTx := that.currentTx + 1;
      currentOp := 0;
      currentSubOp := 0;
      readSet := map[];
      writeSet := {};
    // impl-end
    }

    constructor addToReadSet(that: ProcessState, obj: MemoryObject, ts: TimeStamp)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures currentTx == that.currentTx
      ensures currentOp == that.currentOp
      ensures currentSubOp == that.currentSubOp
      ensures readSet.Keys == that.readSet.Keys + {obj} && readSet[obj] == ts && forall o :: o in readSet && o != obj ==> readSet[o] == that.readSet[o]
      ensures writeSet == that.writeSet
      // post-conditions-end
    {
    // impl-start
      currentTx := that.currentTx;
      currentOp := that.currentOp;
      currentSubOp := that.currentSubOp;
      readSet := that.readSet[obj := ts];
      writeSet := that.writeSet;
    // impl-end
    }

    constructor addToWriteSet(that: ProcessState, obj: MemoryObject)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == that.currentOp
      ensures this.currentSubOp == that.currentSubOp
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet + {obj}
      // post-conditions-end
    {
    // impl-start
      currentTx := that.currentTx;
      currentOp := that.currentOp;
      currentSubOp := that.currentSubOp;
      readSet := that.readSet;
      writeSet := that.writeSet + {obj};
    // impl-end
    }
  }

  class TMSystem {
    const txQueues: map<ProcessId, seq<Transaction>>
    const procStates: map<ProcessId, ProcessState>
    const dirtyObjs: set<MemoryObject>
    const lockedObjs: set<MemoryObject>
    const objTimeStamps: map<MemoryObject, nat>

    constructor (q: map<ProcessId, seq<Transaction>>)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end
    {
    // impl-start
      txQueues := q;
      procStates := map[];
      dirtyObjs := {};
      lockedObjs := {};
      objTimeStamps := map[];
    // impl-end
    }

    constructor initTimestamp(that: TMSystem, obj: MemoryObject)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.txQueues == that.txQueues
      ensures this.procStates == that.procStates
      ensures this.dirtyObjs == that.dirtyObjs
      ensures this.lockedObjs == that.lockedObjs
      ensures this.objTimeStamps.Keys == that.objTimeStamps.Keys + {obj} && this.objTimeStamps[obj] == 0 && forall o :: o in this.objTimeStamps && o != obj ==> this.objTimeStamps[o] == that.objTimeStamps[o]
      // post-conditions-end
    {
    // impl-start
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps[obj := 0];
    // impl-end
    }

    constructor updateState(that: TMSystem, pid: ProcessId, state: ProcessState)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.txQueues == that.txQueues
      ensures this.procStates.Keys == that.procStates.Keys + {pid} && this.procStates[pid] == state && forall p :: p in this.procStates && p != pid ==> this.procStates[p] == that.procStates[p]
      ensures this.dirtyObjs == that.dirtyObjs
      ensures this.lockedObjs == that.lockedObjs
      ensures this.objTimeStamps == that.objTimeStamps
      // post-conditions-end
    {
    // impl-start
      txQueues := that.txQueues;
      procStates := that.procStates[pid := state];
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps;
    // impl-end
    }

    constructor markDirty(that: TMSystem, obj: MemoryObject)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.txQueues == that.txQueues
      ensures this.procStates == that.procStates
      ensures this.dirtyObjs == that.dirtyObjs + {obj}
      ensures this.lockedObjs == that.lockedObjs
      ensures this.objTimeStamps == that.objTimeStamps
      // post-conditions-end
    {
    // impl-start
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs + {obj};
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps;
    // impl-end
    }

    constructor clearDirty(that: TMSystem, writeSet: set<MemoryObject>)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.txQueues == that.txQueues
      ensures this.procStates == that.procStates
      ensures this.dirtyObjs == that.dirtyObjs - writeSet
      ensures this.lockedObjs == that.lockedObjs
      ensures this.objTimeStamps == that.objTimeStamps
      // post-conditions-end
    {
    // impl-start
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs - writeSet;
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps;
    // impl-end
    }

    constructor acquireLock(that: TMSystem, o: MemoryObject)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.txQueues == that.txQueues
      ensures this.procStates == that.procStates
      ensures this.dirtyObjs == that.dirtyObjs
      ensures this.lockedObjs == that.lockedObjs + {o}
      ensures this.objTimeStamps == that.objTimeStamps
      // post-conditions-end
    {
    // impl-start
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs + {o};
      objTimeStamps := that.objTimeStamps;
    // impl-end
    }

    constructor releaseLocks(that: TMSystem, objs: set<MemoryObject>)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.txQueues == that.txQueues
      ensures this.procStates == that.procStates
      ensures this.dirtyObjs == that.dirtyObjs
      ensures this.lockedObjs == that.lockedObjs - objs
      ensures this.objTimeStamps == that.objTimeStamps
      // post-conditions-end
    {
    // impl-start
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs - objs;
      objTimeStamps := that.objTimeStamps;
    // impl-end
    }

    constructor updateTimestamps(that: TMSystem, objs: set<MemoryObject>)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures this.txQueues == that.txQueues
      ensures this.procStates == that.procStates
      ensures this.dirtyObjs == that.dirtyObjs
      ensures this.lockedObjs == that.lockedObjs
      ensures this.objTimeStamps.Keys == that.objTimeStamps.Keys && forall o :: o in that.objTimeStamps ==> if o in objs then objTimeStamps[o] != that.objTimeStamps[o] else objTimeStamps[o] == that.objTimeStamps[o]
      // post-conditions-end
    {
    // impl-start
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs;
      objTimeStamps := map o | o in that.objTimeStamps :: if o in objs then that.objTimeStamps[o] + 1 else that.objTimeStamps[o];
    // impl-end
    }

    predicate stateValid(pid: ProcessId, state: ProcessState)
      requires pid in this.procStates && state == this.procStates[pid]
    {
      pid in txQueues &&
      state.currentTx <= |txQueues[pid]| &&
      if state.currentTx == |txQueues[pid]| then state.currentOp == 0 && state.currentSubOp == 0 && |state.readSet| == 0 && |state.writeSet| == 0 else if state.currentTx < |txQueues[pid]| then true && exists tx :: tx == txQueues[pid][state.currentTx] && state.currentOp <= |tx.ops| && state.currentOp >= -1 && (if state.currentOp >= 0 && state.currentOp < |tx.ops| then state.currentSubOp < 2 else if state.currentOp == |tx.ops| then state.currentSubOp < 4 else if state.currentOp == -1 then state.currentSubOp < 3 else false) && state.readSet.Keys <= objTimeStamps.Keys && state.writeSet <= lockedObjs else false
    }
    // pure-end

    predicate validSystem()
    {
      procStates.Keys <= txQueues.Keys &&
      dirtyObjs <= objTimeStamps.Keys &&
      lockedObjs <= objTimeStamps.Keys &&
      forall p, s :: 
        p in procStates &&
        s == procStates[p] ==>
          stateValid(p, s)
    }
    // pure-end
  }
}
