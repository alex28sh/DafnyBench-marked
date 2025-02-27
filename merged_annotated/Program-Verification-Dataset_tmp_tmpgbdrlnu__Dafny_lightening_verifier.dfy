// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_lightening_verifier.dfy

predicate ghost_state_inv(s: GhostState)
{
  0 <= s.num_entry * 2 < |s.log| &&
  |s.log| > 0 &&
  |s.mem| == s.mem_len &&
  |s.ideal_mem| == s.mem_len &&
  |s.old_mem| == s.mem_len &&
  s.countdown >= 0
}
// pure-end

function init_ghost_state(log: seq<int>, mem: seq<int>, countdown: int): GhostState
  requires |log| > 0
  requires countdown >= 0
  ensures ghost_state_inv(init_ghost_state(log, mem, countdown))
{
  GS(0, log[..], |mem|, mem[..], mem[..], mem[..], countdown, map[])
}
// pure-end

function mem_write(s: GhostState, off: int, val: int): GhostState
  requires ghost_state_inv(s)
  requires 0 <= off < s.mem_len
  ensures ghost_state_inv(mem_write(s, off, val))
{
  var new_mem := s.mem[off := val];
  var new_ideal_mem := s.ideal_mem[off := val];
  s.(mem := new_mem, ideal_mem := new_ideal_mem)
}
// pure-end

function log_write(s: GhostState, off: int, val: int): GhostState
  requires ghost_state_inv(s)
  requires 0 <= off < |s.log|
  ensures ghost_state_inv(log_write(s, off, val))
{
  s.(log := s.log[off := val])
}
// pure-end

predicate valid_op(s: GhostState, op: GhostOp)
{
  match op
  case WriteMem(off, val) =>
    0 <= off < |s.mem|
  case WriteLog(off, val) =>
    0 <= off < |s.log|
}
// pure-end

function countdown(s: GhostState): GhostState
{
  if s.countdown > 0 then
    s.(countdown := s.countdown - 1)
  else
    s
}
// pure-end

function normal_step(s: GhostState, op: GhostOp): GhostState
  requires valid_op(s, op)
  requires ghost_state_inv(s)
  ensures ghost_state_inv(normal_step(s, op))
{
  match op
  case WriteMem(off, val) =>
    mem_write(s, off, val)
  case WriteLog(off, val) =>
    log_write(s, off, val)
}
// pure-end

function ghost_step(s: GhostState, op: GhostOp): (GhostState, bool)
  requires valid_op(s, op)
  requires ghost_state_inv(s)
  ensures ghost_state_inv(normal_step(s, op))
{
  if s.countdown > 0 then
    var s' := normal_step(s, op);
    (s'.(countdown := s.countdown - 1), true)
  else
    (s, false)
}
// pure-end

function mem_write_step(s: GhostState, off: int, val: int): (GhostState, bool)
  requires 0 <= off < s.mem_len
  requires ghost_state_inv(s)
{
  ghost_step(s, WriteMem(off, val))
}
// pure-end

function log_write_step(s: GhostState, off: int, val: int): (GhostState, bool)
  requires 0 <= off < |s.log|
  requires ghost_state_inv(s)
{
  ghost_step(s, WriteLog(off, val))
}
// pure-end

function set_num_entry(s: GhostState, n: int): (GhostState, bool)
  requires 0 <= n * 2 < |s.log|
{
  if s.countdown > 0 then
    (s.(num_entry := n, countdown := s.countdown - 1), true)
  else
    (s, false)
}
// pure-end

predicate crashed(s: GhostState)
{
  s.countdown <= 0
}
// pure-end

predicate old_mem_equiv(s: GhostState)
  requires ghost_state_inv(s)
{
  forall o :: 
    !(o in s.first_log_pos) &&
    0 <= o < |s.mem| ==>
      s.mem[o] == s.old_mem[o]
}
// pure-end

predicate ghost_tx_inv(s: GhostState)
{
  ghost_state_inv(s) &&
  (forall o :: 
    o in s.first_log_pos ==>
      0 <= o < s.mem_len) &&
  (forall o :: 
    o in s.first_log_pos ==>
      0 <= s.first_log_pos[o] < s.num_entry) &&
  (forall o :: 
    o in s.first_log_pos ==>
      0 <= s.first_log_pos[o] * 2 + 1 < |s.log|) &&
  (forall o :: 
    o in s.first_log_pos ==>
      s.log[s.first_log_pos[o] * 2] == o) &&
  (forall o :: 
    o in s.first_log_pos ==>
      s.log[s.first_log_pos[o] * 2 + 1] == s.old_mem[o]) &&
  (forall o :: 
    o in s.first_log_pos ==>
      forall i :: 
        0 <= i < s.first_log_pos[o] ==>
          s.log[i * 2] != o) &&
  forall i :: 
    0 <= i < s.num_entry ==>
      s.log[i * 2] in s.first_log_pos
}
// pure-end

function ghost_begin_tx(s: GhostState): GhostState
  requires ghost_state_inv(s)
  requires s.num_entry == 0
  ensures ghost_state_inv(ghost_begin_tx(s))
  ensures ghost_tx_inv(ghost_begin_tx(s))
  ensures old_mem_equiv(ghost_begin_tx(s))
{
  var (s', f) := set_num_entry(s, 0);
  var s' := s'.(first_log_pos := map[], old_mem := s.mem[..]);
  s'
}
// pure-end

function ghost_commit_tx(s: GhostState): (GhostState, bool)
  requires ghost_tx_inv(s)
  requires old_mem_equiv(s)
  ensures ghost_state_inv(ghost_commit_tx(s).0)
  ensures ghost_tx_inv(ghost_commit_tx(s).0)
  ensures !ghost_commit_tx(s).1 ==> old_mem_equiv(ghost_commit_tx(s).0)
  ensures ghost_commit_tx(s).1 ==> ghost_commit_tx(s).0.num_entry == 0
{
  var s' := s;
  var (s', f) := set_num_entry(s', 0);
  var s' := if f then s'.(first_log_pos := map[]) else s';
  (s', f)
}
// pure-end

function ghost_tx_write(s0: GhostState, off: int, val: int): GhostState
  requires ghost_tx_inv(s0)
  requires old_mem_equiv(s0)
  requires 0 <= off < s0.mem_len
  requires 0 <= s0.num_entry * 2 + 2 < |s0.log|
  ensures ghost_tx_inv(ghost_tx_write(s0, off, val))
  ensures old_mem_equiv(ghost_tx_write(s0, off, val))
  ensures |ghost_tx_write(s0, off, val).mem| == s0.mem_len
  ensures !crashed(ghost_tx_write(s0, off, val)) ==> ghost_tx_write(s0, off, val).mem[off] == val
{
  var s := s0;
  var log_idx := s.num_entry;
  var log_off := log_idx * 2;
  var old_val := s.mem[off];
  var (s, f) := log_write_step(s, log_off, off);
  var (s, f) := log_write_step(s, log_off + 1, old_val);
  var (s, f) := set_num_entry(s, log_idx + 1);
  var s := if f && !(off in s.first_log_pos) then s.(first_log_pos := s.first_log_pos[off := log_idx]) else s;
  var (s, f) := mem_write_step(s, off, val);
  s
}
// pure-end

function reverse_recovery(s0: GhostState, idx: int): GhostState
  requires ghost_tx_inv(s0)
  requires old_mem_equiv(s0)
  requires 0 <= idx <= s0.num_entry
  ensures ghost_tx_inv(reverse_recovery(s0, idx))
  ensures old_mem_equiv(reverse_recovery(s0, idx))
  ensures s0.old_mem == reverse_recovery(s0, idx).old_mem
  ensures s0.first_log_pos == reverse_recovery(s0, idx).first_log_pos
  ensures forall o :: o in s0.first_log_pos && s0.first_log_pos[o] >= idx ==> reverse_recovery(s0, idx).mem[o] == s0.mem[o]
  ensures forall o :: o in s0.first_log_pos && 0 <= s0.first_log_pos[o] < idx ==> reverse_recovery(s0, idx).mem[o] == s0.old_mem[o]
  decreases idx
{
  if idx == 0 then
    assert old_mem_equiv(s0);
    s0
  else
    var s := s0; var i := idx - 1; var off := s.log[i * 2]; var val := s.log[i * 2 + 1]; var s := s.(mem := s.mem[off := val]); assert off in s.first_log_pos; var s := reverse_recovery(s, idx - 1); assert i == idx - 1; assert forall o :: o in s.first_log_pos && 0 <= s.first_log_pos[o] < i ==> s.mem[o] == s.old_mem[o]; assert forall o :: o in s.first_log_pos && s.first_log_pos[o] == i ==> o == off && val == s.old_mem[o]; assert forall o :: o in s.first_log_pos && s.first_log_pos[o] == i ==> s.mem[o] == val; assert old_mem_equiv(s); s
}
// pure-end

function ghost_recover(s0: GhostState): GhostState
  requires ghost_tx_inv(s0)
  requires old_mem_equiv(s0)
  ensures ghost_recover(s0).mem == s0.old_mem
  ensures ghost_recover(s0).num_entry == 0
{
  var s := reverse_recovery(s0, s0.num_entry);
  assert old_mem_equiv(s);
  assert forall o :: o in s.first_log_pos ==> s.mem[o] == s0.old_mem[o];
  assert forall i :: 0 <= i < |s.mem| ==> s.mem[i] == s0.old_mem[i];
  s.(num_entry := 0)
}
// pure-end

lemma crash_safe_single_tx(init_log: seq<int>, init_mem: seq<int>, countdown: int, writes: seq<(int, int)>)
  // pre-conditions-start
  requires |init_log| > 0
  requires countdown >= 0
  requires forall i :: 0 <= i < |writes| ==> 0 <= writes[i].0 < |init_mem|
  requires 0 < |writes| * 2 < |init_log|
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var s := init_ghost_state(init_log, init_mem, countdown);
  var end_mem := init_mem;
  s := ghost_begin_tx(s);
  assert s.num_entry == 0;
  assert init_mem == s.old_mem;
  var i := 0;
  while i < |writes|
    invariant 0 <= i <= |writes|
    invariant s.mem_len == |init_mem|
    invariant s.mem_len == |end_mem|
    invariant 0 <= s.num_entry <= i
    invariant |init_log| == |s.log|
    invariant i * 2 < |s.log|
    invariant 0 <= s.num_entry * 2 < |s.log|
    invariant ghost_tx_inv(s)
    invariant old_mem_equiv(s)
    invariant init_mem == s.old_mem
    invariant !crashed(s) ==> forall i :: 0 <= i < |s.mem| ==> s.mem[i] == end_mem[i]
    decreases |writes| - i
  {
    assert 0 <= i < |writes|;
    assert 0 <= writes[i].0 < s.mem_len;
    assert 0 <= s.num_entry * 2 + 2 < |s.log|;
    s := ghost_tx_write(s, writes[i].0, writes[i].1);
    end_mem := end_mem[writes[i].0 := writes[i].1];
    assert !crashed(s) ==> s.mem[writes[i].0] == writes[i].1;
    i := i + 1;
  }
  assert ghost_tx_inv(s);
  assert old_mem_equiv(s);
  var (s', c) := ghost_commit_tx(s);
  assert c ==> !crashed(s);
  if c {
    assert !crashed(s);
    assert s.mem == end_mem;
  } else {
    var recovered := ghost_recover(s');
    assert recovered.mem == init_mem;
  }
// impl-end
}

class CrashableMem<T> {
  var mem_: array<T>

  method read(off: int) returns (r: T)
    // pre-conditions-start
    requires 0 <= off < this.mem_.Length
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    return this.mem_[off];
  // impl-end
  }

  method write(off: int, val: T)
    // pre-conditions-start
    requires 0 <= off < this.mem_.Length
    // pre-conditions-end
    // post-conditions-start
    modifies this.mem_
    // post-conditions-end
  {
  // impl-start
    this.mem_[off] := val;
  // impl-end
  }
}

datatype GhostState = GS(num_entry: int, log: seq<int>, mem_len: int, mem: seq<int>, old_mem: seq<int>, ideal_mem: seq<int>, countdown: int, first_log_pos: map<int, int>)

datatype GhostOp = WriteMem(off: int, val: int) | WriteLog(off: int, val: int)

class UndoLog {
  var log_: array<int>
  var mem_: array<int>
  var impl_countdown: int
  ghost var gs: GhostState

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  predicate ghost_state_equiv(gs: GhostState)
    reads this, this.mem_, this.log_
  {
    this.log_.Length > 0 &&
    this.mem_[..] == gs.mem &&
    this.log_[1..] == gs.log &&
    this.log_[0] == gs.num_entry &&
    this.impl_countdown == gs.countdown
  }
  // pure-end

  predicate state_inv()
    reads this, this.log_
  {
    this.log_.Length > 1 &&
    0 <= this.log_[0] &&
    this.log_[0] * 2 < this.log_.Length &&
    this.log_.Length < 4294967295 &&
    this.mem_ != this.log_ &&
    forall i: int :: 
      0 <= i < this.log_[0] ==>
        0 <= this.log_[i * 2 + 1] < this.mem_.Length &&
        this.impl_countdown >= 0
  }
  // pure-end

  method init(log_size: int, mem_size: int, countdown: int)
    // pre-conditions-start
    requires log_size > 1
    requires mem_size > 0
    requires log_size < 4294967295
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures fresh(this.log_)
    ensures fresh(this.mem_)
    ensures this.state_inv()
    ensures this.ghost_state_equiv(this.gs)
    // post-conditions-end
  {
  // impl-start
    this.log_ := new int[log_size];
    this.mem_ := new int[mem_size];
    this.log_[0] := 0;
    this.impl_countdown := countdown;
    this.gs := GS(0, this.log_[1..], mem_size, this.mem_[..], this.mem_[..], this.mem_[..], countdown, map[]);
  // impl-end
  }

  method impl_countdown_dec()
    // pre-conditions-start
    requires this.impl_countdown > 0
    requires this.mem_ != this.log_
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.mem_ != this.log_
    ensures this.impl_countdown == old(this.impl_countdown) - 1
    ensures this.impl_countdown >= 0
    ensures this.gs == old(this.gs)
    ensures this.log_[..] == old(this.log_)[..]
    ensures this.mem_[..] == old(this.mem_)[..]
    // post-conditions-end
  {
  // impl-start
    this.impl_countdown := this.impl_countdown - 1;
  // impl-end
  }

  method write_mem(off: int, val: int)
    // pre-conditions-start
    requires 0 <= off < this.mem_.Length
    requires this.mem_ != this.log_
    requires ghost_state_inv(this.gs)
    requires this.ghost_state_equiv(this.gs)
    requires 0 <= off < this.gs.mem_len
    // pre-conditions-end
    // post-conditions-start
    modifies this, this.mem_
    ensures this.mem_ == old(this.mem_)
    ensures this.log_ == old(this.log_)
    ensures this.gs == old(this.gs)
    ensures this.ghost_state_equiv(mem_write_step(this.gs, off, val).0)
    // post-conditions-end
  {
  // impl-start
    if this.impl_countdown > 0 {
      this.mem_[off] := val;
      this.impl_countdown := this.impl_countdown - 1;
    }
  // impl-end
  }

  method write_log(off: int, val: int)
    // pre-conditions-start
    requires 0 <= off <= |this.gs.log|
    requires this.mem_ != this.log_
    requires ghost_state_inv(this.gs)
    requires this.ghost_state_equiv(this.gs)
    requires off == 0 ==> 0 <= val * 2 < |this.gs.log|
    // pre-conditions-end
    // post-conditions-start
    modifies this, this.log_
    ensures this.mem_ != this.log_
    ensures this.mem_ == old(this.mem_)
    ensures this.log_ == old(this.log_)
    ensures this.log_.Length == old(this.log_).Length
    ensures this.mem_[..] == old(this.mem_)[..]
    ensures this.log_[off] == val || this.log_[off] == old(this.log_)[off]
    ensures forall i :: 0 <= i < this.log_.Length && i != off ==> this.log_[i] == old(this.log_)[i]
    ensures this.gs == old(this.gs)
    ensures off > 0 ==> this.ghost_state_equiv(log_write_step(this.gs, off - 1, val).0)
    ensures off == 0 ==> this.ghost_state_equiv(set_num_entry(this.gs, val).0)
    // post-conditions-end
  {
  // impl-start
    if this.impl_countdown > 0 {
      this.log_[off] := val;
      this.impl_countdown := this.impl_countdown - 1;
    }
  // impl-end
  }

  method begin_tx()
    // pre-conditions-start
    requires this.state_inv()
    requires this.ghost_state_equiv(this.gs)
    requires ghost_state_inv(this.gs)
    requires this.log_[0] == 0
    // pre-conditions-end
    // post-conditions-start
    modifies this.log_, this
    ensures this.mem_ == old(this.mem_)
    ensures this.log_ == old(this.log_)
    ensures this.state_inv()
    ensures this.ghost_state_equiv(this.gs)
    ensures ghost_tx_inv(this.gs)
    // post-conditions-end
  {
  // impl-start
    this.write_log(0, 0);
    this.gs := ghost_begin_tx(this.gs);
    // assert-start
    assert this.state_inv();
    // assert-end

  // impl-end
  }

  method commit_tx()
    // pre-conditions-start
    requires this.state_inv()
    requires this.ghost_state_equiv(this.gs)
    requires ghost_state_inv(this.gs)
    requires ghost_tx_inv(this.gs)
    requires old_mem_equiv(this.gs)
    // pre-conditions-end
    // post-conditions-start
    modifies this.log_, this
    ensures this.mem_ == old(this.mem_)
    ensures this.log_ == old(this.log_)
    ensures this.ghost_state_equiv(this.gs)
    ensures this.state_inv()
    // post-conditions-end
  {
  // impl-start
    this.write_log(0, 0);
    this.gs := ghost_commit_tx(this.gs).0;
  // impl-end
  }

  method tx_write(offset: int, val: int)
    // pre-conditions-start
    requires this.state_inv()
    requires this.mem_ != this.log_
    requires 0 <= offset < this.mem_.Length
    requires this.ghost_state_equiv(this.gs)
    requires ghost_tx_inv(this.gs)
    requires old_mem_equiv(this.gs)
    requires 0 <= this.log_[0] * 2 + 3 < this.log_.Length
    // pre-conditions-end
    // post-conditions-start
    modifies this, this.log_, this.mem_
    ensures this.ghost_state_equiv(this.gs)
    ensures ghost_tx_inv(this.gs)
    ensures old_mem_equiv(this.gs)
    // post-conditions-end
  {
  // impl-start
    var log_idx := this.log_[0];
    var log_off := log_idx * 2;
    ghost var old_gs := this.gs;
    this.write_log(log_off + 1, offset);
    this.gs := log_write_step(this.gs, log_off, offset).0;
    // assert-start
    assert log_off + 1 > 0;
    // assert-end

    // assert-start
    assert this.ghost_state_equiv(this.gs);
    // assert-end

    // assert-start
    assert this.mem_ != this.log_;
    // assert-end

    var old_val := this.mem_[offset];
    // assert-start
    assert old_val == this.gs.mem[offset];
    // assert-end

    this.write_log(log_off + 2, old_val);
    this.gs := log_write_step(this.gs, log_off + 1, old_val).0;
    // assert-start
    assert ghost_tx_inv(this.gs);
    // assert-end

    // assert-start
    assert this.log_[0] == this.gs.num_entry;
    // assert-end

    // assert-start
    assert this.log_.Length == |this.gs.log| + 1;
    // assert-end

    // assert-start
    assert 0 <= this.gs.num_entry * 2 < |this.gs.log|;
    // assert-end

    this.write_log(0, log_idx + 1);
    ghost var (s, f) := set_num_entry(this.gs, log_idx + 1);
    s := if f && !(offset in s.first_log_pos) then s.(first_log_pos := s.first_log_pos[offset := log_idx]) else s;
    this.gs := s;
    this.write_mem(offset, val);
    this.gs := mem_write_step(this.gs, offset, val).0;
    // assert-start
    assert this.gs == ghost_tx_write(old_gs, offset, val);
    // assert-end

  // impl-end
  }

  method recover()
    // pre-conditions-start
    requires this.state_inv()
    requires ghost_tx_inv(this.gs)
    requires old_mem_equiv(this.gs)
    requires this.ghost_state_equiv(this.gs)
    // pre-conditions-end
    // post-conditions-start
    modifies this.log_, this.mem_, this
    ensures this.gs == ghost_recover(old(this.gs))
    ensures this.ghost_state_equiv(this.gs)
    // post-conditions-end
  {
  // impl-start
    var log_len := this.log_[0];
    // assert-start
    assert log_len == this.gs.num_entry;
    // assert-end

    if log_len > 0 {
      var i := log_len - 1;
      ghost var gs0 := this.gs;
      while i >= 0
        // invariants-start

        invariant this.log_ == old(this.log_)
        invariant this.mem_ == old(this.mem_)
        invariant unchanged(this.log_)
        invariant -1 <= i < log_len
        invariant |this.gs.log| == |gs0.log|
        invariant this.ghost_state_equiv(this.gs)
        invariant ghost_tx_inv(this.gs)
        invariant old_mem_equiv(this.gs)
        invariant reverse_recovery(gs0, log_len) == reverse_recovery(this.gs, i + 1)
        decreases i
        modifies this.mem_, this
        // invariants-end

      {
        // assert-start
        assert this.ghost_state_equiv(this.gs);
        // assert-end

        // assert-start
        assert 0 <= i < this.log_[0];
        // assert-end

        var o := i * 2 + 1;
        var off := this.log_[o];
        var val := this.log_[o + 1];
        this.mem_[off] := val;
        // assert-start
        assert 0 <= off < this.mem_.Length;
        // assert-end

        // assert-start
        assert this.gs.log[i * 2] == off;
        // assert-end

        // assert-start
        assert this.gs.log[i * 2 + 1] == val;
        // assert-end

        this.gs := this.gs.(mem := this.gs.mem[off := val]);
        i := i - 1;
      }
      // assert-start
      assert this.ghost_state_equiv(this.gs);
      // assert-end

    } else {
      // assert-start
      assert this.ghost_state_equiv(this.gs);
      // assert-end

    }
    this.log_[0] := 0;
    this.gs := ghost_recover(old(this.gs));
    // assert-start
    assert this.ghost_state_equiv(this.gs);
    // assert-end

  // impl-end
  }
}
