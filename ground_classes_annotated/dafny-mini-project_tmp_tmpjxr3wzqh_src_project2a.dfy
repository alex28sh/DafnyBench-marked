// dafny-mini-project_tmp_tmpjxr3wzqh_src_project2a.dfy

function rem<T(==)>(x: T, s: seq<T>): seq<T>
  ensures x !in rem(x, s)
  ensures forall i :: 0 <= i < |rem(x, s)| ==> rem(x, s)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] != x ==> s[i] in rem(x, s)
  decreases s
{
  if |s| == 0 then
    []
  else if s[0] == x then
    rem(x, s[1..])
  else
    [s[0]] + rem(x, s[1..])
}
// pure-end

class Address {
  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }
}

class Date {
  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }
}

class MessageId {
  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }
}

class Message {
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: seq<Address>

  constructor (s: Address)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures fresh(this.id)
    ensures fresh(this.date)
    ensures this.content == ""
    ensures this.sender == s
    ensures this.recipients == []
    // post-conditions-end
  {
  // impl-start
    this.id := new MessageId();
    this.date := new Date();
    this.content := "";
    this.sender := s;
    this.recipients := [];
  // impl-end
  }

  method setContent(c: string)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.content == c
    // post-conditions-end
  {
  // impl-start
    this.content := c;
  // impl-end
  }

  method setDate(d: Date)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.date == d
    // post-conditions-end
  {
  // impl-start
    this.date := d;
  // impl-end
  }

  method addRecipient(p: nat, r: Address)
    // pre-conditions-start
    requires p < |this.recipients|
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures |this.recipients| == |old(this.recipients)| + 1
    ensures this.recipients[p] == r
    ensures forall i :: 0 <= i < p ==> this.recipients[i] == old(this.recipients[i])
    ensures forall i :: p < i < |this.recipients| ==> this.recipients[i] == old(this.recipients[i - 1])
    // post-conditions-end
  {
  // impl-start
    this.recipients := this.recipients[..p] + [r] + this.recipients[p..];
  // impl-end
  }
}

class Mailbox {
  var messages: set<Message>
  var name: string

  constructor (n: string)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.name == n
    ensures this.messages == {}
    // post-conditions-end
  {
  // impl-start
    this.name := n;
    this.messages := {};
  // impl-end
  }

  method add(m: Message)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures m in this.messages
    ensures this.messages == old(this.messages) + {m}
    // post-conditions-end
  {
  // impl-start
    this.messages := {m} + this.messages;
  // impl-end
  }

  method remove(m: Message)
    // pre-conditions-start
    requires m in this.messages
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures m !in this.messages
    ensures this.messages == old(this.messages) - {m}
    // post-conditions-end
  {
  // impl-start
    this.messages := this.messages - {m};
  // impl-end
  }

  method empty()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.messages == {}
    // post-conditions-end
  {
  // impl-start
    this.messages := {};
  // impl-end
  }
}

class MailApp {
  ghost var userboxes: set<Mailbox>
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox
  var userboxList: seq<Mailbox>

  ghost predicate Valid()
    reads this
  {
    this.inbox != this.drafts &&
    this.inbox != this.trash &&
    this.inbox != this.sent &&
    this.drafts != this.trash &&
    this.drafts != this.sent &&
    this.inbox !in this.userboxList &&
    this.drafts !in this.userboxList &&
    this.trash !in this.userboxList &&
    this.sent !in this.userboxList &&
    forall i :: 
      0 <= i < |this.userboxList| ==>
        this.userboxList[i] in this.userboxes
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    this.inbox := new Mailbox("Inbox");
    this.drafts := new Mailbox("Drafts");
    this.trash := new Mailbox("Trash");
    this.sent := new Mailbox("Sent");
    this.userboxList := [];
  // impl-end
  }

  method deleteMailbox(mb: Mailbox)
    // pre-conditions-start
    requires this.Valid()
    requires mb in this.userboxList
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  method newMailbox(n: string)
    // pre-conditions-start
    requires this.Valid()
    requires !exists mb | mb in this.userboxList :: mb.name == n
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures exists mb | mb in this.userboxList :: mb.name == n
    // post-conditions-end
  {
  // impl-start
    var mb := new Mailbox(n);
    this.userboxList := [mb] + this.userboxList;
  // impl-end
  }

  method newMessage(s: Address)
    // pre-conditions-start
    requires this.Valid()
    // pre-conditions-end
    // post-conditions-start
    modifies this.drafts
    ensures exists m | m in this.drafts.messages :: m.sender == s
    // post-conditions-end
  {
  // impl-start
    var m := new Message(s);
    this.drafts.add(m);
  // impl-end
  }

  method moveMessage(m: Message, mb1: Mailbox, mb2: Mailbox)
    // pre-conditions-start
    requires this.Valid()
    requires m in mb1.messages
    requires m !in mb2.messages
    // pre-conditions-end
    // post-conditions-start
    modifies mb1, mb2
    ensures m !in mb1.messages
    ensures m in mb2.messages
    // post-conditions-end
  {
  // impl-start
    mb1.remove(m);
    mb2.add(m);
  // impl-end
  }

  method deleteMessage(m: Message, mb: Mailbox)
    // pre-conditions-start
    requires this.Valid()
    requires m in mb.messages
    requires m !in this.trash.messages
    // pre-conditions-end
    // post-conditions-start
    modifies m, mb, this.trash
    // post-conditions-end
  {
  // impl-start
    this.moveMessage(m, mb, this.trash);
  // impl-end
  }

  method sendMessage(m: Message)
    // pre-conditions-start
    requires this.Valid()
    requires m in this.drafts.messages
    requires m !in this.sent.messages
    // pre-conditions-end
    // post-conditions-start
    modifies this.drafts, this.sent
    // post-conditions-end
  {
  // impl-start
    this.moveMessage(m, this.drafts, this.sent);
  // impl-end
  }

  method emptyTrash()
    // pre-conditions-start
    requires this.Valid()
    // pre-conditions-end
    // post-conditions-start
    modifies this.trash
    ensures this.trash.messages == {}
    // post-conditions-end
  {
  // impl-start
    this.trash.empty();
  // impl-end
  }
}
