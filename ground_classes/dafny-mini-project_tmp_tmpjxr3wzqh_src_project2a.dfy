/*
  ===============================================
  DCC831 Formal Methods
  2023.2

  Mini Project 2 - Part A

  Your name: Guilherme de Oliveira Silva
  ===============================================
*/


function rem<T(==)>(x: T, s: seq<T>): seq<T>
  decreases s
  ensures x !in rem(x, s)
  ensures forall i :: 0 <= i < |rem(x, s)| ==> rem(x, s)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] != x ==> s[i] in rem(x, s)
{
  if |s| == 0 then []
  else if s[0] == x then rem(x, s[1..])
  else [s[0]] + rem(x, s[1..])
}


// The next three classes have a minimal class definition,
// for simplicity
class Address
{
  constructor () {}
}

class Date
{
  constructor () {}
}

class MessageId
{
  constructor () {}
}

//==========================================================
//  Message
//==========================================================
class Message
{
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: seq<Address>

  constructor (s: Address)
    ensures fresh(this.id)
    ensures fresh(this.date)
    ensures this.content == ""
    ensures this.sender == s
    ensures this.recipients == []
  {
    this.id := new MessageId();
    this.date := new Date();
    this.content := "";
    this.sender := s;
    this.recipients := [];
  }

  method setContent(c: string)
    modifies this
    ensures this.content == c
  {
    this.content := c;
  }

  method setDate(d: Date)
    modifies this
    ensures this.date == d
  {
    this.date := d;
  }

  method addRecipient(p: nat, r: Address)
    modifies this
    requires p < |this.recipients|
    ensures |this.recipients| == |old(this.recipients)| + 1
    ensures this.recipients[p] == r
    ensures forall i :: 0 <= i < p ==> this.recipients[i] == old(this.recipients[i])
    ensures forall i :: p < i < |this.recipients| ==> this.recipients[i] == old(this.recipients[i-1])
  {
    this.recipients := this.recipients[..p] + [r] + this.recipients[p..];
  }
}

//==========================================================
//  Mailbox
//==========================================================
// Each Mailbox has a name, which is a string. Its main content is a set of messages.
class Mailbox {
  var messages: set<Message>
  var name: string

  // Creates an empty mailbox with name n
  constructor (n: string)
    ensures this.name == n
    ensures this.messages == {}
  {
    this.name := n;
    this.messages := {};
  }

  // Adds message m to the mailbox
  method add(m: Message)
    modifies this
    ensures m in this.messages
    ensures this.messages == old(this.messages) + {m}
  {
    this.messages := { m } + this.messages;
  }

  // Removes message m from mailbox. m must not be in the mailbox.
  method remove(m: Message)
    modifies this
    requires m in this.messages
    ensures m !in this.messages
    ensures this.messages == old(this.messages) - {m}
  {
    this.messages := this.messages - { m };
  }

  // Empties the mailbox messages
  method empty()
    modifies this
    ensures this.messages == {}
  {
    this.messages := {};
  }
}

//==========================================================
//  MailApp
//==========================================================
class MailApp {
  // abstract field for user defined boxes
  ghost var userboxes: set<Mailbox>

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox

  // userboxList implements userboxes
  var userboxList: seq<Mailbox>

  // Class invariant
  ghost predicate Valid()
    reads this
  {
    //----------------------------------------------------------
    // Abstract state invariants
    //----------------------------------------------------------
    // all predefined mailboxes (inbox, ..., sent) are distinct
    this.inbox != this.drafts &&
    this.inbox != this.trash &&
    this.inbox != this.sent &&
    this.drafts != this.trash &&
    this.drafts != this.sent &&

    // none of the predefined mailboxes are in the set of user-defined mailboxes
    this.inbox !in this.userboxList &&
    this.drafts !in this.userboxList &&
    this.trash !in this.userboxList &&
    this.sent !in this.userboxList &&

    //----------------------------------------------------------
    // Abstract-to-concrete state invariants
    //----------------------------------------------------------
    // userboxes is the set of mailboxes in userboxList
    forall i :: 0 <= i < |this.userboxList| ==> this.userboxList[i] in this.userboxes
  }

  constructor ()
  {
    this.inbox := new Mailbox("Inbox");
    this.drafts := new Mailbox("Drafts");
    this.trash := new Mailbox("Trash");
    this.sent := new Mailbox("Sent");
    this.userboxList := [];
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
    requires this.Valid()
    requires mb in this.userboxList
    // ensures mb !in userboxList
  {
    // this.userboxList := rem(mb, this.userboxList);
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
    modifies this
    requires this.Valid()
    requires !exists mb | mb in this.userboxList :: mb.name == n
    ensures exists mb | mb in this.userboxList :: mb.name == n
  {
    var mb := new Mailbox(n);
    this.userboxList := [mb] + this.userboxList;
  }

  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
    modifies this.drafts
    requires this.Valid()
    ensures exists m | m in this.drafts.messages :: m.sender == s
  {
    var m := new Message(s);
    this.drafts.add(m);
  }

  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage (m: Message, mb1: Mailbox, mb2: Mailbox)
    modifies mb1, mb2
    requires this.Valid()
    requires m in mb1.messages
    requires m !in mb2.messages
    ensures m !in mb1.messages
    ensures m in mb2.messages
  {
    mb1.remove(m);
    mb2.add(m);
  }

  // Moves message m from mailbox mb to the trash mailbox provided
  // that mb is not the trash mailbox
  method deleteMessage (m: Message, mb: Mailbox)
    modifies m, mb, this.trash
    requires this.Valid()
    requires m in mb.messages
    requires m !in this.trash.messages
  {
    this.moveMessage(m, mb, this.trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
    modifies this.drafts, this.sent
    requires this.Valid()
    requires m in this.drafts.messages
    requires m !in this.sent.messages
  {
    this.moveMessage(m, this.drafts, this.sent);
  }

  // Empties the trash mailbox
  method emptyTrash()
    modifies this.trash
    requires this.Valid()
    ensures this.trash.messages == {}
  {
    this.trash.empty();
  }
}
