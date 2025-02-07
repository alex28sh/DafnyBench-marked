function Init(v: Variables): bool
{
  v.WellFormed() &&
  forall b :: 
    b in v.library ==>
      v.library[b].Shelf?
}
// pure-end

function CheckoutStep(v: Variables, v': Variables, step: Step): bool
  requires step.Checkout?
{
  v.WellFormed() &&
  step.b in v.library &&
  v.library[step.b].Shelf? &&
  v' == v.(library := v.library[step.b := Patron(step.to)])
}
// pure-end

function ReturnStep(v: Variables, v': Variables, step: Step): bool
  requires step.Return?
{
  v.WellFormed() &&
  step.b in v.library &&
  v.library[step.b].Patron? &&
  v' == v.(library := v.library[step.b := Shelf])
}
// pure-end

function NextStep(v: Variables, v': Variables, step: Step): bool
{
  match step {
    case Checkout(_ /* _v0 */, _ /* _v1 */) =>
      CheckoutStep(v, v', step)
    case Return(_ /* _v2 */) =>
      ReturnStep(v, v', step)
  }
}
// pure-end

function Next(v: Variables, v': Variables): bool
{
  exists step :: 
    NextStep(v, v', step)
}
// pure-end

lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, step: Step)
  // pre-conditions-start
  requires NextStep(v, v', step)
  // pre-conditions-end
  // post-conditions-start
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ExampleExec()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var e := [Variables(library := map[Book("Snow Crash") := Shelf, Book("The Stand") := Shelf]), Variables(library := map[Book("Snow Crash") := Patron("Jon"), Book("The Stand") := Shelf]), Variables(library := map[Book("Snow Crash") := Patron("Jon"), Book("The Stand") := Patron("Tej")]), Variables(library := map[Book("Snow Crash") := Shelf, Book("The Stand") := Patron("Tej")])];
  assert Init(e[0]);
  var steps := [Checkout(Book("Snow Crash"), "Jon"), Checkout(Book("The Stand"), "Tej"), Return(Book("Snow Crash"))];
  assert forall n: nat | n < |e| - 1 :: NextStep(e[n], e[n + 1], steps[n]);
  assert forall n: nat | n < |e| - 1 :: Next(e[n], e[n + 1]);
// impl-end
}

datatype Status = Shelf | Patron(name: string)

datatype Book = Book(title: string)

datatype Variables = Variables(library: map<Book, Status>) {
  function WellFormed(): bool
  {
    forall b: Book :: 
      b.title == "" ==>
        b !in this.library
  }
// pure-end
}

datatype Step = Checkout(b: Book, to: string) | Return(b: Book)
