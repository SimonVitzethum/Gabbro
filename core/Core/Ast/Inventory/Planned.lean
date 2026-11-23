module

public import Core.Ast.Inventory.Entry

@[expose] public section

namespace Gabbro.Core.Inventory

/-- Source cases for the remaining forms named by the compiler plan. -/
def planned : List SurfaceForm :=
  [⟨"planned.substring", "Take a checked UTF-8 substring with the source capacity as its bound",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§0 and §8.1 O6"⟩, .m6⟩,
    ⟨"planned.boundedWhile", "A condition and body with a static operation bound and named overrun block",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§0 and §8.1 O18"⟩, .m6⟩,
    ⟨"planned.boundedFor", "Iteration over a half-open range as sugar for the bounded loop",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§8.1 O18"⟩, .m6⟩,
    ⟨"planned.effectGroup.declaration", "Declare a module-scoped name for a list of effect places",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§0 and §8 O19"⟩, .m6⟩,
    ⟨"planned.effectGroup.use", "Use a potentially qualified effect group in an effect clause",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§0 and §8 O19"⟩, .m6⟩,
    ⟨"planned.tuple.type", "A positional product of types",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§0 and §8.1 Tuples"⟩, .m6⟩,
    ⟨"planned.tuple.value", "Construct or project a positional product",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§0 and §8.1 Tuples"⟩, .m6⟩,
    ⟨"planned.tuple.binding", "Destructure a positional product in a local binding",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "§0 and §8.1 Tuples"⟩, .m6⟩,
    ⟨"planned.aggregate.value", "Use a record, array, string or payload-bearing tagged value by value in assignments and slots",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "P1"⟩, .m6⟩,
    ⟨"planned.aggregate.argument", "Pass an aggregate value, including the admitted immutable by-reference implementation",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "P1"⟩, .m6⟩,
    ⟨"planned.aggregate.result", "Return an aggregate value, including admitted in-place construction in the caller's result area",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "P1 and §8.1 O20"⟩, .m6⟩,
    ⟨"planned.persistence.table", "Declare a persistent table",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B22"⟩, .m9⟩,
    ⟨"planned.persistence.static", "Declare a persistent static place",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B22"⟩, .m9⟩,
    ⟨"planned.persistence.flush", "Flush a persistent place under the selected persistence envelope",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B22"⟩, .m9⟩,
    ⟨"planned.persistence.fence", "Order durability steps under the selected persistence envelope",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B22"⟩, .m9⟩,
    ⟨"planned.persistence.invariant", "State a crash invariant over ghost durable state",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B22"⟩, .m9⟩,
    ⟨"planned.persistence.cut", "State a persistent-state predicate for interruption at a named point",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B22"⟩, .m9⟩,
    ⟨"planned.persistence.envelope", "Select a pinned persistence envelope for the durable medium",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B22"⟩, .m9⟩,
    ⟨"planned.probability.event", "Bound the probability of a run event",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B11(c)"⟩, .m9p⟩,
    ⟨"planned.probability.cost", "Bound expected cost",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B11(c)"⟩, .m9p⟩,
    ⟨"planned.probability.termination", "State almost-sure termination of a randomized loop",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B11(c)"⟩, .m9p⟩,
    ⟨"planned.probability.progress", "State almost-sure progress of a randomized operation",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B11(c)"⟩, .m9p⟩,
    ⟨"planned.probability.informationTheoretic", "Bound advantage for every adversary with a given query budget",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B11(c)"⟩, .m9p⟩,
    ⟨"planned.probability.reduction", "Bound advantage by reduction to a primitive with named hardness",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B11(c)"⟩, .m9p⟩,
    ⟨"planned.probability.draw", "Call a random binding whose draw law comes from a named catalogue row",
      ⟨"dokumente/PLAN-COMPILER-READY.md", "B11(d)"⟩, .m9p⟩]

end Gabbro.Core.Inventory
