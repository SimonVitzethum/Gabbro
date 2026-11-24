module

@[expose] public section

namespace Gabbro.Core.Maschine

/-- Partial operations for which an unhandled use requires a generated guard. -/
inductive PartielleOperation where
  | division
  | modulo
  | index
  | shift
  | konvertierung
  | entpacken
  | ganzzahlBereich
  deriving DecidableEq, Repr

/-- The inputs required to check one use. Integer results use the full exact
    result and the contextual signed width, so a wrapped result cannot pass. -/
def Operanden : PartielleOperation → Type
  | .division => Nat × Nat
  | .modulo => Nat × Nat
  | .index => Nat × Nat
  | .shift => Nat × Nat
  | .konvertierung => Nat × Nat
  | .entpacken => Nat
  | .ganzzahlBereich => Int × Nat


/-- Written predicates, kept in source order as elaboration combines fragments. -/
structure Quellklauseln (S : Type) where
  voraus : List (S → Prop)
  sicher : List (S → Prop)
  invariant : List (S → Prop)

def Quellklauseln.leer : Quellklauseln S := ⟨[], [], []⟩

def Quellklauseln.anhaengen (a b : Quellklauseln S) : Quellklauseln S :=
  ⟨a.voraus ++ b.voraus, a.sicher ++ b.sicher, a.invariant ++ b.invariant⟩

/-- Data produced by elaboration. Guards are indexed by pre-state and have no
    dependency on the existence of a successor or on implementation execution. -/
structure Quelltabellen (S : Type) where
  klauseln : Quellklauseln S
  guard : S → (op : PartielleOperation) → Operanden op → Prop

def Quelltabellen.leer : Quelltabellen S := ⟨.leer, fun _ _ _ => False⟩

end Gabbro.Core.Maschine
