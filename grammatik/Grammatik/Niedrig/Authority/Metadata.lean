module

public import Grammatik.Kern.Syntax.Typen.Sicht
public import Grammatik.Kern.Syntax.Marken.Owner.State
public import Grammatik.Niedrig.Arch.Zustand
public import Grammatik.Niedrig.Maske.Prio

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-- An authority declaration is satisfied at the chosen boot boundary. Its
    token is the existing nominal owner grant, never a copyable Ty value. -/
structure Authority (D : Deklaration) where
  names : OwnerNamespace D
  token : OwnerToken D
  spans : List (Span D)
  epoch : Nat


/-- Architectural state is abstract. No target or instruction is encoded here.
    One context grant is suspended/restored by the existing owner loan stack. -/
structure Context (D : Deklaration) (Privilege Interrupt : Type) where
  owners : OwnerState D
  frame : ArenaOwnership.Frame
  views : List (View D)
  privilege : Privilege
  interrupt : Interrupt


end Gabbro.Grammatik.LowLevel

namespace Gabbro.Grammatik.LowLevel.Construct

/-- The canonical target-neutral context stored by the call machine. -/
abbrev SystemContext (D : Deklaration) :=
  Context D Niedrig.Arch.ArchState Niedrig.Maske.PrioMaske

end Gabbro.Grammatik.LowLevel.Construct
