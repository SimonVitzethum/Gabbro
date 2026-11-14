module
public import Stage0.Senke.Anweisung.Fast.Expression
public import Stage0.Senke.Anweisung.Faelle.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Argument evaluation retains the canonical reverse order and ABI offsets. -/
def lowAFast (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (frame : FrameCache Γ) :
    {τs : List Ty} → Args D Γ Λ τs → Nat → Nat → Option (List II × Nat)
  | _, .nil, p, _ => some ([], p)
  | _ :: τs, .cons e rest, p, reserved => do
    let cr ← lowAFast L frame rest p reserved
    let ce ← lowEFast L e (p + contextWords τs) reserved true frame
    pure (cr.1 ++ ce.1, max cr.2 ce.2)

theorem lowAFast_eq (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (frame : FrameCache Γ)
    {τs : List Ty} (args : Args D Γ Λ τs) (p reserved : Nat) :
    lowAFast L frame args p reserved = lowA L args p reserved :=
  match args with
  | .nil => rfl
  | .cons e rest => by
    have ih := lowAFast_eq L frame rest p reserved
    unfold lowAFast lowA
    simp only [ih, lowEFast_eq]
termination_by structural args

def lowErgFast (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (frame : FrameCache Γ) :
    {e : Option Ty} → ErgExpr D Γ Λ e → Nat → Nat → Option (List II × Nat)
  | _, .empty, d, _ => some ([ci 1 d 0 0], d + 1)
  | some τ, .val e, d, reserved =>
    (lowEFast L e d reserved true frame).map
      fun (p : List II × Nat) => (p.1, max p.2 (d + valueWords τ))

theorem lowErgFast_eq (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} (frame : FrameCache Γ)
    {e : Option Ty} (value : ErgExpr D Γ Λ e) (d reserved : Nat) :
    lowErgFast L frame value d reserved = lowErg L value d reserved := by
  cases value with
  | empty => rfl
  | val e => simp only [lowErgFast, lowErg, lowEFast_eq]

end Gabbro.Stage0.Senke
