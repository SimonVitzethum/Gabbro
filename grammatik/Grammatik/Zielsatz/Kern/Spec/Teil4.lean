/- C16: the goal leg for declared checks -- evidence and its consumption.

   `CheckTreueG` is the fidelity leg for `Ziel`/`ZielX`/`ZielFX`: every ghost
   evidence entry belongs to a declared check's probe; a live entry holds the
   Duty with no consumer, a consumed entry names exactly one declared gate of
   that check; and the same report of one probe never manufactures a second
   Duty -- equal verdict, equal samples and equal liveness go to the same
   consumer. The machine-indexed fold (reading the evidence off the ghost
   history at the reached machine, through the C08/C09 transport) is the
   lead's build step; this leg already fixes the statement that fold proves. -/
module

public import Grammatik.Zielsatz.Kern.Spec.Teil1
public import Grammatik.Kern.Syntax.Satz.Pruefung

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `CheckTreueG`: check evidence and its consumption. Duty records a completed
    measurement with its verdict, never proof of the prose claim. -/
def CheckTreueG (P : Programm D) (checks : List (CheckDecl D))
    (ev : List (CheckEvidenz D)) : Prop :=
  (∀ e ∈ ev, ∃ c ∈ checks, e.erzeuger = c.probe) ∧
  (∀ e ∈ ev, ∀ c ∈ checks, e.erzeuger = c.probe →
    (e.lebt = true ∧ e.tor = none) ∨
    (e.lebt = false ∧ ∃ g ∈ c.gates, e.tor = some g)) ∧
  (∀ c ∈ checks, ∀ e₁ ∈ ev, ∀ e₂ ∈ ev, e₁.erzeuger = c.probe → e₂.erzeuger = c.probe →
    e₁.berich.urteil = e₂.berich.urteil → e₁.berich.proben = e₂.berich.proben →
    e₁.lebt = e₂.lebt ∧ e₁.tor = e₂.tor)

/-- The empty history is faithful: the leg holds vacuously. -/
example : CheckTreueG (D := pruefD) pruefP [] [] := by decide

/-! ## Witnesses: one live and one consumed entry, jointly -/

/-- The verdicts of the fixture reports: one completed measurement with a
    positive verdict, one with a negative verdict. -/
def treueBerichtWahr : CheckReport := { proben := [], boeden := [], urteil := true }
def treueBerichtFalsch : CheckReport := { proben := [], boeden := [], urteil := false }

/-- One live and one consumed entry of the fixture probe. -/
def treueLebt : CheckEvidenz pruefD := { erzeuger := true, bericht := treueBerichtWahr, lebt := true, tor := none }
def treueVerbraucht : CheckEvidenz pruefD := { erzeuger := true, bericht := treueBerichtFalsch, lebt := false, tor := some false }

/-- Non-degenerate fidelity: a live and a consumed entry of the fixture probe,
    with different verdicts, satisfy the leg jointly -- the same report of one
    probe never manufactures a second Duty. -/
theorem checkTreue_zeuge : CheckTreueG (D := pruefD) pruefP [pruefC] [treueLebt, treueVerbraucht] := by decide

end Gabbro.Grammatik.Zielsatz
