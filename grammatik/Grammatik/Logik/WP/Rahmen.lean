import Grammatik.Logik.WP.Kern
import Grammatik.Logik.Vertraege.RahmenTreu

/-!
# GabbroV over machine G: the frame rule

What a block does not write stays as it was. `RahmenTreu.lean` proves it for every statement, block and end block
over machine G (`block_treu`, `end_treu`): every outcome world differs from the start world at most at the carriers
the contract's write rights name, and holds the same locks. Here it becomes a rule of the calculus: it can be added
to ANY postcondition for free (`wpB_rahmen`, `wpE_rahmen`). The call meaning of a program keeps its frame
(`rufAt_treu`), so the rule applies to the program's real runs.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Rahmen

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : TreuR R) (hO : TreuO O)
include hR hO
variable {l : Bool} {Γ : Ctx}

/-- **The frame of a block**: every outcome world is within the contract's write rights, with the same locks. -/
theorem wpB_rahmen_allein {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    wpB O passes R b (TreuAusgang V.schreibt V.gschreibt σ) σ ρ :=
  block_treu O passes R hR hO b σ ρ

/-- **The frame rule**: the frame may be added to any postcondition. -/
theorem wpB_rahmen {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) (h : wpB O passes R b Q σ ρ) :
    wpB O passes R b (fun o => Q o ∧ TreuAusgang V.schreibt V.gschreibt σ o) σ ρ :=
  ⟨h, wpB_rahmen_allein O passes R hR hO b σ ρ⟩

/-- **The frame rule for a body.** -/
theorem wpE_rahmen {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (Q : EndAusgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) (h : wpE O passes R e Q σ ρ) :
    wpE O passes R e (fun o => Q o ∧ TreuEnd V.schreibt V.gschreibt σ o) σ ρ :=
  ⟨h, end_treu O passes R hR hO e σ ρ⟩

/-- A slot of a table the contract may not write is the same after a normal end. -/
theorem rahmen_slot {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hrun : execBlock O passes R b σ ρ = .ok σ' ρ') (t : D.Tab) (ht : V.schreibt t = false) (k : Int)
    (f : D.Feld t) : σ'.slots t k f = σ.slots t k f :=
  ((wpB_rahmen_allein O passes R hR hO b σ ρ) σ' (by rw [hrun]; rfl)).1.1 t ht k f

end Rahmen

end Gabbro.Grammatik.WP
