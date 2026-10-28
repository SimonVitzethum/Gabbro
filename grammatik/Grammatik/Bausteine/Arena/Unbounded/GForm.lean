import Grammatik.Bausteine.Arena.Unbounded.Execution
import Grammatik.Bausteine.Arena.Ownership.World
import Grammatik.Logik.Terminierung.Klasse

/-!
The fallible-allocation boundary in actual G terms. The provider result is an
ordinary Boolean expression, obtained by the program's own binding. A positive
answer does not remove the finite physical allocator's own full/failure branch.
These are finite realisations of individual requests, NOT an unbounded G heap
or an automatic extension of `gabbro_ziel` to the storage component.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- One request with mandatory failure continuation, including below a reservation
and on free-list reuse. There is no implicit retry or assumption of success. -/
def Block.allocationAttempt (available : Expr D Γ Λ .bool)
    (failure : Endblock D V l Γ Λ) (success : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .check available failure success

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- Provider refusal executes the user's failure continuation before any allocator
write; only the provider-result expression's declared reads have been recorded. -/
theorem allocationAttempt_refused (available : Expr D Γ Λ .bool)
    (failure : Endblock D V l Γ Λ) (success : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (he : eval (σ.lese Λ available.orte) available (σ.lese Λ available.orte) ρ = false) :
    execBlock O passes R (Block.allocationAttempt available failure success) σ ρ =
      (execEnd O passes R failure (σ.lese Λ available.orte) ρ).zuAusgang := by
  simp only [Block.allocationAttempt, execBlock, wahr?, he, Bool.false_eq_true, ↓reduceIte]

/-- Positive availability only selects the normal, fully checked G continuation. -/
theorem allocationAttempt_available (available : Expr D Γ Λ .bool)
    (failure : Endblock D V l Γ Λ) (success : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (he : eval (σ.lese Λ available.orte) available (σ.lese Λ available.orte) ρ = true) :
    execBlock O passes R (Block.allocationAttempt available failure success) σ ρ =
      execBlock O passes R success (σ.lese Λ available.orte) ρ := by
  simp only [Block.allocationAttempt, execBlock, wahr?, he, ↓reduceIte]

/-- Both source branches remain visible to the existing termination classifier. -/
theorem allocationAttempt_termination (available : Expr D Γ Λ .bool)
    (failure : Endblock D V l Γ Λ) (success : Block D V l Γ Λ Λ') (level forever : Bool) :
    befB level forever (Block.allocationAttempt available failure success) =
      befE level forever failure ++ befB level forever success := rfl

end Execution

namespace ArenaStorage

/-- The actual G world and the growing storage component share the EXISTING grant
ledger. This bridge imposes a finite extent only on the chosen realisation. -/
def Represented (H : Heap region α) (A : FreiForm D) (σ : World D) : Prop :=
  H.rights.agrees A σ ∧ (H.extent : Int) = A.stand σ ∧
    (H.extent : Int) ≤ D.count A.tab

theorem Represented.live {H : Heap region α} {A : FreiForm D} {σ : World D}
    (hr : Represented H A σ) {f : ArenaOwnership.Frame} {r : Ref region}
    (ha : H.rights.access f r.handle) : A.Lebt σ r.handle.slot :=
  ArenaOwnership.State.access_live hr.1 ha

/-- A successful abstract allocation and an executed G allocation agree on their
new grant ledger when they allocate the same actual slot. The premises are exact
execution equalities; neither a provider success nor a G execution is postulated
as an axiom. Payload lowering and the whole-program bridge remain separate work. -/
theorem allocation_grant_bridge {H H' : Heap region α} {capacity : Capacity}
    {available : Bool} {f : ArenaOwnership.Frame} {value : α} {r : Ref region}
    {rights : ArenaOwnership.State} {handle : ArenaOwnership.Handle}
    (ha : H.allocate capacity available f value = some (H', r))
    (hg : H.rights.allocate f (H.candidate : Int) = some (rights, handle)) :
    H'.rights = rights ∧ r.handle = handle := by
  have hh := (Heap.allocate_parts ha).2.2.1
  rw [hg] at hh
  have hp := Prod.mk.inj (Option.some.inj hh)
  exact ⟨hp.1.symm, hp.2.symm⟩

end ArenaStorage
end Gabbro.Grammatik
