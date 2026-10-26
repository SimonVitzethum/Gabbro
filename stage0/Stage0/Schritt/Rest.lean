/-
  File:      stage0/Stage0/Schritt/Rest.lean
  Subject:   The executable step, part 4: the residues that are no block -- `frei` (release a lock), `schrumpf`
             (drop a binding), the traverse (`trav`, `travRest`), the bounded retry (`wieder`, `wiederRest`) and the
             forever loop (`ewig`, `ewigRest`). A traverse or loop whose invariant is false does not step (the
             machine stops there, as in the model: `trav_falsch_steht`).
-/
import Stage0.Schritt.Grund

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-- **A head residue that is no block and no end block.** -/
def zugRest (M : RufMaschineG D) (f : Faden) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) : Option (Zug P O passes M f) :=
  match r, ρ, hk with
  | .frei (Λ := Λ0) L k, ρ, hk => some ⟨_, .freiGib M f l Γ Λ0 L k ρ hk⟩
  | .schrumpf (Γ := Γ0) (τ := τ) k, .cons v ρ0, hk => some ⟨_, .schrumpfVergiss M f l Γ0 Λ τ k v ρ0 hk⟩
  | .trav t inv body (i :: is) k, ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ inv.orte
      if hw : wahr? (eval σ₁ inv σ₁ ρ) = true then
        some ⟨_, .travNext M f l Γ Λ t inv body i is k ρ hk σ₁ rfl hw _ (lese_neu M f Λ inv.orte)
          (heldIn_of hΛ)⟩
      else none
    else none
  | .trav t inv body [] k, ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ inv.orte
      if hw : wahr? (eval σ₁ inv σ₁ ρ) = true then
        some ⟨_, .travDone M f l Γ Λ t inv body k ρ hk σ₁ rfl hw _ (lese_neu M f Λ inv.orte) (heldIn_of hΛ)⟩
      else none
    else none
  | .travRest (l := l0) (Γ := Γ0) t inv body is k, .cons i ρ0, hk =>
    some ⟨_, .travFort M f l0 Γ0 Λ t inv body is k i ρ0 hk⟩
  | .wieder 0 bis body ueber k, ρ, hk => some ⟨_, .wiederUeber M f l Γ Λ bis body ueber k ρ hk⟩
  | .wieder (n + 1) bis body ueber k, ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ bis.orte
      if hw : wahr? (eval σ₁ bis σ₁ ρ) = true then
        some ⟨_, .wiederWeiter M f l Γ Λ n bis body ueber k ρ hk σ₁ rfl hw _ (lese_neu M f Λ bis.orte)
          (heldIn_of hΛ)⟩
      else
        some ⟨_, .wiederSchritt M f l Γ Λ n bis body ueber k ρ hk σ₁ rfl (by simpa using hw) _
          (lese_neu M f Λ bis.orte) (heldIn_of hΛ)⟩
    else none
  | .wiederRest (l := l0) n bis body ueber k, ρ, hk =>
    some ⟨_, .wiederFort M f l0 Γ Λ n bis body ueber k ρ hk⟩
  | .ewig a (n + 1) inv body k, ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ inv.orte
      if hw : wahr? (eval σ₁ inv σ₁ ρ) = true then
        some ⟨_, .ewigWeiter M f l Γ Λ a n inv body k ρ hk σ₁ rfl hw _ (lese_neu M f Λ inv.orte)
          (heldIn_of hΛ)⟩
      else none
    else none
  | .ewigRest (l := l0) a n inv body k, ρ, hk => some ⟨_, .ewigFort M f l0 Γ Λ a n inv body k ρ hk⟩
  | _, _, _ => none

end Gabbro.Stage0
