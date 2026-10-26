/-
  File:      stage0/Stage0/Schritt/Abbruch.lean
  Subject:   The executable step, part 3: `leave` and `next` at the head of a `dann` block. The continuation decides
             the rule: the rest of a loop (`dannLeave*`/`dannNext*`), or a layer the jump is peeled through
             (`peelDann*`, `peelSchrumpf*`, `peelFrei*`, `peelAbbruch*`).
-/
import Stage0.Schritt.Grund

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-- **`leave` at the head of a `dann` block.** -/
def zugLeave (M : RufMaschineG D) (f : Faden) {Γ : Ctx} {Λ Λ'' : List (Res D)} (ρ : Env D Γ)
    (h : true = true)
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ'')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ'')
    (hk : (M.faeden f).kopf.rest = ⟨true, Γ, Λ, ρ,
      .dann (.cons ((.leave h) : Stmt D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) rest) k⟩) :
    Option (Zug P O passes M f) :=
  match k, ρ, hk with
  | .dann b k', ρ, hk => some ⟨_, .peelDannLeave M f true Γ Λ rest b k' ρ h hk⟩
  | .schrumpf (Γ := Γ0) (τ := τ) k', ρ, hk => some ⟨_, .peelSchrumpfLeave M f true Γ0 Λ τ rest k' ρ h hk⟩
  | .frei L k', ρ, hk => some ⟨_, .peelFreiLeave M f true Γ Λ L rest k' ρ h hk⟩
  | .abbruch (Λk := Λk) k', ρ, hk => some ⟨_, .peelAbbruchLeave M f Γ Λ Λ'' Λk rest k' ρ h hk⟩
  | .travRest (l := l) (Γ := Γ0) (Λ := Λ0) t inv body is k', .cons i ρ0, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ0 inv.orte
      if hw : wahr? (eval σ₁ inv σ₁ ρ0) = true then
        some ⟨_, .dannLeaveTrav M f l Γ0 Λ0 t inv body is k' rest i ρ0 h hk (M.weltVon f) (.cons i ρ0) []
          rfl rfl (fun _ _ hm => by simp at hm) σ₁ rfl hw _ (lese_neu M f Λ0 inv.orte) (heldIn_of hΛ)⟩
      else none
    else none
  | .wiederRest (l := l) (Λ := Λ0) n bis body ueber k', ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      some ⟨_, .dannLeaveWieder M f l Γ Λ0 n bis body ueber k' rest ρ h hk (M.weltVon f) ρ [] rfl rfl
        (fun _ _ hm => by simp at hm) (heldIn_of hΛ)⟩
    else none
  | .ewigRest (l := l) (Λ := Λ0) a n inv body k', ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      some ⟨_, .dannLeaveEwig M f l Γ Λ0 a n inv body k' rest ρ h hk (M.weltVon f) ρ [] rfl rfl
        (fun _ _ hm => by simp at hm) (heldIn_of hΛ)⟩
    else none
  | _, _, _ => none

/-- **`next` at the head of a `dann` block.** -/
def zugNext (M : RufMaschineG D) (f : Faden) {Γ : Ctx} {Λ Λ'' : List (Res D)} (ρ : Env D Γ)
    (h : true = true)
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ'')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ'')
    (hk : (M.faeden f).kopf.rest = ⟨true, Γ, Λ, ρ,
      .dann (.cons ((.next h) : Stmt D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ) rest) k⟩) :
    Option (Zug P O passes M f) :=
  match k, ρ, hk with
  | .dann b k', ρ, hk => some ⟨_, .peelDannNext M f true Γ Λ rest b k' ρ h hk⟩
  | .schrumpf (Γ := Γ0) (τ := τ) k', ρ, hk => some ⟨_, .peelSchrumpfNext M f true Γ0 Λ τ rest k' ρ h hk⟩
  | .frei L k', ρ, hk => some ⟨_, .peelFreiNext M f true Γ Λ L rest k' ρ h hk⟩
  | .abbruch (Λk := Λk) k', ρ, hk => some ⟨_, .peelAbbruchNext M f Γ Λ Λ'' Λk rest k' ρ h hk⟩
  | .travRest (l := l) (Γ := Γ0) (Λ := Λ0) t inv body is k', .cons i ρ0, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      some ⟨_, .dannNextTrav M f l Γ0 Λ0 t inv body is k' rest i ρ0 h hk (M.weltVon f) (.cons i ρ0) [] rfl rfl
        (fun _ _ hm => by simp at hm) (heldIn_of hΛ)⟩
    else none
  | .wiederRest (l := l) (Λ := Λ0) n bis body ueber k', ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      some ⟨_, .dannNextWieder M f l Γ Λ0 n bis body ueber k' rest ρ h hk (M.weltVon f) ρ [] rfl rfl
        (fun _ _ hm => by simp at hm) (heldIn_of hΛ)⟩
    else none
  | .ewigRest (l := l) (Λ := Λ0) a n inv body k', ρ, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      some ⟨_, .dannNextEwig M f l Γ Λ0 a n inv body k' rest ρ h hk (M.weltVon f) ρ [] rfl rfl
        (fun _ _ hm => by simp at hm) (heldIn_of hΛ)⟩
    else none
  | _, _, _ => none

end Gabbro.Stage0
