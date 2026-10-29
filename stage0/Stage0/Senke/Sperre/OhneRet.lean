/-
  File:      stage0/Stage0/Senke/Sperre/OhneRet.lean
  Subject:   A statement or block without `ret` (`retFreiS`, `retFreiB`) never ends in G's `zurueck`: the body of a
             `locks` leaves only by its end, `leave`, `next` or a stop, and every one of these passes the give.
-/
import Stage0.Senke.Sperre.Code

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- The outcome leaves the function, normally or with a reason. -/
def istZ {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Bool
  | .zurueck .. | .why .. => true
  | _ => false

theorem istZ_schrumpf {l : Bool} {Γ : Ctx} {τ : Ty} (o : Ausgang V l (τ :: Γ)) : istZ o.schrumpf = istZ o := by
  cases o <;> rfl

theorem istZ_schrumpfArm {l : Bool} {Γ : Ctx} (c : Option (Int × Int))
    (o : Ausgang V l (ArmCtx Γ c)) : istZ (o.schrumpfArm c) = istZ o := by
  cases c with
  | none => rfl
  | some p => rcases p with ⟨lo, hi⟩; exact istZ_schrumpf o

theorem istZ_mapWelt {l : Bool} {Γ : Ctx} (g : World D → World D) (o : Ausgang V l Γ) :
    istZ (o.mapWelt g) = istZ o := by
  cases o <;> rfl

theorem trav_istZ {l : Bool} {Γ : Ctx} {τ : Ty} {schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ)}
    {inv : World D → Env D Γ → World D × Bool} (h : ∀ σ ρ, istZ (schritt σ ρ) = false) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), istZ (traverseLauf (l := l) schritt inv ks σ ρ) = false
  | [], σ, ρ => by
    simp only [traverseLauf]; split <;> rfl
  | k :: ks, σ, ρ => by
    simp only [traverseLauf]
    split
    · rfl
    · have hk := h (inv σ ρ).1 (.cons k ρ)
      split
      · exact trav_istZ h ks _ _
      · exact trav_istZ h ks _ _
      · split <;> rfl
      · next heq => rw [heq] at hk; cases hk
      · next heq => rw [heq] at hk; cases hk
      · rfl
      · rfl

variable {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}

mutual
theorem retFreiS_istZ : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (s : Stmt D V l Γ Λ Λ') →
    retFreiS s = true → ∀ σ ρ, istZ (execStmt O passes R s σ ρ) = false
  | _, _, _, _, .assignVar .., _, _, _ | _, _, _, _, .assignGlob .., _, _, _
  | _, _, _, _, .assignSlot .., _, _, _ | _, _, _, _, .assignThru .., _, _, _
  | _, _, _, _, .advances .., _, _, _ | _, _, _, _, .retires .., _, _, _
  | _, _, _, _, .leave _, _, _, _ | _, _, _, _, .next _, _, _, _
  | _, _, _, _, .publish .., _, _, _ | _, _, _, _, .putBytes .., _, _, _ => by simp only [execStmt]; rfl
  | _, _, _, _, .call _ _ _ hr, _, σ, ρ => by
    simp only [execStmt]
    split
    · rfl
    · next r _ => exact (Fin.cast hr r).elim0
    · rfl
    · rfl
  | _, _, _, _, .callInd _ _ _ hr, _, σ, ρ => by
    simp only [execStmt]
    split
    next g hg hv =>
      split
      · rfl
      · next r _ => exact keinGrundSig hg hr r
      · rfl
      · rfl
  | _, _, _, _, .axiomCall .., _, σ, ρ => by
    simp only [execStmt]
    split <;> rfl
  | _, _, _, _, .ite _ t e, h, σ, ρ => by
    simp only [retFreiS, Bool.and_eq_true] at h
    simp only [execStmt]
    split
    · exact retFreiB_istZ t h.1 _ _
    · exact retFreiB_istZ e h.2 _ _
  | _, _, _, _, .onOption _ p a, h, σ, ρ => by
    simp only [retFreiS, Bool.and_eq_true] at h
    simp only [execStmt]
    split
    · rw [istZ_schrumpf]; exact retFreiB_istZ p h.1 _ _
    · exact retFreiB_istZ a h.2 _ _
  | _, _, _, _, .onTag v arms, h, σ, ρ => by
    exact retFreiArms_istZ arms h _ _ _
  | _, _, _, _, .traverse _ _ b, h, σ, ρ => by
    simp only [retFreiS] at h
    simp only [execStmt]
    exact trav_istZ (fun σ ρ => retFreiB_istZ b h σ ρ) _ _ _
  | _, _, _, _, .breaking _ b, h, σ, ρ => by
    simp only [retFreiS] at h
    simp only [execStmt]
    exact retFreiB_istZ b h _ _
  | _, _, _, _, .locks _ _ b, h, σ, ρ => by
    simp only [retFreiS] at h
    simp only [execStmt]
    rw [istZ_mapWelt]
    exact retFreiB_istZ b h _ _
  | _, _, _, _, .shift .., _, _, _ => by simp only [execStmt]; split <;> rfl
  | _, _, _, _, .onWhy .., h, _, _
  | _, _, _, _, .retry .., h, _, _ | _, _, _, _, .forever .., h, _, _ | _, _, _, _, .regWrite .., h, _, _
  | _, _, _, _, .transition .., h, _, _ | _, _, _, _, .ret .., h, _, _
  | _, _, _, _, .retWhy .., h, _, _ | _, _, _, _, .assignSlotRef .., h, _, _ => by simp [retFreiS] at h

theorem retFreiB_istZ : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (b : Block D V l Γ Λ Λ') →
    retFreiB b = true → ∀ σ ρ, istZ (execBlock O passes R b σ ρ) = false
  | _, _, _, _, .nil, _, _, _ => by simp only [execBlock]; rfl
  | _, _, _, _, .cons s r, h, σ, ρ => by
    simp only [retFreiB, Bool.and_eq_true] at h
    have hs := retFreiS_istZ s h.1 σ ρ
    simp only [execBlock]
    split
    · exact retFreiB_istZ r h.2 _ _
    · exact hs
  | _, _, _, _, .bind _ r, h, σ, ρ => by
    simp only [retFreiB] at h
    simp only [execBlock]
    rw [istZ_schrumpf]
    exact retFreiB_istZ r h _ _
  | _, _, _, _, .bindCall _ _ _ _ hr r, h, σ, ρ => by
    simp only [retFreiB] at h
    simp only [execBlock]
    split
    · rw [istZ_schrumpf]; exact retFreiB_istZ r h _ _
    · next r' _ => exact (Fin.cast hr r').elim0
    · rfl
    · rfl
  | _, _, _, _, .bindCallInd _ _ _ _ hr r, h, σ, ρ => by
    simp only [retFreiB] at h
    simp only [execBlock]
    split
    next g hg hv =>
      split
      · rw [istZ_schrumpf]; exact retFreiB_istZ r h _ _
      · next r' _ => exact keinGrundSig hg hr r'
      · rfl
      · rfl
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ r, h, σ, ρ => by
    simp only [retFreiB] at h
    simp only [execBlock]
    split
    · rw [istZ_schrumpf]; exact retFreiB_istZ r h _ _
    · rfl
  | _, _, _, _, .awaits _ _ _ _ _ r, h, σ, ρ => by
    simp only [retFreiB] at h
    simp only [execBlock]
    split
    · rw [istZ_schrumpf]; exact retFreiB_istZ r h _ _
    · rfl
  | _, _, _, _, .exchange _ _ _ _ r, h, σ, ρ => by
    simp only [retFreiB] at h
    simp only [execBlock]
    rw [istZ_schrumpf]; exact retFreiB_istZ r h _ _
  | _, _, _, _, .bindCallElse .., h, _, _
  | _, _, _, _, .bindAxiomElse .., h, _, _ | _, _, _, _, .regRead .., h, _, _
  | _, _, _, _, .regReadElse .., h, _, _
  | _, _, _, _, .narrow .., h, _, _ | _, _, _, _, .check .., h, _, _ | _, _, _, _, .float .., h, _, _
  | _, _, _, _, .floatLit .., h, _, _ | _, _, _, _, .floatOf .., h, _, _
  | _, _, _, _, .floatNarrow .., h, _, _ => by simp [retFreiB] at h
theorem retFreiArms_istZ : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → (arms : Arms D V l Γ Λ Λ' cs) →
    retFreiArms arms = true → ∀ v σ ρ, istZ (execArms O passes R arms v σ ρ) = false
  | _, _, _, _, _, .nil, _, ⟨i, _⟩, _, _ => Fin.elim0 i
  | _, _, _, _, _, .cons b rest, h, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
    simp only [retFreiArms, Bool.and_eq_true] at h
    simp only [execArms]
    have hb := retFreiB_istZ b h.1 σ (armEnv nutz ρ)
    exact (istZ_schrumpfArm _ _).trans hb
  | _, _, _, _, _, .cons _ rest, h, ⟨⟨i + 1, _⟩, nutz⟩, σ, ρ => by
    simp only [retFreiArms, Bool.and_eq_true] at h
    exact retFreiArms_istZ rest h.2 _ σ ρ
end

end Gabbro.Stage0.Senke
