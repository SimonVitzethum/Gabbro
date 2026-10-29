/- Continuation types for case proofs; the dispatcher keeps the original theorem statements. -/
import Stage0.Senke.Anweisung.Faelle.Rueckgabe
import Stage0.Senke.Anweisung.Tor

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

abbrev StmtCase (L : Lay D) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (cap : Nat)
    (P : Programm D) (f : D.Fn) (fp : Runner.W) (K Ks lo : Nat) (rp cfp : Runner.W)
    (σ0 : World D) (ρ0 : Env D (D.params f)) (cens : List II) (tens : Nat)
    (pr : List Nat) (ex : Int × Int)
{l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D (vertragVon D f) l Γ Λ Λ') : Prop :=
    ∀ (c : List II) (top : Nat),
    lowS A L lo (cens, tens) pr ex s = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    FB ≤ lo → lo ≤ frei Γ → Umf L A C dv m fp Ks K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R s σ ρ)

abbrev BlockCase (L : Lay D) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (cap : Nat)
    (P : Programm D) (f : D.Fn) (fp : Runner.W) (K Ks lo : Nat) (rp cfp : Runner.W)
    (σ0 : World D) (ρ0 : Env D (D.params f)) (cens : List II) (tens : Nat)
    (pr : List Nat) (ex : Int × Int)
{l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D (vertragVon D f) l Γ Λ Λ') : Prop :=
    ∀ (c : List II) (top : Nat),
    lowB A L lo (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    FB ≤ lo → lo ≤ frei Γ → Umf L A C dv m fp Ks K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R b σ ρ)

abbrev EndCase (L : Lay D) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (cap : Nat)
    (P : Programm D) (f : D.Fn) (fp : Runner.W) (K Ks lo : Nat) (rp cfp : Runner.W)
    (σ0 : World D) (ρ0 : Env D (D.params f)) (cens : List II) (tens : Nat)
    (pr : List Nat) (ex : Int × Int)
{l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D (vertragVon D f) l Γ Λ) : Prop :=
    ∀ (c : List II) (top : Nat), lowEnd A L lo (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    lo ≤ frei Γ → Umf L A C dv m fp Ks K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R b σ ρ)

theorem encErg_wert {e : Option Ty} {τ : Ty} (he : e = some τ) {v : ErgVal D e} {w : Runner.W}
    (h : EncErg e v w) : Enc τ (ergWert he v) w := by
  subst he; exact h

end Gabbro.Stage0.Senke
