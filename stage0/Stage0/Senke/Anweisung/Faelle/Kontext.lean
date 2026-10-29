/- Continuation types for case proofs; the dispatcher keeps the original theorem statements. -/
import Stage0.Senke.Anweisung.Faelle.Rueckgabe
import Stage0.Senke.Anweisung.Tor
import Stage0.Senke.Anweisung.Fnptr

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

abbrev StmtCase (L : Lay D) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (cap : Nat)
    (P : Programm D) (f : D.Fn) (fp : Runner.W) (K Ks lo : Nat) (rp cfp : Runner.W)
    (σ0 : World D) (ρ0 : Env D (D.params f)) (cens : List II) (tens : Nat)
    (pr : List Nat) (ex : Int × Int)
{l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D (vertragVon D f) l Γ Λ Λ') (reserved : Nat := 0) : Prop :=
    ∀ (c : List II) (top : Nat),
    lowS (reserved := reserved) passes A L lo (cens, tens) pr ex s = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved →
    FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R s σ ρ) reserved

abbrev BlockCase (L : Lay D) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (cap : Nat)
    (P : Programm D) (f : D.Fn) (fp : Runner.W) (K Ks lo : Nat) (rp cfp : Runner.W)
    (σ0 : World D) (ρ0 : Env D (D.params f)) (cens : List II) (tens : Nat)
    (pr : List Nat) (ex : Int × Int)
{l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D (vertragVon D f) l Γ Λ Λ') (reserved : Nat := 0) : Prop :=
    ∀ (c : List II) (top : Nat),
    lowB (reserved := reserved) passes A L lo (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved →
    FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R b σ ρ) reserved

abbrev EndCase (L : Lay D) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (cap : Nat)
    (P : Programm D) (f : D.Fn) (fp : Runner.W) (K Ks lo : Nat) (rp cfp : Runner.W)
    (σ0 : World D) (ρ0 : Env D (D.params f)) (cens : List II) (tens : Nat)
    (pr : List Nat) (ex : Int × Int)
{l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D (vertragVon D f) l Γ Λ) (reserved : Nat := 0) : Prop :=
    ∀ (c : List II) (top : Nat), lowEnd (reserved := reserved) passes A L lo (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved →
    lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R b σ ρ)


end Gabbro.Stage0.Senke
