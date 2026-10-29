/-
  File:      stage0/Stage0/Senke/Anweisung/Verzweigung/Wahl.lean
  Subject:   `ir_sim` for `if c { t } else { e }` (`ite`): the condition into slot `frei Γ`, `brz` to the `else` code, the
             `then` code and a jump over the `else` code; G's branch is the code's (`ite_ok`). The branches' own
             simulations come in as hypotheses (the induction of `lowS_ok`).
-/
import Stage0.Senke.Anweisung.Verzweigung

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem ite_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {L : Lay D} {P : Programm D} {f : D.Fn} {fp : Runner.W}
    {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cnd : Expr D Γ Λ .bool}
    {t e : Block D (vertragVon D f) l Γ Λ Λ'} {cc ct ce : List II} {tc tt te : Nat}
    (hcc : lowE L cnd (frei Γ) = some (cc, tc)) (htc : tc ≤ Ks) (htt : tt ≤ Ks) (hte : te ≤ Ks)
    (hs : 16 * (cc.length + 1 + ct.length + 1 + ce.length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hthen : ∀ m' pc', PreS L m' pc' fp K (frei Γ) ct ρ → Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 →
      WeltAt m' L (σ.lese Λ cnd.orte) →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * ct.length))
        (pc' + BitVec.ofNat 64 (16 * ct.length) + BitVec.ofInt 64 (exPlus ex (ce.length + 1)).1)
        (pc' + BitVec.ofNat 64 (16 * ct.length) + BitVec.ofInt 64 (exPlus ex (ce.length + 1)).2)
        (execBlock O passes R t (σ.lese Λ cnd.orte) ρ))
    (helse : ∀ m' pc', PreS L m' pc' fp K (frei Γ) ce ρ → Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 →
      WeltAt m' L (σ.lese Λ cnd.orte) →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * ce.length))
        (pc' + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofInt 64 ex.2)
        (execBlock O passes R e (σ.lese Λ cnd.orte) ρ))
    (hp : PreS L m pc fp K (frei Γ) (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
      [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce) ρ)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length))
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cc ++ [ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ ct ++
        [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (.ite cnd t e) σ ρ) := by
  have htop := lowE_top cnd (frei Γ) cc tc hcc
  simp only [execStmt]
  refine choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ)
    (b := wahr? (D := D) (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ))
    (Nat.le_refl _) (by have := hW.ks; omega) hs hW hlo hlo0 hlo2 hpr ?_
    (fun _ m pc hp _ hu hk hw => hthen m pc hp hu hk hw)
    (fun _ m pc hp _ hu hk hw => helse m pc hp hu hk hw) hp hu hk hWa
  intro hpc
  have hks := hW.ks
  have hpw := PreS.welt hpc hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, st, a1, w, hw, hen⟩ := lowE_ok (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte)
    (fun _ h => h) cnd (frei Γ) cc tc hcc htc m pc ρ hpw
  exact ⟨m1, st, Agree.widen a1 hks, w, hw, hen⟩

end Gabbro.Stage0.Senke
