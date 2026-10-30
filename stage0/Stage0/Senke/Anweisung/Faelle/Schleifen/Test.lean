/- A retry check preserves the read event and either finishes or enters the remaining attempts. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.Verzweigung
import Stage0.Senke.Anweisung.Faelle.Schleifen.Code

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable {reserved : Nat}
variable [Kern] {D : Deklaration} {L : Lay D}

section
variable {P : Programm D} {f : D.Fn} {fp : Runner.W}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
  {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)}
  {pr : List Nat} {ex : Int × Int} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
  {bis : Expr D Γ Λ .bool} {cc rest : List II} {tc : Nat}
  {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}

theorem retryTest_ok (hcc : lowE (reserved := reserved) L bis (frei Γ reserved) = some (cc, tc)) (ht : tc ≤ Ks)
    (hs : 16 * (cc.length + 2 + rest.length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length)
    (hlo2 : lo ≤ frei Γ reserved) (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    {oe : Ausgang (vertragVon D f) l Γ}
    (helse : ∀ m' pc', PreS L m' pc' fp K (frei Γ reserved) rest ρ reserved →
      Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * rest.length))
        (pc' + BitVec.ofNat 64 (16 * rest.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * rest.length) + BitVec.ofInt 64 ex.2) oe reserved)
    (hp : PreS L m pc fp K (frei Γ reserved) (retryTest (frei Γ reserved) cc rest) ρ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (retryTest (frei Γ reserved) cc rest).length))
      (pc + BitVec.ofNat 64 (16 * (retryTest (frei Γ reserved) cc rest).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (retryTest (frei Γ reserved) cc rest).length) + BitVec.ofInt 64 ex.2)
      (if wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) then .ok (σ.lese Λ bis.orte) ρ else oe) reserved := by
  have htop := lowE_top bis (frei Γ reserved) cc tc hcc
  have he : retryTest (frei Γ reserved) cc rest = cc ++ [ci 19 (frei Γ reserved) 32 0] ++ [] ++
      [ci 18 (16 * (rest.length + 1)) 0 0] ++ rest := by simp [retryTest]
  rw [he] at hp ⊢
  apply choice_ok (ρ := ρ) (d := frei Γ reserved) (ct := []) (cc := cc) (ce := rest)
    (b := wahr? (D := D) (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))
    (Nat.le_refl _) (by have := hW.ks; omega) (by simpa using hs) hW hlo hlo0 hlo2 hpr

  · intro hpc
    have hks := hW.ks
    have hpw := PreS.welt hpc hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, st, a1, w, hw, hen⟩ := lowE_ok (σ.lese Λ bis.orte) (σ.lese Λ bis.orte)
      (fun _ h => h) bis (frei Γ reserved) cc tc hcc (by omega) m pc ρ hpw
    exact ⟨m1, st, Agree.widen a1 hks, w, hw, hen⟩
  · intro _ m' pc' hp' _ _ _ hw'
    exact ⟨m', by simpa using Star.refl ⟨pc', fp⟩ m', AgreeW.refl _ _ _ _ _, hp'.env, hw', Keeps.refl _ _ _⟩
  · intro _ m' pc' hp' _ hu' hk' hw'
    exact helse m' pc' hp' hu' hk' hw'
  · exact hp
  · exact hu
  · exact hk
  · exact hWa
end
end Gabbro.Stage0.Senke
