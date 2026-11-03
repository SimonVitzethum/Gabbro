/- Connect the aggregate sum dispatcher to the actual statement simulation. -/
module
public import Stage0.Senke.Anweisung.Faelle.Sum.Dispatch
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {O : Orakel D} {passes : Nat}
  {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} {P : Programm D}
  {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp : Runner.W} {lo Ks K : Nat}
  {ens : List II × Nat} {pr : List Nat}

local notation "BR" => BlockRuns (reserved := reserved) O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K ens pr

/-- A tag count reaching the immediate bound necessarily needs an unrepresentable
    dispatch body. Payload widths themselves impose no admission restriction. -/
theorem onSumTag_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    {v : Expr D Γ Λ (.sum cs)} {arms : Arms D (vertragVon D f) l Γ Λ Λ' cs}
    {cv ca : List II} {tv ta : Nat} {ex : Int × Int}
    (blocks : ArmsAll (fun b => BR b) arms) (separate : sumFits cs = false)
    (count : cs.length < 2 ^ 31)
    (hcv : lowE (reserved := reserved) L v (frei Γ reserved) = some (cv, tv))
    (hca : lowSumTags (reserved := reserved) passes A L (functionFrame P f) ens pr ex arms (valueWords (.sum cs)) 0 = some (ca, ta))
    (htv : tv ≤ Ks) (hta : ta + cap ≤ Ks) (size : 16 * (cv.length + ca.length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = (functionFrame P f).internalResult)
    (hlo2 : lo ≤ frei Γ reserved) (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (pre : PreS L m pc fp K (frei Γ reserved) (cv ++ ca) ρ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length))
      (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (.onTag v arms) σ ρ) reserved := by
  have htop := lowE_top v _ _ _ hcv
  have hks := hW.ks
  have pw := PreS.welt pre.left hks world hW.lay (by have := hW.lo; omega)
  let σE := σ.lese Λ v.orte
  let val := eval σE v σE ρ
  obtain ⟨m1, steps, changed, output⟩ := lowE_ok (same := by intro _; rfl) σE σE
    (fun _ h => h) hW.lay v _ cv tv hcv htv m pc ρ pw
  have ch := Agree.widen changed hks
  have p1 := pre.next ch (Nat.le_refl _) (by omega)
  have header : integerWords 0 (cs.length - 1) = 1 := integerWords_unsigned (by decide) (by omega)
  have span : valueWords (.sum cs) = 1 + sumPayloadWords cs := by
    simp only [valueWords, separate, Bool.false_eq_true, ↓reduceIte, header]
  have tagWords := output.2
  rw [encodeWords_sum L separate, List.append_assoc, wordsAt_append] at tagWords
  have tag : m1.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 val.1.val) := by
    have read := tagWords.1 0 (by simp only [integerEncoding_length, header]; decide)
    simpa only [header, integerEncoding, List.getElem_cons_zero, Nat.add_zero, BitVec.ofInt_natCast] using read
  have payload := output.sum_payload separate
  rw [header] at payload
  have result := lowSumTags_ok (σ := σE) arms blocks
    (fun i => by have := payloadWords_bound cs i; rw [span]; omega)
    hca hta (by omega) hW hlo hlo0 hlo2 hpr val (by have := val.1.isLt; omega)
    (by simpa only [Nat.zero_add] using tag) payload p1
    (hu.agreeW hW (agreeW_of (ch.mono hlo2)) hlo)
    (hk.agreeW hW (agreeW_of (ch.mono hlo2)) (by omega))
    (pw.wstab m m1 world (changed.mono (Nat.zero_le _)))
  simp only [execStmt]
  rw [pc_add1]
  exact Sim.prefix hlo steps (agreeW_of (ch.mono hlo2))
    (keeps_of_agreeW hW ch hpr (by omega)) result

end Gabbro.Stage0.Senke
