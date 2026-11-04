/- Generic complete-span sum dispatch, preserving inputs until an arm is selected. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Sum.Arm
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {O : Orakel D} {passes : Nat}
  {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} {P : Programm D}
  {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp : Runner.W} {lo Ks K : Nat}
  {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}

local notation "BR" => BlockRuns (reserved := reserved) O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K ens pr

/-- The source span stays below every test. Only the selected arm copies it into
    the payload binding; recursive tests never change any payload word. -/
theorem lowSumTags_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D (vertragVon D f) l Γ Λ Λ' cs)
    (blocks : ArmsAll (fun b => BR b) arms) {span k : Nat} {cd : List II} {top : Nat}
    (width : ∀ i : Fin cs.length, 1 + payloadWords (cs.get i) ≤ span)
    (made : lowSumTags (reserved := reserved) passes A L (functionFrame P f) ens pr ex arms span k = some (cd, top))
    (fits : top + cap ≤ Ks) (size : 16 * cd.length < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = (functionFrame P f).internalResult)
    (hlo2 : lo ≤ frei Γ reserved) (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (v : Wert D (.sum cs)) (hi : k + v.1.val < 2 ^ 31)
    (tag : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 (k + v.1.val)))
    (payload : PayloadAt L m fp (frei Γ reserved + 1) (cs.get v.1) (Fall.toNutzlast _ _ _ _ v.2))
    (pre : PreS L m pc fp K (frei Γ reserved) cd ρ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * cd.length))
      (pc + BitVec.ofNat 64 (16 * cd.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * cd.length) + BitVec.ofInt 64 ex.2)
      (execArms O passes R arms v σ ρ) reserved := by
  cases arms with
  | nil => exact Fin.elim0 v.1
  | cons b rest =>
    rename_i payloadTy restSchema
    simp only [lowSumTags, ← hlo0] at made
    split at made
    · next hkSmall =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at made
      obtain ⟨⟨cr, tr⟩, restMade, ⟨cb, tb⟩, blockMade, out⟩ := made
      simp only [Prod.mk.injEq] at out
      obtain ⟨rfl, rfl⟩ := out
      have spanPositive : 0 < span := by have := width v.1; omega
      have selectedWidth := width v.1
      have restWidth : ∀ j : Fin restSchema.length,
          1 + payloadWords (restSchema.get j) ≤ span := by
        intro j
        simpa only [List.get_cons_succ] using
          width ⟨j.val + 1, by have := j.isLt; omega⟩
      have hks := hW.ks
      let cp := sumSpanPayloadC (frei Γ reserved) payloadTy
      have p : PreS L m pc fp K (frei Γ reserved)
          (sumSpanTestC (frei Γ reserved) (frei Γ reserved + span) k ++
            [ci 19 (frei Γ reserved + span) (16 * ((cp ++ cb).length + 2)) 0] ++
            (cp ++ cb) ++ [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr) ρ reserved := by
        simpa only [cp, List.length_append, List.append_assoc, Int.natCast_add] using pre
      have result := choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ reserved + span)
        (b := k + v.1.val == k) (ot := execArms O passes R (.cons b rest) v σ ρ)
        (oe := execArms O passes R (.cons b rest) v σ ρ)
        (by omega) (by omega)
        (by
          simp only [sumSpanTestC, List.length_append, List.length_cons, List.length_nil, cp] at size ⊢
          omega)
        hW hlo hlo0 hlo2 hpr
        (fun pcnd => sumSpanTest_ok (by omega) hkSmall (by omega) (by omega)
          ⟨by have := pcnd.ctx; omega, pcnd.small, pcnd.frame, pcnd.code, pcnd.far,
            pcnd.env, trivial, wstab_true _ _⟩ tag)
        (fun selected m' pc' p1 changed hu1 hk1 world1 => ?_)
        (fun skipped m' pc' p1 changed hu1 hk1 world1 => ?_) p hu hk world
      · simpa only [ite_self, List.length_append, List.length_singleton, Nat.add_assoc, cp] using result
      · have zero : v.1.val = 0 := by have := eq_of_beq selected; omega
        rcases v with ⟨⟨i, hiv⟩, val⟩
        change i = 0 at zero
        subst i
        change 1 + payloadWords payloadTy ≤ span at selectedWidth
        change PayloadAt L m fp (frei Γ reserved + 1) payloadTy val at payload
        simp only [execArms]
        have kept := payload.agree_low changed pre.frame.room (by omega) (by omega)
        exact sumSpanArm_ok blocks.1 blockMade (by omega) (by
          simp only [List.length_append, sumSpanTestC, List.length_cons, List.length_nil] at size
          omega) (by omega) hW hlo hlo0 hlo2 hpr
          val kept p1 hu1 hk1 world1
      · have nonzero : v.1.val ≠ 0 := by
          intro zero
          simp only [zero, Nat.add_zero, beq_self_eq_true] at skipped
          cases skipped
        rcases v with ⟨⟨i, hiv⟩, val⟩
        cases i with
        | zero => exact (nonzero rfl).elim
        | succ i =>
          change k + (i + 1) < 2 ^ 31 at hi
          change 1 + payloadWords (restSchema.get ⟨i, Nat.lt_of_succ_lt_succ hiv⟩) ≤ span at selectedWidth
          change PayloadAt L m fp (frei Γ reserved + 1)
            (restSchema.get ⟨i, Nat.lt_of_succ_lt_succ hiv⟩)
            (Fall.toNutzlast D.Fn D.passt restSchema ⟨i, Nat.lt_of_succ_lt_succ hiv⟩ val) at payload
          simp only [execArms]
          have keptTag : m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) =
              some (BitVec.ofNat 64 (k + (i + 1))) := by
            rw [agree_rd_low changed pre.frame.room (by omega) (by omega)]
            exact tag
          have kept := payload.agree_low changed pre.frame.room (by omega) (by omega)
          exact lowSumTags_ok rest blocks.2 restWidth
            restMade (by omega) (by
              simp only [List.length_append, sumSpanTestC, List.length_cons, List.length_nil] at size
              omega) hW hlo hlo0 hlo2 hpr
            ⟨⟨i, Nat.lt_of_succ_lt_succ hiv⟩, val⟩
            (by simpa only [Fin.val_mk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi)
            (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using keptTag)
            kept p1 hu1 hk1 world1
    · cases made
termination_by cs.length

/-- Every arm needs at least a test, conditional branch and trailing jump. Thus
    the tag-count gate rejects only an already unrepresentable code image. -/
theorem lowSumTags_code_bound {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs)
    (layout : FrameLayout) (span k : Nat) {code : List II} {top : Nat}
    (made : lowSumTags (reserved := reserved) passes A L layout ens pr ex arms span k = some (code, top)) :
    5 * cs.length ≤ code.length := by
  cases arms with
  | nil =>
    simp only [lowSumTags, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨rfl, rfl⟩ := made
    decide
  | cons b rest =>
    simp only [lowSumTags] at made
    split at made
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
      obtain ⟨⟨cr, tr⟩, restMade, ⟨cb, tb⟩, _, rfl, rfl⟩ := made
      have bound := lowSumTags_code_bound rest layout span (k + 1) restMade
      simp only [List.length_cons, List.length_append, List.length_nil, sumSpanTestC]
      omega
    · cases made
termination_by cs.length

end Gabbro.Stage0.Senke
