/- One native computation followed by a retained-result source range check. -/
module
public import Stage0.Senke.Anweisung.Faelle.Binden
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Anweisung.Faelle.Gleit.AddCode
public import Stage0.Senke.Ausdruck.Gleit.Slots.Test
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The arithmetic/conversion child runs once. The guard only loads its actual
    raw result; success constructs the exact finite source value in that slot. -/
theorem nativeFloatBind_ok {P : Programm D} {f : D.Fn} {fp : Runner.W}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
    {K Ks lo : Nat} {reserved : Nat} {rp cfp : Runner.W} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {pr : List Nat} {ex : Int × Int} {l : Bool}
    {Γ : Ctx} {ρ : Env D Γ} {σ : World D} {low high : Int × Int} {x : Float}
    {ce cc cr : List II} {tc : Nat}
    (out : Gleit low high → Ausgang (vertragVon D f) l (.fl low high :: Γ))
    (guard : floatRetainedRangeL (frei Γ reserved) (frei Γ reserved + 1) low high = some (cc, tc))
    (guardRoom : tc ≤ Ks)
    (size : 16 * (ce.length + (floatNarrowC (frei Γ reserved + 1) cc
      (stopC 107 (frei Γ reserved)) [] cr).length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo)
    (hlo0 : lo = (functionFrame P f).internalResult) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    (compute : ∀ m pc, Pre L m pc fp Ks (frei Γ reserved) ce ρ
      (fun m => WeltAt m L σ) reserved →
      Ok m pc fp Ks (frei Γ reserved) ce (fun w => Runner.readFloat w = x))
    (continuation : ∀ (v : Gleit low high) m' pc',
      PreS L m' pc' fp K (frei (.fl low high :: Γ) reserved) cr
        (Env.cons (τ := .fl low high) v ρ) reserved →
      Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m'
        (pc' + BitVec.ofNat 64 (16 * cr.length))
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.2) (out v) reserved)
    {m : Runner.Mem} {pc : Runner.W}
    (pre : PreS L m pc fp K (frei Γ reserved)
      (ce ++ floatNarrowC (frei Γ reserved + 1) cc (stopC 107 (frei Γ reserved)) [] cr) ρ reserved)
    (umf : Umf L A C dv m fp Ks K) (kopf : Kopf L f m fp K rp cfp ρ0 P σ0)
    (world : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (ce ++ floatNarrowC (frei Γ reserved + 1) cc
        (stopC 107 (frei Γ reserved)) [] cr).length))
      (pc + BitVec.ofNat 64 (16 * (ce ++ floatNarrowC (frei Γ reserved + 1) cc
        (stopC 107 (frei Γ reserved)) [] cr).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (ce ++ floatNarrowC (frei Γ reserved + 1) cc
        (stopC 107 (frei Γ reserved)) [] cr).length) + BitVec.ofInt 64 ex.2)
      (match gleitPasst low high x with | none => .logik .bereich | some v => (out v).schrumpf) reserved := by
  have room := floatRangeL_room guard
  have hks := hW.ks
  have input : frei Γ reserved < Ks := by omega
  have pw := PreS.welt pre.left hks world hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, run, agreeS, word, read, decoded⟩ := compute m pc pw
  have agree := Agree.widen agreeS hks
  have next := pre.next agree (Nat.le_refl _) (by omega)
  have u1 := umf.agreeW hW (agreeW_of (agree.mono hlo2)) hlo
  have k1 := kopf.agreeW hW (agreeW_of (agree.mono hlo2)) (by omega)
  have w1 := pw.wstab m m1 world (agreeS.mono (Nat.zero_le _))
  have branches := choice_ok (P := P) (σ0 := σ0) (ex := ex)
    (m := m1) (pc := pc + BitVec.ofNat 64 (16 * ce.length)) (ρ := ρ)
    (d := frei Γ reserved + 1) (cc := cc) (ct := stopC 107 (frei Γ reserved)) (ce := cr)
    (b := floatRangeReject low high x)
    (ot := match gleitPasst low high x with | none => .logik .bereich | some v => (out v).schrumpf)
    (oe := match gleitPasst low high x with | none => .logik .bereich | some v => (out v).schrumpf)
    (by omega) (by omega)
    (by simp only [floatNarrowC, List.length_append, List.length_singleton,
      List.length_nil, Nat.zero_add, List.nil_append] at size ⊢; omega)
    hW hlo hlo0 hlo2 hpr (σ := σ) ?_ ?_ ?_
    (by simpa only [floatNarrowC, List.nil_append, List.length_nil,
      Int.natCast_zero, Int.zero_add] using next) u1 k1 w1
  · have result := branches
    simp only [ite_self] at result
    simpa only [floatNarrowC, List.nil_append, List.length_nil,
      Int.natCast_zero, Int.zero_add, pc_add1] using
      Sim.prefix hlo run (agreeW_of (agree.mono hlo2))
        (keeps_of_agreeW hW agree hpr (by omega)) result
  · intro condition
    have p := PreS.welt condition hks w1 hW.lay (by have := hW.lo; omega)
    obtain ⟨m2, steps, unchanged, flag, flagRead, value⟩ :=
      floatRetainedRangeL_ok guard guardRoom p read decoded
    exact ⟨m2, steps, Agree.widen unchanged hks, flag, flagRead,
      by simpa only [bool_word] using value⟩
  · intro rejected m2 pc2 branch _ hu hk hw
    rw [floatRangeReject_none.mpr rejected]
    change Stops ⟨pc2, fp⟩ m2 107
    exact stop_ok branch.code branch.far branch.frame (by omega) branch.small (by decide)
  · intro accepted m2 pc2 branch unchanged hu hk hw
    cases success : gleitPasst low high x with
    | none =>
      have rejected := floatRangeReject_none.mp success
      rw [accepted] at rejected
      cases rejected
    | some v =>
      have retained : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some word := by
        rw [agree_rd_low unchanged next.frame.room (by omega) (by omega)]
        exact read
      have value : ValueAt L m2 fp (frei Γ reserved) (.fl low high) v := by
        apply ValueAt.of_enc (by rfl) retained
        exact nativeFloat_word_eq v.endlich (by simpa only [floatPasst_x success] using decoded)
      have bound := branch.ctx
      have rest : PreS L m2 pc2 fp K (frei (.fl low high :: Γ) reserved) cr (Env.cons v ρ) reserved :=
        ⟨Nat.le_refl _, branch.small, branch.frame, branch.code, branch.far,
          envAt_cons branch.env value, trivial, wstab_true _ _⟩
      exact Sim.schrumpf (continuation v m2 pc2 rest hu hk hw)

end Gabbro.Stage0.Senke
