/- Reach the selected block inside an emitted conditional, before running its body. -/
module
public import Stage0.Senke.Bild.Block.Plain
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Wahl
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- A statement boundary whose fallthrough is supplied by an enclosing block.
    Its exit offsets already include that enclosing block's remaining suffix. -/
def BodyFrame.RandSIR (B : BodyFrame D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D B.f) l Γ Λ Λ') (pc : Runner.W) (m : Runner.Mem)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  ∃ (c : List II) (top : Nat),
    lowS (reserved := B.reserved) (sc := B.sc) B.passes B.A B.L (functionFrame B.P B.f)
      (B.cens, B.tens) B.pr B.ex s = some (c, top) ∧
    top + B.cap ≤ B.Ks ∧ 16 * c.length < 2 ^ 31 ∧
    PreS B.L m pc B.fp B.K (frei Γ B.reserved) c ρ B.reserved ∧ B.lo ≤ frei Γ B.reserved ∧
    Umf B.L B.A B.C B.dv m B.fp B.Ks B.K B.H ∧
    Kopf B.L B.f m B.fp B.K B.rp B.cfp B.ρ0 B.P B.σ0 ∧ WeltAt m B.L σ ∧
    (∀ i ∈ B.pr, i < frei Γ B.reserved) ∧ HeldIn B.H Λ (vertragVon D B.f).boden

/-- Split the first statement off an end-block boundary without executing code. -/
theorem BodyFrame.randIR_stmt {B : BodyFrame D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D B.f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D B.f) l Γ Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandIR (.cons s rest) pc m σ ρ) : ∃ n, (B.suffix n).RandSIR s pc m σ ρ := by
  obtain ⟨c, top, hl, ht, hs, pre, hlo, hu, hk, hw, hpr, hH⟩ := h
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨cr, tr⟩, _, ⟨cs, ts⟩, hcs, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  exact ⟨cr.length, cs, ts, hcs, by omega, by omega, pre.left, hlo, hu, hk, hw, hpr, hH⟩

/-- Split the first statement off a block boundary without executing code. -/
theorem BodyFrame.randBIR_stmt {B : BodyFrame D} {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {s : Stmt D (vertragVon D B.f) l Γ Λ Λ'} {rest : Block D (vertragVon D B.f) l Γ Λ' Λ''}
    {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandBIR (.cons s rest) pc m σ ρ) : ∃ n, (B.suffix n).RandSIR s pc m σ ρ := by
  obtain ⟨c, top, hl, ht, hs, pre, hlo, hu, hk, hw, hpr, hH⟩ := h
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨cr, tr⟩, _, ⟨cs, ts⟩, hcs, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  exact ⟨cr.length, cs, ts, hcs, by omega, by omega, pre.left, hlo, hu, hk, hw, hpr, hH⟩

/-- Run only the condition and branch instruction. The selected block has its own
    image boundary; neither arm's body is run in the proof of this descent. -/
theorem BodyFrame.randSIR_ite {B : BodyFrame D} (hB : B.Ok) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cnd : Expr D Γ Λ .bool} {t e : Block D (vertragVon D B.f) l Γ Λ Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ} {take : Bool}
    (h : B.RandSIR (.ite cnd t e) pc m σ ρ)
    (hb : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = take) :
    ∃ (n : Nat) (pc2 : Runner.W) (m2 : Runner.Mem),
      Star ⟨pc, B.fp⟩ m ⟨pc2, B.fp⟩ m2 ∧
      (B.suffix n).RandBIR (if take then t else e) pc2 m2 (σ.lese Λ cnd.orte) ρ := by
  obtain ⟨c, top, hl, ht, hs, pre, hlo, hu, hk, hw, hpr, hH⟩ := h
  simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨ct, tt⟩, hct, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append, List.length_singleton] at hs
  have hW := hB.win
  have hks := hW.ks
  have htop := lowE_top cnd (frei Γ B.reserved) cc tc hcc
  have q : PreS B.L m pc B.fp B.K (frei Γ B.reserved)
      (cc ++ ([ci 19 (frei Γ B.reserved) (16 * (ct.length + 2)) 0] ++
        (ct ++ ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)))) ρ B.reserved := by
    simpa only [List.append_assoc, Int.natCast_add, Int.ofNat_one] using pre
  have pw := PreS.welt q.left hks hw hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw1, hen⟩ := lowE_ok (same := by intro _; rfl)
    (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) (fun _ h => h) hW.lay cnd
    (frei Γ B.reserved) cc tc hcc (by omega) m pc ρ pw |>.word trivial
  have a1 := Agree.widen a1s hks
  have world : WeltAt m1 B.L (σ.lese Λ cnd.orte) :=
    pw.wstab m m1 hw (a1s.mono (Nat.zero_le _))
  have q1 := q.next a1 (Nat.le_refl _) (by omega)
  have q2 := q1.next (a := [ci 19 (frei Γ B.reserved) (16 * (ct.length + 2)) 0])
    (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have hu1 := hu.agree a1 pre.frame (by simp only [frei]; omega)
  have hk1 := hk.agree a1 pre.frame (by rw [← hB.lo0]; exact hlo)
  simp only [Enc, hb] at hen
  cases take with
  | true =>
    have sb := brz_stay q1.left.code (by have := pre.small; omega) pre.small
      (by simpa only [hen] using hw1) (by decide : (1 : Runner.W) ≠ 0)
    exact ⟨ce.length + 1, _, m1, s1.trans sb,
      ct, tt, hct, by omega, by omega, q2.left, hlo, hu1, hk1, world, hpr, hH⟩
  | false =>
    have sb := brz_go q1.left.code (by have := pre.small; omega) pre.small
      (lit32_nat (by omega)) (by simpa only [hen] using hw1)
    have q3 := (q2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)).next
      (a := [ci 18 (16 * (ce.length + 1)) 0 0]) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    have sp : Star ⟨pc, B.fp⟩ m ⟨_, B.fp⟩ m1 := s1.trans sb
    have target : pc + BitVec.ofNat 64 (16 * cc.length) +
        BitVec.ofInt 64 (16 * ((ct.length : Int) + 2)) =
        pc + BitVec.ofNat 64 (16 * cc.length) + BitVec.ofNat 64 (16 * 1) +
          BitVec.ofNat 64 (16 * ct.length) + BitVec.ofNat 64 (16 * 1) := by
      rw [show 16 * ((ct.length : Int) + 2) = ((16 * (ct.length + 2) : Nat) : Int) by omega,
        BitVec.ofInt_natCast]
      simp only [addr_norm]
      congr 2
      omega
    rw [target] at sp
    refine ⟨0, _, m1, sp, ce, te, ?_, by omega, by omega, q3, hlo, hu1, hk1, world, hpr, hH⟩
    simpa only [BodyFrame.suffix, exPlus, Int.natCast_zero, Int.mul_zero, Int.add_zero] using hce

end Gabbro.Stage0.Senke.BildLauf
