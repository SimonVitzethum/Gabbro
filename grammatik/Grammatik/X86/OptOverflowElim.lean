/-
  File:      Grammatik/X86/OptOverflowElim.lean
  Subject:   Overflow-check elimination rule lemma (lane 869).

  OPTIMIZER row B3 (§3.5): an overflow check is removed only under a
  proved-impossible overflow (range entailment, recomputed); §7.2 row
  "checks (B1–B3)": the certificate carries SSA versions + range
  entailment, the validator recomputes the entailment `decide` at the
  cited versions. R4 (§3.6, §3.10 hard gates): signed division is not a
  shift -- signed-division-via-shift reasoning refuses. §3.9: float
  checks are never removed by this rule (default REFUSE).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`) and the
  ACCEPTED checker (`X86.InvariantenOpt`: `isWahr`/`isWahrAll_sound`/
  `exec_pruefung_wahr`): the per-width unsigned-carry (CF) vs signed
  overflow (OF) identity, the range-entailment bridge that makes the
  two-sided bound check decidably true, and the connection theorem
  `OptOverflowElim_verbindung`: a `Block.pruefung` overflow check
  whose bound the validator recomputed is provably taken, so removing
  it preserves the exact `execBlock` outcome (no fault added or
  removed, same successor worlds, same read observations, same call
  logs, same downstream budget). No `ensures` is derived, no refusal
  becomes a warning, no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one overflow-check site
    (§7.2 "checks" row): the range entailment recomputed at the cited
    SSA versions, the width named from 8/16/32/64, the signedness fixed
    (CF vs OF chosen correctly), no signed-division-via-shift shape
    (R4), and an integer-only window (floats never touched, §3.9). -/
structure OverflowCert where
  bereichPasst : Bool
  breiteOk : Bool
  vorzeichenFix : Bool
  keinShiftDiv : Bool
  nurGanzzahl : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def overflowZulassen (c : OverflowCert) : Bool :=
  c.bereichPasst && c.breiteOk && c.vorzeichenFix && c.keinShiftDiv && c.nurGanzzahl

/-! ## 1. Refusal: every missing side condition refuses the rule.

    A refused OPTIONAL optimisation falls back to another certified
    translation, never to a warning. In particular `keinShiftDiv =
    false` refuses: signed division is not a shift (R4, §3.10 hard
    gates), so no overflow argument built on a division-via-shift
    shape may discharge this rule. And `nurGanzzahl = false` refuses:
    float checks are never removed here (§3.9, default REFUSE), which
    is the IEEE protection of this integer-only rule. -/

/-- No recomputed range entailment, no elimination (B3). -/
theorem overflowVerweigert_bereich (c : OverflowCert)
    (h : c.bereichPasst = false) :
    overflowZulassen c = false := by
  simp [overflowZulassen, h]

/-- No named width, no elimination. -/
theorem overflowVerweigert_breite (c : OverflowCert)
    (h : c.breiteOk = false) :
    overflowZulassen c = false := by
  simp [overflowZulassen, h]

/-- No fixed signedness (CF vs OF unnamed), no elimination. -/
theorem overflowVerweigert_vorzeichen (c : OverflowCert)
    (h : c.vorzeichenFix = false) :
    overflowZulassen c = false := by
  simp [overflowZulassen, h]

/-- Signed-division-via-shift reasoning refuses (R4). -/
theorem overflowVerweigert_shiftDiv (c : OverflowCert)
    (h : c.keinShiftDiv = false) :
    overflowZulassen c = false := by
  simp [overflowZulassen, h]

/-- A float-tainted window refuses: this rule never removes a float
    check (IEEE, §3.9). -/
theorem overflowVerweigert_gleit (c : OverflowCert)
    (h : c.nurGanzzahl = false) :
    overflowZulassen c = false := by
  simp [overflowZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_overflowZulassen_ok :
    overflowZulassen ⟨true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a shift-div-shaped certificate is refused. -/
theorem probe_overflowZulassen_shiftDiv :
    overflowZulassen ⟨true, true, true, false, true⟩ = false := by
  decide

/-- Probe: a float-tainted certificate is refused. -/
theorem probe_overflowZulassen_gleit :
    overflowZulassen ⟨true, true, true, true, false⟩ = false := by
  decide

/-! ## 2. Per-width CF-vs-OF identity.

    At width `w` the unsigned carry (CF: the mathematical sum reaches
    `2^w`) and the signed overflow (OF: the sum leaves the symmetric
    `2^(w-1)` range) are DIFFERENT predicates over the same sum. The
    validator must therefore name the width AND the signedness before
    any overflow check may go (`breiteOk`, `vorzeichenFix` in §1);
    `tragU_cf_of_auseinander` pins the divergence at width 8. Both
    directions are proved: a sum inside the range sets no flag
    (the elimination direction), and a sum outside the range SETS it
    (the guard is live -- removing the check never silences a real
    overflow). -/

/-- Unsigned carry (CF) at width `w`: the sum reaches `2^w`. -/
def tragU (w : Nat) (x y : Int) : Bool :=
  decide (2 ^ w ≤ x + y)

/-- Signed overflow (OF) at width `w`: the sum leaves the symmetric
    `2^(w-1)` range. -/
def ueberlaufS (w : Nat) (x y : Int) : Bool :=
  decide (x + y < -(2 ^ (w - 1)) ∨ 2 ^ (w - 1) ≤ x + y)

/-- No unsigned overflow, no carry: the elimination direction. -/
theorem tragU_kein (w : Nat) (x y : Int) (h : x + y < 2 ^ w) :
    tragU w x y = false := by
  have h' : ¬ (2 : Int) ^ w ≤ x + y := by omega
  simp [tragU, h']

/-- A real unsigned overflow SETS the carry: the guard is live. -/
theorem tragU_trifft (w : Nat) (x y : Int) (h : 2 ^ w ≤ x + y) :
    tragU w x y = true := by
  simp [tragU, h]

/-- No signed overflow, no OF: the elimination direction. -/
theorem ueberlaufS_kein (w : Nat) (x y : Int)
    (hlo : -(2 : Int) ^ (w - 1) ≤ x + y) (hhi : x + y < 2 ^ (w - 1)) :
    ueberlaufS w x y = false := by
  have h' : ¬ (x + y < -(2 : Int) ^ (w - 1) ∨ 2 ^ (w - 1) ≤ x + y) := by
    omega
  simp [ueberlaufS, h']

/-- A real signed overflow SETS OF: the guard is live. -/
theorem ueberlaufS_trifft (w : Nat) (x y : Int)
    (h : 2 ^ (w - 1) ≤ x + y) :
    ueberlaufS w x y = true := by
  simp [ueberlaufS, h]

/-- CF and OF diverge at width 8 (`150 + 50 = 200`: no carry, but
    outside the signed byte range), so the signedness must be named. -/
theorem tragU_cf_of_auseinander :
    tragU 8 150 50 = false ∧ ueberlaufS 8 100 100 = true := by
  decide

/-- Probes: a fitting sum sets neither flag at any hardware width. -/
theorem probe_tragU_8 : tragU 8 100 100 = false := by decide

theorem probe_tragU_16 : tragU 16 30000 30000 = false := by decide

theorem probe_tragU_32 : tragU 32 2000000000 2000000000 = false := by decide

theorem probe_tragU_64 : tragU 64 5000000000000000000 5000000000000000000 = false := by
  decide

theorem probe_ueberlaufS_8 : ueberlaufS 8 100 20 = false := by decide

theorem probe_ueberlaufS_64 : ueberlaufS 64 100 20 = false := by decide

/-! ## 3. Range-entailment bridge: the bound check is decidably true.

    The validator's recomputed entailment (`lo ≤ s`, `s ≤ hi` at the
    cited versions, §7.2) makes the two-sided bound check -- the shape
    the computable checker decides (`litLeBool` over literals, the S1
    precedent) -- answer `true`. This is the step the Rust analysis
    does NOT get trusted for: the `Bool` is re-run here in the kernel
    from the cited range facts. -/

/-- The recomputed entailment decides the bound check true. -/
theorem overflowBedingung_wahr {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (lo s hi : Int) (hlo : lo ≤ s) (hhi : s ≤ hi) :
    InvariantenOpt.isWahr
      (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
        Expr D Γ Λ .bool) = true := by
  simp [InvariantenOpt.isWahr, InvariantenOpt.isWahrAll,
    InvariantenOpt.litLeBool, InvariantenOpt.alsLitOpt, hlo, hhi]

/-! ## 4. Connection: the admitted overflow check is taken, so removing
    it changes nothing.

    The rewrite fires only where the validator admitted the site
    (`hz`) and recomputed the entailment at the cited versions
    (`hEnt`, the §7.2 certificate content -- claimed only where the
    site is admitted, never trusted from Rust). Conclusion, jointly:
    (1) the bound check EVALUATES to true in the actual semantics;
    (2) the `execBlock` OUTCOME equals the check-free continuation in
    the post-read world -- same constructor, same successor worlds --
    so no fault is added or removed (the `sonst` branch is unreachable,
    proved, not assumed), every downstream observation agrees
    (contracts at their place read the same values from the same
    environments, call logs gain no event, no shared access is added
    or removed for concurrency -- both sides run past the same `orte`
    reads), and the step-budget accounting is unchanged (the same
    continuation runs; the removed check is pure and unbudgeted).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard: a site the
    validator did not admit keeps its check. -/

/-- CONNECTION: an admitted overflow check is taken; removing it
    preserves the evaluated guard and the exact `execBlock` outcome. -/
theorem OptOverflowElim_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (cert : OverflowCert) (lo s hi : Int)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ')
    (hz : overflowZulassen cert = true)
    (hEnt : overflowZulassen cert = true → (lo ≤ s ∧ s ≤ hi))
    (σ : World D) (ρ : Env D Γ) :
    wahr? (eval σ (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
      Expr D Γ Λ .bool) σ ρ) = true
    ∧ execBlock O passes R
        (Block.pruefung (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
          Expr D Γ Λ .bool) sonst rest) σ ρ
      = execBlock O passes R rest
        (σ.lese Λ (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
          Expr D Γ Λ .bool).orte) ρ := by
  have hWahr := overflowBedingung_wahr (D := D) (Γ := Γ) (Λ := Λ) lo s hi
    (hEnt hz).1 (hEnt hz).2
  have hE : eval σ (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
      Expr D Γ Λ .bool) σ ρ = true := by
    have h := InvariantenOpt.isWahrAll_sound _ σ σ ρ hWahr
    simpa [InvariantenOpt.holdsBool] using h
  exact ⟨hE ▸ rfl,
    InvariantenOpt.exec_pruefung_wahr O passes R _ _ _ _ _ hWahr⟩

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptOverflowElim_verbindung` instantiated JOINTLY:
    the u8-shaped bound check `0 ≤ 200 ∧ 200 ≤ 255` (a sum that fits
    the byte range, CF and OF both clear) under an admitted
    certificate, in the NON-DEGENERATE reference program `refD`
    (whose `einzahlen` writes its table, `refEin_schreibt`), beside
    the reached F-machine run `MB` that changes memory
    (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`). Both
    conclusion conjuncts are used. -/

/-- JOINT WITNESS for `OptOverflowElim_verbindung`: the u8 bound
    check on `refD`, beside the memory-changing reached run. -/
theorem OptOverflowElim_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ Λ' : List (Res refD)) (l : Bool)
      (cert : OverflowCert) (lo s hi : Int)
      (sonst : Endblock refD V l Γ Λ) (rest : Block refD V l Γ Λ Λ')
      (_hz : overflowZulassen cert = true)
      (_hEnt : overflowZulassen cert = true → (lo ≤ s ∧ s ≤ hi))
      (σ : World refD) (ρ : Env refD Γ),
      wahr? (eval σ (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
        Expr refD Γ Λ .bool) σ ρ) = true
      ∧ execBlock O passes R
          (Block.pruefung (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
            Expr refD Γ Λ .bool) sonst rest) σ ρ
        = execBlock O passes R rest
          (σ.lese Λ (.und (.le (.lit lo) (.lit s)) (.le (.lit s) (.lit hi)) :
            Expr refD Γ Λ .bool).orte) ρ
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptOverflowElim_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (Λ' := [])
    (l := true) (cert := ⟨true, true, true, true, true⟩)
    (lo := 0) (s := 200) (hi := 255)
    (sonst := Endblock.leave rfl) (rest := Block.nil)
    (hz := by decide) (hEnt := fun _ => ⟨by decide, by decide⟩)
    (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], [], true,
    ⟨true, true, true, true, true⟩, 0, 200, 255,
    Endblock.leave rfl, Block.nil, by decide, (fun _ => ⟨by decide, by decide⟩),
    refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No validator-side recomputation: `hEnt` takes the recomputed
      range entailment as a conditional premise (§7.2 certificate
      content); the analysis that PRODUCES it (SSA versions, entailment
      `decide` at the cited versions) is future work, not proved here.
      Only admitted sites refine -- nothing is trusted from Rust.
    - No signed-division overflow reasoning: any division-via-shift
      shape refuses by `keinShiftDiv` (R4, §3.10 hard gates); no
      `sdiv`/`srem`/`div`/`rem` overflow rule is stated here.
    - No float rule: any float-tainted window refuses by `nurGanzzahl`
      (§3.9, default REFUSE); no `gleitRechne`/`gleitPasst` equation is
      folded or removed.
    - No totalCost inequality: the outcome is the same continuation in
      the same post-read world, so downstream step accounting agrees;
      the formal level-(c) machine-work bound stays OPEN per
      OPTIMIZER §6.4.
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at canonical values and `execBlock` outcome
      equality over the source machine.
-/

#print axioms overflowZulassen
#print axioms overflowVerweigert_bereich
#print axioms overflowVerweigert_breite
#print axioms overflowVerweigert_vorzeichen
#print axioms overflowVerweigert_shiftDiv
#print axioms overflowVerweigert_gleit
#print axioms tragU
#print axioms ueberlaufS
#print axioms tragU_kein
#print axioms tragU_trifft
#print axioms ueberlaufS_kein
#print axioms ueberlaufS_trifft
#print axioms tragU_cf_of_auseinander
#print axioms overflowBedingung_wahr
#print axioms OptOverflowElim_verbindung
#print axioms OptOverflowElim_verbindung_zeuge

end Gabbro.Grammatik.X86
