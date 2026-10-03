/-
  File:      Grammatik/X86/OptFoldConst.lean
  Subject:   Constant folding / SCCP rule lemma (lane 860).

  DESIGN section 7 row: local premise "operands literal, width exact, no FP
  width change, `bruch` = `rundeBruch`", certificate "A+B avail facts",
  failure case "fold `float` via host `strtod` (double rounding); fold
  across MXCSR scope", phase E, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `Gleitkomma`, `X86.Typen`, `X86.Wort`, `ReferenzB`):
  integer literal folds preserve the evaluated value (the folded literal IS
  the computed value), the folded window takes the same `execStmt` outcome
  (no fault added or removed, same successor world), and the width-exact
  folded value reads back through the canonical word. Float folds preserve
  value and `gleitPasst` outcome exactly where the validator recomputed the
  equation in the kernel model under one rounding scope; both DESIGN failure
  cases are refused by `foldZulassen`. No `ensures` is derived, no refusal
  becomes a warning, no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one constant-fold site
    (DESIGN section 7 row): width-exact operands, no FP width change, the
    float literal is the single `rundeBruch` (kernel-recomputed, never host
    `strtod`), and both FP sites share one rounding scope (FpExport). -/
structure FoldCert where
  breiteOk : Bool
  keineFPWeite : Bool
  einfachGerundet : Bool
  gleicheRundung : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def foldZulassen (c : FoldCert) : Bool :=
  c.breiteOk && c.keineFPWeite && c.einfachGerundet && c.gleicheRundung

/-! ## 1. Refusal: the two DESIGN failure cases must NOT fold.

    A fold whose float literal came through host `strtod` (double rounding:
    decimal string to host double, then to the target width) is refused:
    `einfachGerundet = false` forces `foldZulassen = false`. A fold across
    two rounding scopes (MXCSR differs between the sites, FpExport) is
    refused: `gleicheRundung = false` forces `false`. Both are proved of the
    decided Bool, so the validator cannot silently skip them. -/

/-- Host-`strtod` double rounding refuses the fold. -/
theorem foldVerweigert_strtod (c : FoldCert)
    (h : c.einfachGerundet = false) :
    foldZulassen c = false := by
  simp [foldZulassen, h]

/-- A cross-MXCSR-scope fold refuses. -/
theorem foldVerweigert_mxcsr (c : FoldCert)
    (h : c.gleicheRundung = false) :
    foldZulassen c = false := by
  simp [foldZulassen, h]

/-- A width-changing FP fold refuses. -/
theorem foldVerweigert_weite (c : FoldCert)
    (h : c.keineFPWeite = false) :
    foldZulassen c = false := by
  simp [foldZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_foldZulassen_ok :
    foldZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: a `strtod`-tainted certificate is refused. -/
theorem probe_foldZulassen_strtod :
    foldZulassen ⟨true, true, false, true⟩ = false := by
  decide

/-- Probe: a cross-scope certificate is refused. -/
theorem probe_foldZulassen_mxcsr :
    foldZulassen ⟨true, true, true, false⟩ = false := by
  decide

/-! ## 2. Integer literal folds: the folded literal IS the computed value.

    Each lemma is over ARBITRARY values (`x y : Int`): the "operands
    literal" premise is carried by the syntax rewrite of section 4, which
    fires only on `.lit` operands. `add`/`sub`/`mul`/`neg` are total;
    `div`/`rem` keep the source `M102` side conditions (`h0`, `h1'`) as
    validator-decided premises, forwarded unchanged, so no fault is added
    or removed: a zero divisor never reaches the fold. -/

/-- `x + y` folds to `x + y`: the value is preserved. -/
theorem foldAdd_wert (x y : Int) :
    (Zahl.add (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x + y := by
  rfl

/-- `x - y` folds to `x - y`. -/
theorem foldSub_wert (x y : Int) :
    (Zahl.sub (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x - y := by
  rfl

/-- `x * y` folds to `x * y` (four-corner range needs no premise: the
    folded literal carries its own exact range `.int (x*y) (x*y)`). -/
theorem foldMul_wert (x y : Int) :
    (Zahl.mul (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x * y := by
  rfl

/-- `-x` folds to `-x`. -/
theorem foldNeg_wert (x : Int) :
    (Zahl.neg (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)).n = -x := by
  rfl

/-- `x / y` folds to `x.tdiv y` under the `M102` premises. -/
theorem foldDiv_wert (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y) :
    (Zahl.div h0 h1' (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x.tdiv y := by
  rfl

/-- `x % y` folds to `x.tmod y` under the `M102` premises. -/
theorem foldRem_wert (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y) :
    (Zahl.rem h0 h1' (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x.tmod y := by
  rfl

/-- Probes: the folds compute (`7`, `2`, `12`, `-3`, `3`, `1`). -/
theorem probe_foldAdd : (Zahl.add (⟨3, by decide, by decide⟩ : Zahl 3 3)
    (⟨4, by decide, by decide⟩ : Zahl 4 4)).n = 7 := by
  decide

theorem probe_foldSub : (Zahl.sub (⟨5, by decide, by decide⟩ : Zahl 5 5)
    (⟨3, by decide, by decide⟩ : Zahl 3 3)).n = 2 := by
  decide

theorem probe_foldMul : (Zahl.mul (⟨3, by decide, by decide⟩ : Zahl 3 3)
    (⟨4, by decide, by decide⟩ : Zahl 4 4)).n = 12 := by
  decide

theorem probe_foldDiv : (Zahl.div (by decide : (0 : Int) ≤ 7) (by decide : (1 : Int) ≤ 2)
    (⟨7, by decide, by decide⟩ : Zahl 7 7)
    (⟨2, by decide, by decide⟩ : Zahl 2 2)).n = 3 := by
  decide

theorem probe_foldRem : (Zahl.rem (by decide : (0 : Int) ≤ 7) (by decide : (1 : Int) ≤ 2)
    (⟨7, by decide, by decide⟩ : Zahl 7 7)
    (⟨2, by decide, by decide⟩ : Zahl 2 2)).n = 1 := by
  decide

/-! ## 3. Width-exactness: the folded value reads back through the word.

    "Width exact" (DESIGN row) is the validator-decided `hW`: the folded
    value fits the 64-bit canonical word. Under `hW` the word holds the
    value whole -- no truncation, no wrap -- so the later lowering writes
    the folded constant, not a wrapped one. -/

/-- The folded sum reads back whole through the canonical word. -/
theorem foldWort_add (x y : Int) (hW : 0 ≤ x + y ∧ x + y < 2 ^ 64) :
    ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat := by
  have h : (x + y).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `3 + 4` reads back as `7` through the word. -/
theorem probe_foldWort :
    ((BitVec.ofNat 64 ((3 : Int) + 4).toNat : Wort)).toNat = 7 := by
  decide

/-! ## 4. Float fold: single rounding, one scope, same `gleitPasst` outcome.

    The validator precomputes `gleitRechne op` on the two literal values IN
    THE KERNEL (`einfachGerundet`: `bruch = rundeBruch`, never host
    `strtod`) and both sites share one rounding scope (`gleicheRundung`,
    FpExport). The recomputation obligation is conditional on admission
    (`hEq` takes `hz`): the equation is claimed only where the validator
    admitted the site. Conclusion: the folded literal and the recomputed
    op agree under `gleitPasst` -- same pushed value, same `logik bereich`
    outcome, so neither a value nor a fault is folded away. -/

/-- The admitted float fold preserves value and `gleitPasst` outcome. -/
theorem foldGleit_behält (cert : FoldCert) (op : GleitOp)
    (qa qb qf lo hi : Int × Int)
    (hz : foldZulassen cert = true)
    (hEq : foldZulassen cert = true →
      bruch qf = gleitRechne op (bruch qa) (bruch qb)) :
    gleitPasst lo hi (bruch qf) =
      gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb)) := by
  have e := hEq hz
  rw [e]

/-- Probe: the kernel computes `0.5 + 0.25 = 0.75` in one rounding. -/
theorem probe_foldGleit :
    gleitRechne .add (bruch (1, 2)) (bruch (1, 4)) = bruch (3, 4) := by
  decide

/-! ## 5. Connection: the folded bind behaves like the unfolded one.

    The rewrite fires only on `.lit` operands (the DESIGN "operands
    literal" premise by construction) with a width-exact result (`hW`,
    section 3); it is stated at an `Endblock.bind` window with an ARBITRARY
    continuation `rest`, so the conclusion covers every downstream
    observation at once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved;
    (2) the `execEnd` OUTCOME is equal -- same constructor, same successor
    worlds and environments -- so no fault is added or removed
    (`logik`/`hardware` agree), every downstream observation agrees
    (contracts at their place read the same values from the same
    environments, call logs gain no event, no shared access is added or
    removed for concurrency -- both sides read `orte = []`), and the
    step-budget accounting is unchanged (same block shape, the removed
    computation is pure and unbudgeted);
    (3) the folded value reads back whole through the canonical word.
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard (`div`/`rem` keep `M102`).
    The checker's range at the site (`weiter`/`narrow`) is untouched by the
    fold and still enforced there -- never weakened, never re-derived. -/

/-- CONNECTION: folding `x + y` under a bind preserves value, outcome
    and the width-exact word image. -/
theorem OptFoldConst_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x y : Int)
    (rest : Endblock D V l ((.int (x + y) (x + y)) :: Γ) Λ)
    (hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.lit (x + y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
      = (eval σ₀ (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.lit (x + y) : Expr D Γ Λ (.int (x + y) (x + y))) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y))) rest) σ ρ
    ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat := by
  exact ⟨rfl, rfl, foldWort_add x y hW⟩

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptFoldConst_verbindung` instantiated JOINTLY:
    `3 + 4` folds to `7` under a `bind` with a `leave` continuation, in the
    NON-DEGENERATE reference program `refD` (whose `einzahlen` writes its
    table, `refEin_schreibt`), beside the reached F-machine run `MB` that
    changes memory (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`).
    Both conjunct groups are used. -/

/-- JOINT WITNESS for `OptFoldConst_verbindung`: `3 + 4` folds to `7`
    on `refD`, beside the memory-changing reached run. -/
theorem OptFoldConst_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x y : Int)
      (rest : Endblock refD V l ((.int (x + y) (x + y)) :: Γ) Λ)
      (_hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (.lit (x + y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
        = (eval σ₀ (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (.lit (x + y) : Expr refD Γ Λ (.int (x + y) (x + y))) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y))) rest) σ ρ
      ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptFoldConst_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (x := 3) (y := 4) (rest := Endblock.leave rfl) (hW := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, 3, 4,
    Endblock.leave rfl, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No block-window float rewrite: section 4 proves the admitted float
      fold preserves value and `gleitPasst` outcome at the value level;
      the two-block `gleitLit`/`gleit` window with recomputed avail facts
      (DESIGN certificate "A+B") stays with the lowering lane.
    - No `div`/`rem`/`neg` syntax connection: their VALUES fold
      (section 2); only `add` gets the `Endblock` connection here.
    - No totalCost inequality: the folded window is the same block shape
      with one pure computation removed, so step-budget accounting is
      unchanged; the formal level-(c) machine-work bound is OPEN per
      IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at canonical words and `gleitRechne` values.
-/

#print axioms foldZulassen
#print axioms foldVerweigert_strtod
#print axioms foldVerweigert_mxcsr
#print axioms foldVerweigert_weite
#print axioms foldAdd_wert
#print axioms foldSub_wert
#print axioms foldMul_wert
#print axioms foldNeg_wert
#print axioms foldDiv_wert
#print axioms foldRem_wert
#print axioms foldWort_add
#print axioms probe_foldWort
#print axioms foldGleit_behält
#print axioms probe_foldGleit
#print axioms OptFoldConst_verbindung
#print axioms OptFoldConst_verbindung_zeuge

end Gabbro.Grammatik.X86
