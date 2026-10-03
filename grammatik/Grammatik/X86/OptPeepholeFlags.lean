/-
  File:      Grammatik/X86/OptPeepholeFlags.lean
  Subject:   Flag-aware peephole rule lemma (lane 876).

  DESIGN section 7 row: local premise "same-value `sub` site, flags dead
  (recomputed liveness), integer site, no FMA fusion shape", certificate
  "local rewrite record + recomputed analysis citations", failure cases
  "flags live below the site; float self-subtraction (NaN/Inf: `x - x`
  is not zero); FMA fusion (single rounding differs from two)".
  Phase E, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `Gleitkomma`, `X86.Typen`, `X86.Wort`,
  `ReferenzB`): the cert-gated rewrite `sub (.lit x) (.lit x)` to
  `.lit (x - x)` preserves the evaluated value, takes the same
  `execEnd` outcome (no fault added or removed, same successor worlds
  and environments), and reads back whole through the canonical word.
  The dropped flag write is valid exactly where the validator
  recomputed dead flags (`flagTot`); a live-flag site refuses. Float
  self-subtraction refuses (`ganzzahlig`): NaN minus NaN is NaN, not
  zero. Any fused mul-add shape refuses (`keinFMA`): one rounding is
  not two. No `ensures` is derived, no refusal becomes a warning, no
  faulting form is speculated above its guard (`sub` on integers is
  total; the float and FMA shapes keep their refusal).
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.Gleitkomma
import Grammatik.KostenG
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one flag-peephole site
    (DESIGN section 7 row): no flag is live below the site
    (recomputed liveness citation), the site is integer-typed (float
    self-subtraction is not zero), and the site is no fused mul-add
    shape (one rounding is not two). -/
structure FlagPeepholeCert where
  flagTot : Bool
  ganzzahlig : Bool
  keinFMA : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to the certified translation (identity),
    never to a warning. -/
def peepholeZulassen (c : FlagPeepholeCert) : Bool :=
  c.flagTot && c.ganzzahlig && c.keinFMA

/-! ## 1. Refusals: the three DESIGN failure cases must NOT fire.

    A site with a live flag below it is refused: the rewrite drops
    the flag write of `sub`, so a live reader would observe a
    different machine. A float site is refused: `x - x` is not zero
    for NaN or infinities (pinned in section 3). A fused mul-add
    shape is refused: one rounding is not two roundings. All three
    are proved of the decided Bool, so the validator cannot silently
    skip them. -/

/-- A live flag below the site refuses the rewrite. -/
theorem peepholeVerweigert_lebenig (c : FlagPeepholeCert)
    (h : c.flagTot = false) :
    peepholeZulassen c = false := by
  simp [peepholeZulassen, h]

/-- A float site refuses the rewrite. -/
theorem peepholeVerweigert_float (c : FlagPeepholeCert)
    (h : c.ganzzahlig = false) :
    peepholeZulassen c = false := by
  simp [peepholeZulassen, h]

/-- A fused mul-add shape refuses the rewrite. -/
theorem peepholeVerweigert_fma (c : FlagPeepholeCert)
    (h : c.keinFMA = false) :
    peepholeZulassen c = false := by
  simp [peepholeZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_peepholeZulassen_ok :
    peepholeZulassen ⟨true, true, true⟩ = true := by
  decide

/-- Probe: a live-flag certificate is refused. -/
theorem probe_peepholeZulassen_lebenig :
    peepholeZulassen ⟨false, true, true⟩ = false := by
  decide

/-- Probe: a float certificate is refused. -/
theorem probe_peepholeZulassen_float :
    peepholeZulassen ⟨true, false, true⟩ = false := by
  decide

/-- Probe: a fused-shape certificate is refused. -/
theorem probe_peepholeZulassen_fma :
    peepholeZulassen ⟨true, true, false⟩ = false := by
  decide

/-! ## 2. Integer self-subtraction: the value IS zero.

    Each lemma is over an ARBITRARY value (`x : Int`): the "same-value
    `sub` site" premise is carried by the syntax rewrite of section 4,
    which fires only on `.sub (.lit x) (.lit x)`. Integer `sub` is
    total, so no fault is added or removed: there is no divisor, no
    guard to forward. -/

/-- `x - x` evaluates to `x - x`: the value is preserved. -/
theorem subSelbst_wert (x : Int) :
    (Zahl.sub (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)).n = x - x := by
  rfl

/-- `x - x` is zero. -/
theorem subSelbst_null (x : Int) : x - x = 0 := by
  omega

/-- Probe: `5 - 5` is `0`. -/
theorem probe_subSelbst : (5 : Int) - 5 = 0 := by
  decide

/-! ## 3. Width-exactness and the IEEE refusal ground.

    "Width exact" (DESIGN row) is the validator-decided `hW`: the
    folded `x - x` fits the 64-bit canonical word. Under `hW` the word
    holds the value whole -- no truncation, no wrap -- so the later
    lowering writes the folded constant, not a wrapped one.

    The IEEE ground for the float refusal of section 1: quiet NaN
    minus quiet NaN is quiet NaN in the kernel model
    (`Gleitkomma.sub` propagates NaN through `add`), and quiet NaN is
    not the zero word. Hence no float self-subtraction folds to zero. -/

/-- The folded `x - x` reads back whole through the canonical word. -/
theorem subSelbst_wort (x : Int) (hW : 0 ≤ x - x ∧ x - x < 2 ^ 64) :
    ((BitVec.ofNat 64 (x - x).toNat : Wort)).toNat = (x - x).toNat := by
  have hlo := hW.1
  have hhi := hW.2
  have h : (x - x).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `5 - 5` reads back as `0` through the word. -/
theorem probe_subSelbst_wort :
    ((BitVec.ofNat 64 ((5 : Int) - 5).toNat : Wort)).toNat = 0 := by
  decide

/-- IEEE PIN: quiet NaN minus quiet NaN is quiet NaN, not zero, so a
    float self-subtraction must never fold to zero. -/
theorem subSelbst_float_kein_null :
    Gleitkomma.sub Gleitkomma.f64 (Gleitkomma.nanQ Gleitkomma.f64)
      (Gleitkomma.nanQ Gleitkomma.f64) ≠ ⟨false, 0, 0⟩ := by
  decide

/-! ## 4. The cert-gated site rewrite: the exact certificate shape.

    The certificate is the local rewrite record (this function: the
    site shape `.sub (.lit x) (.lit x)` and its literal result) plus
    the recomputed analysis citations (the three `FlagPeepholeCert`
    fields of section 1, re-decided by the validator from the
    program: liveness, integer typing, fusion shape). Where admitted,
    the site becomes the literal; where refused, the site is left
    alone -- the certified translation, never a warning. -/

/-- Cert-gated site rewrite: `sub (.lit x) (.lit x)` becomes the
    literal where admitted, otherwise the site is left alone. Both
    sides share `.int (x - x) (x - x)`. -/
def subSelbstUmschreiben {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (cert : FlagPeepholeCert) (x : Int) :
    Expr D Γ Λ (.int (x - x) (x - x)) :=
  if peepholeZulassen cert then .lit (x - x) else .sub (.lit x) (.lit x)

/-- A refused site is the identity: the certified translation stands. -/
theorem umschreibenVerweigert_identitaet {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (cert : FlagPeepholeCert) (x : Int)
    (hz : peepholeZulassen cert = false) :
    subSelbstUmschreiben (D := D) (Γ := Γ) (Λ := Λ) cert x
      = (.sub (.lit x) (.lit x) :
        Expr D Γ Λ (.int (x - x) (x - x))) := by
  simp [subSelbstUmschreiben, hz]

/-! ## 5. Observation and budget pins.

    Both literal-operand sides read nothing: the removed computation
    performed no carrier or global read, so the rewrite adds no shared
    access and removes none that could race -- concurrency
    observations are unchanged. The rewritten literal costs no more
    than the removed `sub`: the step-budget accounting is unchanged
    (the removed computation is pure and unbudgeted). -/

/-- The original site reads nothing: literal operands. -/
theorem subSelbst_orte_original {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (x : Int) :
    ((.sub (.lit x) (.lit x) : Expr D Γ Λ (.int (x - x) (x - x)))).orte
      = [] := by
  rfl

/-- The rewritten literal reads nothing. -/
theorem subSelbst_orte_neu {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (x : Int) :
    ((.lit (x - x) : Expr D Γ Λ (.int (x - x) (x - x)))).orte = [] := by
  rfl

/-- The rewritten literal costs no more than the removed `sub`. -/
theorem subSelbst_kosten {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (x : Int) :
    kostenExpr (.lit (x - x) : Expr D Γ Λ (.int (x - x) (x - x)))
      ≤ kostenExpr (.sub (.lit x) (.lit x) :
        Expr D Γ Λ (.int (x - x) (x - x))) := by
  simp [kostenExpr]

/-! ## 6. Connection: the admitted rewrite behaves like the site.

    The rewrite fires only on `.sub (.lit x) (.lit x)` (the DESIGN
    "same-value operands" premise by construction) with a width-exact
    result (`hW`, section 3); it is stated at an `Endblock.bind`
    window with an ARBITRARY continuation `rest`, so the conclusion
    covers every downstream observation at once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved;
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree; integer `sub` is total),
    every downstream observation agrees (contracts at their place
    read the same values from the same environments, call logs gain
    no event since the world is untouched, no shared access is added
    or removed for concurrency -- both sides read `orte = []`,
    section 5), and the step-budget accounting is unchanged (same
    block shape, the removed computation is pure and unbudgeted,
    section 5);
    (3) the value IS zero (`x - x = 0`: the peephole result);
    (4) the folded value reads back whole through the canonical word.
    The admission `hz` fires the gate: without it the rewrite is the
    identity (section 4) and there is nothing to connect. Nothing
    here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard (float and FMA shapes
    keep their section 1 refusals). The checker's range at the site
    (`weiter`/`narrow`) is untouched by the rewrite and still
    enforced there -- never weakened, never re-derived. -/

/-- CONNECTION: the admitted `x - x` to literal rewrite preserves
    value, outcome, zero and the width-exact word image. -/
theorem OptPeepholeFlags_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x : Int)
    (rest : Endblock D V l ((.int (x - x) (x - x)) :: Γ) Λ)
    (cert : FlagPeepholeCert)
    (hz : peepholeZulassen cert = true)
    (hW : 0 ≤ x - x ∧ x - x < 2 ^ 64)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (subSelbstUmschreiben (D := D) (Γ := Γ) (Λ := Λ) cert x)
        σ ρ).n
      = (eval σ₀ (.sub (.lit x) (.lit x) :
          Expr D Γ Λ (.int (x - x) (x - x))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (subSelbstUmschreiben (D := D) (Γ := Γ) (Λ := Λ)
          cert x) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.sub (.lit x) (.lit x) :
          Expr D Γ Λ (.int (x - x) (x - x))) rest) σ ρ
    ∧ x - x = 0
    ∧ ((BitVec.ofNat 64 (x - x).toNat : Wort)).toNat
        = (x - x).toNat := by
  have hfire : subSelbstUmschreiben (D := D) (Γ := Γ) (Λ := Λ) cert x
      = (.lit (x - x) : Expr D Γ Λ (.int (x - x) (x - x))) := by
    simp [subSelbstUmschreiben, hz]
  refine ⟨?_, ?_, by omega, subSelbst_wort x hW⟩
  · simp only [hfire]
    rfl
  · simp only [hfire]
    rfl

/-! ## 7. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptPeepholeFlags_verbindung` instantiated
    JOINTLY: `5 - 5` folds to `0` under a `bind` with a `leave`
    continuation, with the admitted certificate, in the
    NON-DEGENERATE reference program `refD` (whose `einzahlen` writes
    its table, `refEin_schreibt`), beside the reached F-machine run
    `MB` that changes memory (`refB_erreicht`, `refB_schreibt`:
    slot `0 -> 100`). All conjunct groups are used. -/

/-- JOINT WITNESS for `OptPeepholeFlags_verbindung`: `5 - 5` folds to
    `0` on `refD`, beside the memory-changing reached run. -/
theorem OptPeepholeFlags_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x : Int)
      (rest : Endblock refD V l ((.int (x - x) (x - x)) :: Γ) Λ)
      (cert : FlagPeepholeCert)
      (_hz : peepholeZulassen cert = true)
      (_hW : 0 ≤ x - x ∧ x - x < 2 ^ 64)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (subSelbstUmschreiben (D := refD) (Γ := Γ) (Λ := Λ)
          cert x) σ ρ).n
        = (eval σ₀ (.sub (.lit x) (.lit x) :
            Expr refD Γ Λ (.int (x - x) (x - x))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (subSelbstUmschreiben (D := refD) (Γ := Γ)
            (Λ := Λ) cert x) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.sub (.lit x) (.lit x) :
            Expr refD Γ Λ (.int (x - x) (x - x))) rest) σ ρ
      ∧ x - x = 0
      ∧ ((BitVec.ofNat 64 (x - x).toNat : Wort)).toNat
          = (x - x).toNat
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptPeepholeFlags_verbindung (D := refD)
    (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (x := 5) (rest := Endblock.leave rfl) (cert := ⟨true, true, true⟩)
    (hz := by decide) (hW := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, 5,
    Endblock.leave rfl, ⟨true, true, true⟩, by decide, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No target-machine liveness fixpoint: `flagTot` is a
      validator-recomputed citation carried as checked data, not a
      result proved here. The dropped flag write (integer `sub`
      lowers to flag-setting `subReg64`, ExpressionLowering) is valid
      exactly under that citation; nothing here computes liveness.
    - No general same-expression `.sub e e` rewrite: with
      memory-reading operands the two sides take different `lese`
      read traces, so raw `execEnd` equality does not hold there.
      Only the literal-operand site is connected here, where both
      sides read nothing (section 5 pins).
    - No float value lemma beyond the refusal: NaN minus NaN is NaN
      (section 3 pin), so float self-subtraction never folds.
    - No fused operation in the model: FMA fusion refusal is a
      certificate-level refusal (section 1); one-rounding versus
      two-rounding equality is not stated and not claimed.
    - No totalCost inequality: the rewritten window is the same block
      shape with one pure computation removed, so step-budget
      accounting is unchanged (section 5 cost pin); the formal
      level-(c) machine-work bound is OPEN.
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader
      claim: correspondence stops at canonical words and kernel-model
      floats.
-/

#print axioms peepholeVerweigert_lebenig
#print axioms peepholeVerweigert_float
#print axioms peepholeVerweigert_fma
#print axioms subSelbst_wert
#print axioms subSelbst_null
#print axioms subSelbst_wort
#print axioms probe_subSelbst_wort
#print axioms subSelbst_float_kein_null
#print axioms umschreibenVerweigert_identitaet
#print axioms subSelbst_orte_original
#print axioms subSelbst_orte_neu
#print axioms subSelbst_kosten
#print axioms OptPeepholeFlags_verbindung
#print axioms OptPeepholeFlags_verbindung_zeuge

end Gabbro.Grammatik.X86
