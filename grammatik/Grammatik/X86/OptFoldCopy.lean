/-
  File:      Grammatik/X86/OptFoldCopy.lean
  Subject:   Copy propagation rule lemma (lane 861).

  DESIGN section 7 row: local premise "copy `y = x` reaches the use:
  recomputed avail, definition dominates the use, width preserved",
  certificate "local rewrite record plus recomputed analysis citations",
  failure case "redefinition of `x` or `y` between definition and use".

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `Gleitkomma`, `ReferenzB`): a use of `y` reads
  the same value as a use of `x` where the validator admitted the site,
  the `bind` window admits the same `execEnd` outcome on both sides (no
  fault added or removed, same successor worlds), both sides read no
  carrier (`orte = []`), and a float copy keeps the same `gleitPasst`
  outcome with no recomputation (no rounding scope is crossed). The
  redefinition case refuses by `copyZulassen`. No `ensures` is derived,
  no refusal becomes a warning, no faulting form is speculated above
  its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one copy-propagation site
    (DESIGN section 7 row): the validator RECOMPUTED availability (`x`
    holds the copied value at the use), the definition DOMINATES the use,
    the width is preserved (both ends share the type), and NO
    redefinition of `x` or `y` stands between definition and use. -/
structure CopyCert where
  verfuegbar : Bool
  dominiert : Bool
  breiteOk : Bool
  keineNeudef : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def copyZulassen (c : CopyCert) : Bool :=
  c.verfuegbar && c.dominiert && c.breiteOk && c.keineNeudef

/-! ## 1. Refusal: a redefinition between definition and use must NOT propagate.

    The DESIGN failure case: `x` or `y` is redefined between the copy
    definition and the use. `keineNeudef = false` forces
    `copyZulassen = false`. The same holds for the other three
    citations (unavailable, non-dominating, width-changing): each is
    proved of the decided Bool, so the validator cannot silently skip
    any of them. -/

/-- A redefinition between definition and use refuses the copy. -/
theorem copyVerweigert_neudef (c : CopyCert)
    (h : c.keineNeudef = false) :
    copyZulassen c = false := by
  simp [copyZulassen, h]

/-- A non-dominating definition refuses the copy. -/
theorem copyVerweigert_dominanz (c : CopyCert)
    (h : c.dominiert = false) :
    copyZulassen c = false := by
  simp [copyZulassen, h]

/-- An unavailable source refuses the copy. -/
theorem copyVerweigert_verfuegbar (c : CopyCert)
    (h : c.verfuegbar = false) :
    copyZulassen c = false := by
  simp [copyZulassen, h]

/-- A width-changing copy refuses. -/
theorem copyVerweigert_weite (c : CopyCert)
    (h : c.breiteOk = false) :
    copyZulassen c = false := by
  simp [copyZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_copyZulassen_ok :
    copyZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: a redefined certificate is refused. -/
theorem probe_copyZulassen_neudef :
    copyZulassen ⟨true, true, true, false⟩ = false := by
  decide

/-- Probe: a non-dominating certificate is refused. -/
theorem probe_copyZulassen_dominanz :
    copyZulassen ⟨true, false, true, true⟩ = false := by
  decide

/-! ## 2. Value: the admitted copy reads the same value.

    Over ARBITRARY values at an ARBITRARY type `τ`: the recomputation
    obligation is conditional on admission (`hEq` takes `hz`), exactly
    like the admitted float fold of the const-fold lane -- the equation
    is claimed only where the validator admitted the site. Width is
    preserved by construction: both ends are `Var Γ τ` at the SAME
    type, so no `narrow`, no wrap and no width change can hide in the
    rewrite (the validator re-decides it as `breiteOk`). -/

/-- The admitted copy preserves the evaluated value, at any type. -/
theorem copyVar_wert {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (x y : Var Γ τ)
    (cert : CopyCert)
    (hz : copyZulassen cert = true)
    (ρ : Env D Γ)
    (hEq : copyZulassen cert = true → ρ.get y = ρ.get x)
    (σ₀ σ : World D) :
    eval σ₀ (.var y : Expr D Γ Λ τ) σ ρ =
      eval σ₀ (.var x : Expr D Γ Λ τ) σ ρ := by
  show ρ.get y = ρ.get x
  exact hEq hz

/-- Probe: two reads of one environment slot agree. -/
theorem probe_copyVar_wert :
    let ρ : Env refD [.int 0 10] :=
      Env.cons (⟨7, by decide, by decide⟩ : Wert refD (.int 0 10)) Env.nil
    ρ.get Var.hier = ρ.get Var.hier := by
  rfl

/-! ## 3. Observations and floats: no carrier read, no rounding crossed.

    A variable read observes NO carrier (`orte = []` on both sides), so
    the rewrite adds and removes no shared access for concurrency, no
    call-log event and no contract-visible read. A float copy is the
    SAME value (no recomputation, unlike a fold): the `gleitPasst`
    outcome agrees bit-identically, and no rounding scope is crossed. -/

/-- Both sides read no carrier: the footprint is empty on both sides. -/
theorem copyVar_orte {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (x y : Var Γ τ) :
    (.var y : Expr D Γ Λ τ).orte = (.var x : Expr D Γ Λ τ).orte := by
  rfl

/-- The float copy keeps the same `gleitPasst` outcome: the value is
    bit-identical, nothing is recomputed, no MXCSR scope is crossed. -/
theorem copyGleit_passt {D : Deklaration} {lo hi : Int × Int}
    (v w : Wert D (.fl lo hi)) (h : v = w) :
    gleitPasst lo hi v.x = gleitPasst lo hi w.x := by
  rw [h]

/-! ## 4. Connection: the propagated bind behaves like the original.

    The rewrite fires only where the validator admitted the site
    (`cert`, `hz`, `hEq`: recomputed avail, dominance, width, no
    redefinition). It is stated at an `Endblock.bind` window with an
    ARBITRARY continuation `rest`, so the conclusion covers every
    downstream observation at once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved;
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree), every downstream observation
    agrees (contracts at their place read the same values from the
    same environments, call logs gain no event, no shared access is
    added or removed for concurrency -- both sides read `orte = []`),
    and the step-budget accounting is unchanged (same block shape, a
    variable read is pure and unbudgeted on both sides);
    (3) both sides read no carrier (`orte` equal).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard (redefinition
    refuses by section 1). The checker's range at the site is
    untouched by the copy and still enforced there. -/

/-- CONNECTION: propagating `x` for `y` under a bind preserves value,
    outcome and the empty footprint. -/
theorem OptFoldCopy_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool} {τ : Ty}
    (x y : Var Γ τ)
    (cert : CopyCert)
    (hz : copyZulassen cert = true)
    (ρ : Env D Γ)
    (hEq : copyZulassen cert = true → ρ.get y = ρ.get x)
    (rest : Endblock D V l (τ :: Γ) Λ)
    (σ₀ σ : World D) :
    (eval σ₀ (.var y : Expr D Γ Λ τ) σ ρ =
      eval σ₀ (.var x : Expr D Γ Λ τ) σ ρ)
    ∧ execEnd O passes R
        (Endblock.bind (.var y : Expr D Γ Λ τ) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.var x : Expr D Γ Λ τ) rest) σ ρ
    ∧ ((.var y : Expr D Γ Λ τ).orte =
      (.var x : Expr D Γ Λ τ).orte) := by
  have he := copyVar_wert (Λ := Λ) x y cert hz ρ hEq (σ.lese Λ []) (σ.lese Λ [])
  refine ⟨copyVar_wert (Λ := Λ) x y cert hz ρ hEq σ₀ σ, ?_, copyVar_orte x y⟩
  show (execEnd O passes R rest (σ.lese Λ [])
      (.cons (eval (σ.lese Λ []) (.var y : Expr D Γ Λ τ) (σ.lese Λ []) ρ) ρ)).schrumpf =
    (execEnd O passes R rest (σ.lese Λ [])
      (.cons (eval (σ.lese Λ []) (.var x : Expr D Γ Λ τ) (σ.lese Λ []) ρ) ρ)).schrumpf
  rw [he]

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptFoldCopy_verbindung` instantiated JOINTLY: two
    context slots holding the same value `7` (the admitted avail fact
    `hEq` by `rfl`), the copy `y := x` propagated under a `bind` with a
    `leave` continuation, in the NON-DEGENERATE reference program
    `refD` (whose `einzahlen` writes its table, `refEin_schreibt`),
    beside the reached F-machine run `MB` that changes memory
    (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`). All three
    conjunct groups are used. -/

/-- JOINT WITNESS for `OptFoldCopy_verbindung`: the copy of slot `7`
    propagates on `refD`, beside the memory-changing reached run. -/
theorem OptFoldCopy_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool) (τ : Ty)
      (x y : Var Γ τ)
      (cert : CopyCert)
      (_hz : copyZulassen cert = true)
      (ρ : Env refD Γ)
      (_hEq : copyZulassen cert = true → ρ.get y = ρ.get x)
      (rest : Endblock refD V l (τ :: Γ) Λ)
      (σ₀ σ : World refD),
      (eval σ₀ (.var y : Expr refD Γ Λ τ) σ ρ =
        eval σ₀ (.var x : Expr refD Γ Λ τ) σ ρ)
      ∧ execEnd O passes R
          (Endblock.bind (.var y : Expr refD Γ Λ τ) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.var x : Expr refD Γ Λ τ) rest) σ ρ
      ∧ ((.var y : Expr refD Γ Λ τ).orte =
        (.var x : Expr refD Γ Λ τ).orte)
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptFoldCopy_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf)
    (Γ := [.int 0 10, .int 0 10]) (Λ := []) (l := true) (τ := .int 0 10)
    (x := Var.hier) (y := Var.dort Var.hier)
    (cert := ⟨true, true, true, true⟩) (hz := by decide)
    (ρ := Env.cons (⟨7, by decide, by decide⟩ : Wert refD (.int 0 10))
      (Env.cons (⟨7, by decide, by decide⟩ : Wert refD (.int 0 10)) Env.nil))
    (hEq := fun _ => rfl)
    (rest := Endblock.leave rfl)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt [])
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf,
    [.int 0 10, .int 0 10], [], true, .int 0 10,
    Var.hier, Var.dort Var.hier,
    ⟨true, true, true, true⟩, by decide,
    Env.cons (⟨7, by decide, by decide⟩ : Wert refD (.int 0 10))
      (Env.cons (⟨7, by decide, by decide⟩ : Wert refD (.int 0 10)) Env.nil),
    fun _ => rfl,
    Endblock.leave rfl,
    refSp0.welt [], refSp0.welt [],
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No lowering to target blocks: the `bind` window stays at the
      source level; the checked machine-block/byte production and its
      per-access bridge belong to the lowering lanes.
    - No totalCost inequality: both sides share one block shape with a
      pure unbudgeted read, so step-budget accounting is unchanged; the
      formal level-(c) machine-work bound is OPEN per IR-VALIDIERUNG.
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at equal `eval` values and `gleitPasst`
      outcomes over canonical types.
    - No interprocedural avail: the validator recomputes `hEq` per use;
      the dominance and no-redefinition citations are carried Bools,
      refused when false, never trusted from an untrusted analysis.
-/

#print axioms copyZulassen
#print axioms copyVerweigert_neudef
#print axioms copyVerweigert_dominanz
#print axioms copyVerweigert_verfuegbar
#print axioms copyVerweigert_weite
#print axioms copyVar_wert
#print axioms copyVar_orte
#print axioms copyGleit_passt
#print axioms OptFoldCopy_verbindung
#print axioms OptFoldCopy_verbindung_zeuge

end Gabbro.Grammatik.X86
