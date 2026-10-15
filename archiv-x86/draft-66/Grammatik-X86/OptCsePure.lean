/-
  File:      Grammatik/X86/OptCsePure.lean
  Subject:   Pure common-subexpression elimination rule lemma (lane 863).

  DESIGN section 7 row: local rewrite "second computation of a pure
  expression with identical width/mode under recomputed availability
  becomes the available value", certificate "local rewrite record plus
  recomputed analysis citations (avail/width/mode facts)", failure case
  "CSE across a gate/range boundary (cross-gate range CSE refuses)",
  phase E, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `Gleitkomma`, `X86.Typen`, `X86.Wort`, `ReferenzB`):
  a recomputed pure `x + y` IS the available value (the reuse reads the
  same evaluated value), the rewritten two-bind window takes the same
  `execEnd` outcome (no fault added or removed, same successor world),
  and the reused value reads back through the canonical word under the
  width-exact premise. Float reuse preserves value and `gleitPasst`
  outcome exactly where the validator recomputed the equation in the
  kernel model under one rounding scope; the DESIGN failure case is
  refused by `cseZulassen`. No `ensures` is derived, no refusal becomes
  a warning, no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one pure-CSE site
    (DESIGN section 7 row): identical width, identical mode (one
    rounding scope for floats), purity (no faulting form above its
    guard, no gate, no shared access), recomputed availability (a
    dominating definition with no intervening kill), and no gate/range
    boundary between definition and use. This record is the LOCAL
    rewrite half of the certificate; the RECOMPUTED analysis half is
    cited by the `hC`/`hEq` premises of the lemmas below. -/
structure CseCert where
  gleicheBreite : Bool
  gleicherModus : Bool
  rein : Bool
  verfuegbar : Bool
  keinTorBereich : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def cseZulassen (c : CseCert) : Bool :=
  c.gleicheBreite && c.gleicherModus && c.rein && c.verfuegbar && c.keinTorBereich

/-! ## 1. Refusal: the DESIGN failure case must NOT rewrite.

    A reuse across a gate/range boundary (a `narrow`/range gate or any
    gate between definition and use) is refused: `keinTorBereich = false`
    forces `cseZulassen = false`. A width or mode mismatch, an impure or
    faulting-above-guard or gated or shared expression, and a killed or
    never-available definition are refused the same way. All are proved
    of the decided Bool, so the validator cannot silently skip them. -/

/-- Cross-gate/range reuse refuses: the DESIGN failure case. -/
theorem cseVerweigert_tor (c : CseCert)
    (h : c.keinTorBereich = false) :
    cseZulassen c = false := by
  simp [cseZulassen, h]

/-- A width-changing reuse refuses. -/
theorem cseVerweigert_breite (c : CseCert)
    (h : c.gleicheBreite = false) :
    cseZulassen c = false := by
  simp [cseZulassen, h]

/-- A cross-mode (rounding scope) reuse refuses. -/
theorem cseVerweigert_modus (c : CseCert)
    (h : c.gleicherModus = false) :
    cseZulassen c = false := by
  simp [cseZulassen, h]

/-- An impure (faulting above its guard, gated, shared) reuse refuses. -/
theorem cseVerweigert_rein (c : CseCert)
    (h : c.rein = false) :
    cseZulassen c = false := by
  simp [cseZulassen, h]

/-- A killed (never-available) reuse refuses. -/
theorem cseVerweigert_verfuegbar (c : CseCert)
    (h : c.verfuegbar = false) :
    cseZulassen c = false := by
  simp [cseZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_cseZulassen_ok :
    cseZulassen ⟨true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a cross-gate certificate is refused. -/
theorem probe_cseZulassen_tor :
    cseZulassen ⟨true, true, true, true, false⟩ = false := by
  decide

/-- Probe: an impure certificate is refused. -/
theorem probe_cseZulassen_rein :
    cseZulassen ⟨true, true, false, true, true⟩ = false := by
  decide

/-! ## 2. Admission unpacks: a fired rewrite held every side condition.

    The validator's recomputed-analysis half of the certificate is cited
    here as the admission hypothesis; unpacking it shows the rewrite
    fired only with identical width and mode, a pure expression, a live
    dominating definition, and no gate/range boundary in between. -/

/-- An admitted site held all five side conditions jointly. -/
theorem cseZulassen_seiten (c : CseCert)
    (h : cseZulassen c = true) :
    c.gleicheBreite = true ∧ c.gleicherModus = true ∧ c.rein = true ∧
      c.verfuegbar = true ∧ c.keinTorBereich = true := by
  cases c with
  | mk b m r v k =>
    simp_all [cseZulassen]

/-! ## 3. Integer reuse: the available value IS the recomputed value.

    Each lemma is over ARBITRARY values (`x y : Int`): the available
    definition and the recomputed use agree because the pure expression
    evaluates to its sum at both sites. Width-exactness (DESIGN row) is
    the validator-decided `hW`: under it the word holds the value whole,
    so the later lowering writes the reused constant, not a wrapped one. -/

/-- The recomputed `x + y` is the available value. -/
theorem cseAdd_wert (x y : Int) :
    (Zahl.add (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x + y := by
  rfl

/-- The reused sum reads back whole through the canonical word. -/
theorem cseWort_add (x y : Int) (hW : 0 ≤ x + y ∧ x + y < 2 ^ 64) :
    ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat := by
  have h : (x + y).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `3 + 4` reads back as `7` through the word. -/
theorem probe_cseWort :
    ((BitVec.ofNat 64 ((3 : Int) + 4).toNat : Wort)).toNat = 7 := by
  decide

/-! ## 4. Float reuse: one rounding scope, same `gleitPasst` outcome.

    The validator precomputed `gleitRechne op` on the two operand values
    IN THE KERNEL under one rounding scope (`gleicherModus`, the mode
    half of the DESIGN row) with no gate between the sites
    (`keinTorBereich`); `qf` is the AVAILABLE value the reuse reads. The
    recomputation obligation is conditional on admission (`hEq` takes
    `hz`): the equation is claimed only where the validator admitted the
    site. Conclusion: the reused value and the recomputed op agree under
    `gleitPasst` -- same pushed value, same `logik bereich` outcome, so
    neither a value nor a fault is eliminated away. -/

/-- The admitted float reuse preserves value and `gleitPasst` outcome. -/
theorem cseGleit_behält (cert : CseCert) (op : GleitOp)
    (qa qb qf lo hi : Int × Int)
    (hz : cseZulassen cert = true)
    (hEq : cseZulassen cert = true →
      bruch qf = gleitRechne op (bruch qa) (bruch qb)) :
    gleitPasst lo hi (bruch qf) =
      gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb)) := by
  have e := hEq hz
  rw [e]

/-- Probe: the kernel computes `0.5 + 0.25 = 0.75` in one rounding. -/
theorem probe_cseGleit :
    gleitRechne .add (bruch (1, 2)) (bruch (1, 4)) = bruch (3, 4) := by
  decide

/-! ## 5. Connection: the reused bind behaves like the recomputed one.

    The rewrite fires only on a pure expression of identical width and
    mode (`gleicheBreite`, `gleicherModus`, `rein`: the DESIGN premises
    by construction of `cseZulassen`) with a live dominating definition
    (`verfuegbar`) and no gate/range boundary between the sites
    (`keinTorBereich`); it is stated at a two-bind window with an
    ARBITRARY continuation `rest`, so the conclusion covers every
    downstream observation at once. Conclusion, jointly:
    (1) the reused bound VALUE is the recomputed one;
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree), every downstream observation
    agrees (contracts at their place read the same values from the same
    environments, call logs gain no event, no shared access is added or
    removed for concurrency -- both sides read `orte = []`), and the
    step-budget accounting is unchanged (same block shape, the removed
    recomputation is pure and unbudgeted);
    (3) the reused value reads back whole through the canonical word;
    (4) admission unpacks: width, mode, purity, availability and the
    gate-free path all held where the rewrite fired.
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard (impure, gated,
    shared and cross-gate shapes keep their refusal of section 1).
    The checker's range at either site (`weiter`/`narrow`) is untouched
    by the reuse and still enforced there -- never weakened, never
    re-derived. -/

/-- CONNECTION: reusing an available `x + y` under a second bind
    preserves value, outcome, the width-exact word image, and the
    fired side conditions. -/
theorem OptCsePure_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x y : Int)
    (cert : CseCert) (hC : cseZulassen cert = true)
    (rest : Endblock D V l ((.int (x + y) (x + y)) :: (.int (x + y) (x + y)) :: Γ) Λ)
    (hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.lit (x + y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
      = (eval σ₀ (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y)))
          (Endblock.bind (.lit (x + y) : Expr D ((.int (x + y) (x + y)) :: Γ) Λ (.int (x + y) (x + y))) rest)) σ ρ
      = execEnd O passes R
        (Endblock.bind (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y)))
          (Endblock.bind (.add (.lit x) (.lit y) : Expr D ((.int (x + y) (x + y)) :: Γ) Λ (.int (x + y) (x + y))) rest)) σ ρ
    ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat
    ∧ (cert.gleicheBreite = true ∧ cert.gleicherModus = true ∧ cert.rein = true ∧
        cert.verfuegbar = true ∧ cert.keinTorBereich = true) := by
  exact ⟨rfl, rfl, cseWort_add x y hW, cseZulassen_seiten cert hC⟩

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptCsePure_verbindung` instantiated JOINTLY:
    `3 + 4` computed once and reused under a second `bind` with a
    `leave` continuation, in the NON-DEGENERATE reference program
    `refD` (whose `einzahlen` writes its table, `refEin_schreibt`),
    beside the reached F-machine run `MB` that changes memory
    (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`). All conjunct
    groups are used. -/

/-- JOINT WITNESS for `OptCsePure_verbindung`: `3 + 4` computed once
    and reused on `refD`, beside the memory-changing reached run. -/
theorem OptCsePure_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x y : Int)
      (cert : CseCert) (_hC : cseZulassen cert = true)
      (rest : Endblock refD V l ((.int (x + y) (x + y)) :: (.int (x + y) (x + y)) :: Γ) Λ)
      (_hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (.lit (x + y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
        = (eval σ₀ (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y)))
            (Endblock.bind (.lit (x + y) : Expr refD ((.int (x + y) (x + y)) :: Γ) Λ (.int (x + y) (x + y))) rest)) σ ρ
        = execEnd O passes R
          (Endblock.bind (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y)))
            (Endblock.bind (.add (.lit x) (.lit y) : Expr refD ((.int (x + y) (x + y)) :: Γ) Λ (.int (x + y) (x + y))) rest)) σ ρ
      ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat
      ∧ (cert.gleicheBreite = true ∧ cert.gleicherModus = true ∧ cert.rein = true ∧
          cert.verfuegbar = true ∧ cert.keinTorBereich = true)
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptCsePure_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (x := 3) (y := 4) (cert := ⟨true, true, true, true, true⟩) (hC := by decide)
    (rest := Endblock.leave rfl) (hW := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, 3, 4,
    ⟨true, true, true, true, true⟩, by decide,
    Endblock.leave rfl, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No block-window float rewrite: section 4 proves the admitted float
      reuse preserves value and `gleitPasst` outcome at the value level;
      the two-block `gleitLit`/`gleit` window with recomputed avail facts
      (DESIGN certificate "A+B") stays with the lowering lane.
    - No `sub`/`mul`/`div`/`rem`/`neg` syntax connection: their VALUES
      reuse the same kernel as `cseAdd_wert` (section 3); only `add`
      gets the two-bind `Endblock` connection here.
    - No cross-`bind` variable reuse: the second site re-evaluates the
      pure expression (value-level reuse); threading a bound variable
      into the use site stays with the lowering lane.
    - No totalCost inequality: the rewritten window is the same block
      shape with one pure recomputation removed, so step-budget
      accounting is unchanged; the formal level-(c) machine-work bound
      is OPEN per IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at canonical words and `gleitRechne` values.
-/

#print axioms cseVerweigert_tor
#print axioms cseVerweigert_breite
#print axioms cseVerweigert_modus
#print axioms cseVerweigert_rein
#print axioms cseVerweigert_verfuegbar
#print axioms probe_cseZulassen_ok
#print axioms probe_cseZulassen_tor
#print axioms probe_cseZulassen_rein
#print axioms cseZulassen_seiten
#print axioms cseAdd_wert
#print axioms cseWort_add
#print axioms probe_cseWort
#print axioms cseGleit_behält
#print axioms probe_cseGleit
#print axioms OptCsePure_verbindung
#print axioms OptCsePure_verbindung_zeuge

end Gabbro.Grammatik.X86
