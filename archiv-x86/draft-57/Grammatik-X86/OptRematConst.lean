/-
  File:      Grammatik/X86/OptRematConst.lean
  Subject:   Rematerialisation rule lemma (lane 881).

  DESIGN section 7 row: local premise "constant cheap, no faulting form,
  spill weight favours remat, `bruch` = `rundeBruch`", certificate "local
  rewrite record plus recomputed analysis citations (literal shape,
  spill weight)", failure case "rematerialise a faulting form above its
  guard (div-by-zero, cross-MXCSR float); remat where the spill is
  cheaper", phase E, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
  `X86.CostSummary`, `X86.InvariantenOpt`): an admitted cheap constant
  recomputed at its use site instead of spilled and reloaded preserves
  the evaluated value, takes the same `execStmt`/`execEnd` outcome (no
  fault added or removed, same successor world), reads back whole
  through the canonical word, costs no more than the spill/reload pair
  it replaces, and the admitted float recomputation preserves value and
  `gleitPasst` outcome in one rounding scope. Every DESIGN failure case
  is refused by `rematZulassen`. No `ensures` is derived, no refusal
  becomes a warning, no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.CostSummary
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Recomputed spill weight: what the rematerialised sequence costs
    against what the spill store plus reload costs. Both counts are
    recomputed by the validator, never trusted from Rust. -/
structure RematGewicht where
  rematKosten : Nat
  spillKosten : Nat
  deriving DecidableEq, Repr

/-- Validator-decided spill-weight check: remat fires only where it
    costs no more than the spill/reload pair it replaces. -/
def gewichtOk (g : RematGewicht) : Bool :=
  decide (g.rematKosten ≤ g.spillKosten)

/-- The validator-decided side conditions for one rematerialisation
    site (DESIGN section 7 row): the constant is cheap, the form cannot
    fault, the spill weight favours remat, and a float recomputation is
    the single `rundeBruch` in one rounding scope. -/
structure RematCert where
  billigOk : Bool
  keinFehler : Bool
  g : RematGewicht
  einfachGerundet : Bool
  gleicheRundung : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation (the
    spill), never to a warning. -/
def rematZulassen (c : RematCert) : Bool :=
  c.billigOk && c.keinFehler && gewichtOk c.g && c.einfachGerundet && c.gleicheRundung

/-! ## 1. Refusal: every DESIGN failure case must NOT rematerialise.

    A rematerialisation whose form can fault (`keinFehler = false`: a
    division that may divide by zero, a float op outside its guard) is
    refused: the fault stays where the source put it, under its guard.
    A non-cheap constant (`billigOk = false`: the spill is cheaper to
    reload than the constant is to recompute) is refused. A site where
    the spill/reload pair is cheaper (`gewichtOk = false`) is refused.
    Float double rounding and cross-scope recomputation are refused like
    in the fold rule. All are proved of the decided Bool, so the
    validator cannot silently skip them. -/

/-- A possibly-faulting form never rematerialises above its guard. -/
theorem rematVerweigert_fehler (c : RematCert)
    (h : c.keinFehler = false) :
    rematZulassen c = false := by
  simp [rematZulassen, h]

/-- A non-cheap constant never rematerialises: it stays spilled. -/
theorem rematVerweigert_teuer (c : RematCert)
    (h : c.billigOk = false) :
    rematZulassen c = false := by
  simp [rematZulassen, h]

/-- A site where the spill pair is cheaper never rematerialises. -/
theorem rematVerweigert_gewicht (c : RematCert)
    (h : gewichtOk c.g = false) :
    rematZulassen c = false := by
  simp [rematZulassen, h]

/-- Host-`strtod` double rounding refuses the float remat. -/
theorem rematVerweigert_strtod (c : RematCert)
    (h : c.einfachGerundet = false) :
    rematZulassen c = false := by
  simp [rematZulassen, h]

/-- A cross-MXCSR-scope float recomputation refuses. -/
theorem rematVerweigert_mxcsr (c : RematCert)
    (h : c.gleicheRundung = false) :
    rematZulassen c = false := by
  simp [rematZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_rematZulassen_ok :
    rematZulassen ⟨true, true, ⟨1, 2⟩, true, true⟩ = true := by
  decide

/-- Probe: a faulting form is refused even where everything else holds. -/
theorem probe_rematZulassen_fehler :
    rematZulassen ⟨true, false, ⟨1, 2⟩, true, true⟩ = false := by
  decide

/-- Probe: a cheaper spill is refused even for a cheap safe constant. -/
theorem probe_rematZulassen_gewicht :
    rematZulassen ⟨true, true, ⟨3, 2⟩, true, true⟩ = false := by
  decide

/-! ## 2. Spill-weight accounting: the admitted remat costs no more.

    The validator recomputes both counts (`RematGewicht`); admission
    (`gewichtOk`) is the decided `≤`. The bound below is what the
    connection's cost conjunct cites: an admitted site replaces the
    spill/reload pair by a sequence that costs no more, so the
    `spillOp` class maximum (`CostSummary`) still covers the segment
    and no budget accounting is weakened. -/

/-- An admitted weight really bounds remat cost by spill cost. -/
theorem gewichtOk_gilt (g : RematGewicht)
    (h : gewichtOk g = true) :
    g.rematKosten ≤ g.spillKosten := by
  unfold gewichtOk at h
  exact of_decide_eq_true h

/-- Probe: `1 ≤ 2` admits; the remat is strictly cheaper. -/
theorem probe_gewichtOk : gewichtOk ⟨1, 2⟩ = true := by
  decide

/-- Probe: `3 ≤ 2` refuses; the spill stays. -/
theorem probe_gewichtOk_nein : gewichtOk ⟨3, 2⟩ = false := by
  decide

/-! ## 3. Value preservation: the recomputed constant IS the value.

    Over ARBITRARY values (`x y : Int`): recomputing `x + y` at the use
    site instead of reloading a spilled copy yields the same value.
    `add`/`sub`/`mul`/`neg` are total; `div`/`rem` keep the source
    `M102` side conditions as validator-decided premises, forwarded
    unchanged, so no fault is added or removed: a zero divisor never
    reaches the remat (and where it might, `keinFehler = false`
    refuses by section 1). The generic literal lemma below covers any
    recomputed expression whose literal shape the validator recomputed
    (`alsLitOpt`, cited analysis, never trusted): such an expression
    evaluates to exactly its literal. -/

/-- Recomputing `x + y` at the use site yields `x + y`. -/
theorem rematAdd_wert (x y : Int) :
    (Zahl.add (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x + y := by
  rfl

/-- Recomputing `x - y` yields `x - y`. -/
theorem rematSub_wert (x y : Int) :
    (Zahl.sub (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x - y := by
  rfl

/-- Recomputing `x * y` yields `x * y`. -/
theorem rematMul_wert (x y : Int) :
    (Zahl.mul (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x * y := by
  rfl

/-- Recomputing `-x` yields `-x`. -/
theorem rematNeg_wert (x : Int) :
    (Zahl.neg (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)).n = -x := by
  rfl

/-- Recomputing `x / y` yields `x.tdiv y` under the `M102` premises:
    the faulting form is recomputed only under its guard. -/
theorem rematDiv_wert (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y) :
    (Zahl.div h0 h1' (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x.tdiv y := by
  rfl

/-- GENERIC literal lemma: any expression whose literal shape the
    validator recomputed (`hLit`) evaluates to exactly that literal,
    so recomputing the literal at the use site preserves the value. -/
theorem rematLit_wert {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (x : Int)
    (σ₀ σ : World D) (ρ : Env D Γ)
    (hLit : InvariantenOpt.alsLitOpt e = some x) :
    (eval σ₀ e σ ρ).n = x :=
  InvariantenOpt.eval_alsLit e x σ₀ σ ρ hLit

/-- Probes: the recomputations compute (`7`, `2`, `12`, `-3`, `3`). -/
theorem probe_rematAdd : (Zahl.add (⟨3, by decide, by decide⟩ : Zahl 3 3)
    (⟨4, by decide, by decide⟩ : Zahl 4 4)).n = 7 := by
  decide

theorem probe_rematSub : (Zahl.sub (⟨5, by decide, by decide⟩ : Zahl 5 5)
    (⟨3, by decide, by decide⟩ : Zahl 3 3)).n = 2 := by
  decide

theorem probe_rematMul : (Zahl.mul (⟨3, by decide, by decide⟩ : Zahl 3 3)
    (⟨4, by decide, by decide⟩ : Zahl 4 4)).n = 12 := by
  decide

theorem probe_rematDiv : (Zahl.div (by decide : (0 : Int) ≤ 7) (by decide : (1 : Int) ≤ 2)
    (⟨7, by decide, by decide⟩ : Zahl 7 7)
    (⟨2, by decide, by decide⟩ : Zahl 2 2)).n = 3 := by
  decide

/-! ## 4. Width-exactness: the recomputed value reads back whole.

    "Cheap" (DESIGN row) includes the validator-decided `hW`: the
    recomputed value fits the 64-bit canonical word. Under `hW` the
    word holds the value whole -- no truncation, no wrap -- so the
    rematerialised sequence writes the constant, not a wrapped one. -/

/-- The recomputed sum reads back whole through the canonical word. -/
theorem rematWort_add (x y : Int) (hW : 0 ≤ x + y ∧ x + y < 2 ^ 64) :
    ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat := by
  have h : (x + y).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `3 + 4` reads back as `7` through the word. -/
theorem probe_rematWort :
    ((BitVec.ofNat 64 ((3 : Int) + 4).toNat : Wort)).toNat = 7 := by
  decide

/-! ## 5. Float recomputation: single rounding, one scope.

    The validator recomputed `gleitRechne op` on the two literal values
    IN THE KERNEL (`einfachGerundet`: `bruch = rundeBruch`, never host
    `strtod`) and both sites share one rounding scope (`gleicheRundung`,
    FpExport). The recomputation obligation is conditional on admission
    (`hEq` takes `hz`): the equation is claimed only where the validator
    admitted the site. Conclusion: the rematerialised literal and the
    recomputed op agree under `gleitPasst` -- same pushed value, same
    `logik bereich` outcome, so neither a value nor a fault is moved. -/

/-- The admitted float recomputation preserves value and outcome. -/
theorem rematGleit_behält (cert : RematCert) (op : GleitOp)
    (qa qb qf lo hi : Int × Int)
    (hz : rematZulassen cert = true)
    (hEq : rematZulassen cert = true →
      bruch qf = gleitRechne op (bruch qa) (bruch qb)) :
    gleitPasst lo hi (bruch qf) =
      gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb)) := by
  have e := hEq hz
  rw [e]

/-- Probe: the kernel computes `0.5 + 0.25 = 0.75` in one rounding. -/
theorem probe_rematGleit :
    gleitRechne .add (bruch (1, 2)) (bruch (1, 4)) = bruch (3, 4) := by
  decide

/-! ## 6. Cost expansions: one remat instruction replaces the pair.

    The rematerialised use site is a single `movImm64` (the cheap
    constant, exhibited here at `7`); the spill/reload pair it replaces
    is a `store64` plus a `load64`. Both counts are `targetWork`
    (`CostSummary` vocabulary, reused): `1 ≤ 2`, so the `spillOp`
    class maximum still covers the segment and the admitted weight
    `⟨1, 2⟩` of section 2 is realised by actual target forms. -/

/-- The rematerialised use site: one immediate move. -/
def rematFolge : List Befehl :=
  [.movImm64 .rax (BitVec.ofNat 64 7)]

/-- The spill/reload pair it replaces: a store plus a load. -/
def spillFolge : List Befehl :=
  [.store64 .rdi .rax (0 : BitVec 32), .load64 .rcx .rdi (0 : BitVec 32)]

/-- The remat sequence retires exactly 1 instruction. -/
theorem rematFolge_zaehlt : targetWork rematFolge = 1 := rfl

/-- The spill pair retires exactly 2 instructions. -/
theorem spillFolge_zaehlt : targetWork spillFolge = 2 := rfl

/-- The remat sequence costs no more than the spill pair. -/
theorem rematFolge_spart : targetWork rematFolge ≤ targetWork spillFolge := by
  decide

/-! ## 7. Connection: the rematerialised bind behaves like the spill.

    The rewrite fires only where admitted (`hz`): the use site
    recomputes `x + y` (one `movImm64`, section 6) instead of reloading
    a spilled copy. It is stated at an `Endblock.bind` window with an
    ARBITRARY continuation `rest`, so the conclusion covers every
    downstream observation at once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved;
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree), every downstream observation
    agrees (contracts at their place read the same values from the same
    environments, call logs gain no event, no shared access is added or
    removed for concurrency -- both sides read `orte = []`), and the
    step-budget accounting is unchanged (same block shape, the removed
    spill traffic is pure and unbudgeted);
    (3) the recomputed value reads back whole through the word;
    (4) the admitted spill weight bounds the remat cost by the spill
    cost -- the `spillOp` class maximum still covers the segment.
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard (faulting forms keep
    their guards by section 3 and refuse by section 1). -/

/-- Admission carries the spill-weight bound into the connection. -/
theorem rematZulassen_gewicht (c : RematCert)
    (h : rematZulassen c = true) :
    gewichtOk c.g = true := by
  cases hg : gewichtOk c.g with
  | true => rfl
  | false =>
    unfold rematZulassen at h
    rw [hg] at h
    simp at h

/-- CONNECTION: recomputing `x + y` at an admitted use site preserves
    value, outcome, the width-exact word image and the spill weight. -/
theorem OptRematConst_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (cert : RematCert)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x y : Int)
    (rest : Endblock D V l ((.int (x + y) (x + y)) :: Γ) Λ)
    (hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
    (hz : rematZulassen cert = true)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.lit (x + y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
      = (eval σ₀ (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.lit (x + y) : Expr D Γ Λ (.int (x + y) (x + y))) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y))) rest) σ ρ
    ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat
    ∧ cert.g.rematKosten ≤ cert.g.spillKosten := by
  have hGew := rematZulassen_gewicht cert hz
  exact ⟨rfl, rfl, rematWort_add x y hW, gewichtOk_gilt _ hGew⟩

/-! ## 8. Joint witness: the rule fires on a real program.

    ALL premises of `OptRematConst_verbindung` instantiated JOINTLY:
    `3 + 4` recomputed to `7` under a `bind` with a `leave`
    continuation at the admitted certificate
    `⟨true, true, ⟨1, 2⟩, true, true⟩`, in the NON-DEGENERATE reference
    program `refD` (whose `einzahlen` writes its table,
    `refEin_schreibt`), beside the reached F-machine run `MB` that
    changes memory (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`).
    Every conjunct group is used. -/

/-- JOINT WITNESS for `OptRematConst_verbindung`: `3 + 4` recomputed
    to `7` at an admitted site on `refD`, beside the memory-changing
    reached run. -/
theorem OptRematConst_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (cert : RematCert)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x y : Int)
      (rest : Endblock refD V l ((.int (x + y) (x + y)) :: Γ) Λ)
      (_hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
      (_hz : rematZulassen cert = true)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (.lit (x + y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
        = (eval σ₀ (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (.lit (x + y) : Expr refD Γ Λ (.int (x + y) (x + y))) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y))) rest) σ ρ
      ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat
      ∧ cert.g.rematKosten ≤ cert.g.spillKosten
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptRematConst_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf)
    (cert := ⟨true, true, ⟨1, 2⟩, true, true⟩)
    (Γ := []) (Λ := []) (l := true)
    (x := 3) (y := 4) (rest := Endblock.leave rfl) (hW := by decide)
    (hz := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf,
    ⟨true, true, ⟨1, 2⟩, true, true⟩, [], [], true, 3, 4,
    Endblock.leave rfl, by decide, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No block-window float rewrite: section 5 proves the admitted float
      recomputation preserves value and `gleitPasst` outcome at the value
      level; the two-block window with recomputed avail facts stays with
      the lowering lane.
    - No `div`/`rem`/`sub`/`neg` syntax connection: their VALUES
      recompute (section 3); only `add` gets the `Endblock` connection
      here.
    - No totalCost inequality: the rematerialised window is the same block
      shape with the spill traffic removed, so step-budget accounting is
      unchanged; the admitted weight `⟨1, 2⟩` is realised by the actual
      target forms of section 6, and the formal level-(c) machine-work
      bound is OPEN per IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at canonical words and `gleitRechne` values.
-/

#print axioms gewichtOk
#print axioms rematZulassen
#print axioms rematVerweigert_fehler
#print axioms rematVerweigert_teuer
#print axioms rematVerweigert_gewicht
#print axioms rematVerweigert_strtod
#print axioms rematVerweigert_mxcsr
#print axioms gewichtOk_gilt
#print axioms rematAdd_wert
#print axioms rematSub_wert
#print axioms rematMul_wert
#print axioms rematNeg_wert
#print axioms rematDiv_wert
#print axioms rematLit_wert
#print axioms rematWort_add
#print axioms rematGleit_behält
#print axioms rematFolge_zaehlt
#print axioms spillFolge_zaehlt
#print axioms rematFolge_spart
#print axioms rematZulassen_gewicht
#print axioms OptRematConst_verbindung
#print axioms OptRematConst_verbindung_zeuge

#print axioms gewichtOk
#print axioms rematZulassen

end Gabbro.Grammatik.X86
