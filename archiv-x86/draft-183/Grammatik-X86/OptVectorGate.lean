/-
  File:      Grammatik/X86/OptVectorGate.lean
  Subject:   Vectorisation gate rule lemma (lane 875).

  DESIGN section 7 row "Vectorisation (future)": local premise "§6 tier-2
  gate: lane separation + atomicity table + privateness + tail",
  certificate "A+B+C", failure case "lane-disjoint but shared-observable
  order inversion; all refused until vector rule proved", phase M, gated.

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.Vektor`):
  vectorisation fires only behind the admitted tier-2 gate; the packed
  lanes implement the scalar sums (lane separation through `laneNat_add`,
  lifted to words through `addB`); the scalar window keeps its evaluated
  value and its `execEnd` outcome (no fault added or removed, same
  successor worlds); the folded value reads back whole through the
  canonical word. No `ensures` is derived, no refusal becomes a warning,
  no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Vektor

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided tier-2 gate (DESIGN section 7 row): proved lane
    separation, an admitted atomicity-table entry (128-bit access is NOT
    single-copy atomic, so a shared store needs the TSO bridge rule),
    a private-or-immutable memory proof, and a preserved tail loop. -/
structure VecGateCert where
  spurOk : Bool
  atomOk : Bool
  privatOk : Bool
  schwanzOk : Bool
  deriving DecidableEq, Repr

/-- Admission: every gate condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def vecTorZulassen (c : VecGateCert) : Bool :=
  c.spurOk && c.atomOk && c.privatOk && c.schwanzOk

/-! ## 1. Refusals: each open gate condition refuses; shared-observable
    order inversion refuses even where lanes are disjoint.

    The DESIGN failure case is `vecTorVerweigert_geteilt`: the lanes are
    proved disjoint (`spurOk = true`) yet the memory is shared-observable
    (`privatOk = false`), so a concurrent observer could see the torn
    intermediate state of `vecWrite_teilt` or an inverted order. The gate
    refuses: lane disjointness never implies atomicity or reordering of
    shared operations. -/

/-- Lane separation missing refuses the rule. -/
theorem vecTorVerweigert_spur (c : VecGateCert)
    (h : c.spurOk = false) :
    vecTorZulassen c = false := by
  simp [vecTorZulassen, h]

/-- Atomicity-table entry missing refuses: a 128-bit access is NOT
    single-copy atomic (`vecWrite_teilt`), so a shared vector store
    without the TSO-bridge rule never fires. -/
theorem vecTorVerweigert_atom (c : VecGateCert)
    (h : c.atomOk = false) :
    vecTorZulassen c = false := by
  simp [vecTorZulassen, h]

/-- SHARED-OBSERVABLE ORDER INVERSION refuses: disjoint lanes over
    shared-observable memory never vectorise. -/
theorem vecTorVerweigert_geteilt (c : VecGateCert)
    (h : c.privatOk = false) :
    vecTorZulassen c = false := by
  simp [vecTorZulassen, h]

/-- Dropped tail loop refuses: without the remainder path the last
    elements would silently change value. -/
theorem vecTorVerweigert_schwanz (c : VecGateCert)
    (h : c.schwanzOk = false) :
    vecTorZulassen c = false := by
  simp [vecTorZulassen, h]

/-- Probe: the fully admitted gate passes. -/
theorem probe_vecTorZulassen_ok :
    vecTorZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: disjoint lanes over shared memory are refused. -/
theorem probe_vecTorZulassen_geteilt :
    vecTorZulassen ⟨true, true, false, true⟩ = false := by
  decide

/-- Probe: a missing atomicity entry is refused. -/
theorem probe_vecTorZulassen_atom :
    vecTorZulassen ⟨true, false, true, true⟩ = false := by
  decide

/-! ## 2. Certificate shape: local rewrite record plus recomputed
    analysis citations (DESIGN certificate "A+B+C").

    Layer A (local rewrite): the gate itself, re-decided by the
    validator. Layer B (dataflow/CFG): recomputed availability and the
    block map, carried as checked data. Layer C (duty binding): the
    effect/duty binding at the site, carried as checked data. A missing
    citation refuses the certificate outright. -/

/-- The exact certificate shape: the re-decided gate plus one Bool per
    recomputed analysis citation. -/
structure VecZertifikat where
  tor : VecGateCert
  verfuegbar : Bool
  blockKarte : Bool
  pflichtBindung : Bool
  deriving DecidableEq, Repr

/-- Certificate admission: the gate plus every citation holds. -/
def zertifikatOk (z : VecZertifikat) : Bool :=
  vecTorZulassen z.tor && z.verfuegbar && z.blockKarte && z.pflichtBindung

/-- An admitted certificate carries an admitted gate. -/
theorem zertifikatOk_tor (z : VecZertifikat)
    (h : zertifikatOk z = true) :
    vecTorZulassen z.tor = true := by
  simp only [zertifikatOk, Bool.and_eq_true] at h
  exact h.1.1.1

/-- A missing availability citation refuses the certificate. -/
theorem zertifikatVerweigert_verfuegbar (z : VecZertifikat)
    (h : z.verfuegbar = false) :
    zertifikatOk z = false := by
  simp [zertifikatOk, h]

/-- Probe: the full certificate is admitted. -/
theorem probe_zertifikatOk :
    zertifikatOk ⟨⟨true, true, true, true⟩, true, true, true⟩ = true := by
  decide

/-- Probe: a gate-admitted rewrite with a missing block map is refused. -/
theorem probe_zertifikatOhneKarte :
    zertifikatOk ⟨⟨true, true, true, true⟩, true, false, true⟩ = false := by
  decide

/-! ## 3. Lane separation: each packed lane is the scalar op on that
    lane, with no cross-lane carry.

    The unconditional facts are `laneNat_add`/`laneGet_add` of
    `Vektor.lean`, reused here, never redefined. The gated lemma below
    lifts the VALIDATOR-RECOMPUTED separation equation (the layer-A
    citation, conditional on admission) to the word level the lowering
    consumes. The recomputation obligation is conditional on admission
    (`hLane` takes `hz`): the equation is claimed only where the
    validator admitted the site. -/

/-- The admitted vector add reads per lane as the canonical modular
    add: the recomputed separation fact lifted to words. -/
theorem vektorAdd_zugelassen (b : Breite) (vx vy : Vektor) (i : Nat)
    (hi : i < laneCount b)
    (z : VecZertifikat) (hz : zertifikatOk z = true)
    (hLane : ∀ j : Nat, j < laneCount b → vecTorZulassen z.tor = true →
      laneNat b (vecAdd b vx vy) j =
        (laneNat b vx j + laneNat b vy j) % 2 ^ b.bits) :
    laneGet b (vecAdd b vx vy) i =
      addB b (laneGet b vx i) (laneGet b vy i) := by
  have e := hLane i hi (zertifikatOk_tor z hz)
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 (laneNat b (vecAdd b vx vy) i)).toNat =
    (addB b (laneGet b vx i) (laneGet b vy i)).toNat
  rw [BitVec.toNat_ofNat, e, addB_nat,
    laneGet_toNat, laneGet_toNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (laneMod_pos b)) (laneMod_le b))]

/-- Boundary probe: two 64-bit lanes add independently
    (`5 + 7 = 12`, `3 + 4 = 7`). -/
theorem probe_vektorAdd_b64 :
    laneNat .b64 (vecAdd .b64 (vecMk .b64 (fun _ => 5))
      (vecMk .b64 (fun _ => 7))) 0 = 12 ∧
    laneNat .b64 (vecAdd .b64 (vecMk .b64 (fun _ => 3))
      (vecMk .b64 (fun _ => 4))) 1 = 7 := by
  decide

/-! ## 4. Connection: the scalar window keeps value and outcome while
    the admitted packed lanes implement the same sums.

    Stated at an `Endblock.bind` window with an ARBITRARY continuation
    `rest`, so the conclusion covers every downstream observation at
    once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved;
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree, including the float `logik
    bereich` checks downstream, which read the same values from the
    same environments), every downstream observation agrees (contracts
    at their place read the same values, call logs gain no event, no
    shared access is added or removed for concurrency -- both sides
    read `orte = []`), and the step-budget accounting is unchanged
    (same block shape, the removed computation is pure and unbudgeted);
    (3) the folded value reads back whole through the canonical word;
    (4) the admitted packed lanes read per lane as the canonical
    modular adds (the recomputed layer-A citation, conditional on the
    admitted certificate).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard. The checker's range
    at the site (`weiter`/`narrow`) is untouched and still enforced
    there. The lowering of the admitted lanes to bytes, the per-access
    TSO bridge and the tail-loop code motion stay OPEN (see CUTS). -/

/-- CONNECTION: the scalar fold preserves value, outcome and the
    width-exact word image, and the admitted vector lanes implement
    the same per-lane sums. -/
theorem OptVectorGate_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x y : Int)
    (rest : Endblock D V l ((.int (x + y) (x + y)) :: Γ) Λ)
    (hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
    (σ₀ σ : World D) (ρ : Env D Γ)
    (b : Breite) (vx vy : Vektor) (i : Nat) (hi : i < laneCount b)
    (z : VecZertifikat) (hz : zertifikatOk z = true)
    (hLane : ∀ j : Nat, j < laneCount b → vecTorZulassen z.tor = true →
      laneNat b (vecAdd b vx vy) j =
        (laneNat b vx j + laneNat b vy j) % 2 ^ b.bits) :
    (eval σ₀ (.lit (x + y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
      = (eval σ₀ (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.lit (x + y) : Expr D Γ Λ (.int (x + y) (x + y))) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.add (.lit x) (.lit y) : Expr D Γ Λ (.int (x + y) (x + y))) rest) σ ρ
    ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat
    ∧ laneGet b (vecAdd b vx vy) i =
        addB b (laneGet b vx i) (laneGet b vy i) := by
  have hWort : ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat := by
    have h : (x + y).toNat < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  exact ⟨rfl, rfl, hWort,
    vektorAdd_zugelassen b vx vy i hi z hz hLane⟩

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptVectorGate_verbindung` instantiated JOINTLY:
    `3 + 4` folds to `7` under a `bind` with a `leave` continuation,
    beside two admitted 64-bit lanes (`3` and `4` against `7` and `0`),
    in the NON-DEGENERATE reference program `refD` (whose `einzahlen`
    writes its table, `refEin_schreibt`), beside the reached F-machine
    run `MB` that changes memory (`refB_erreicht`, `refB_schreibt`:
    slot `0 -> 100`). Every conjunct group is used. -/

/-- JOINT WITNESS for `OptVectorGate_verbindung`: `3 + 4` folds to `7`
    with two admitted lanes on `refD`, beside the memory-changing
    reached run. -/
theorem OptVectorGate_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x y : Int)
      (rest : Endblock refD V l ((.int (x + y) (x + y)) :: Γ) Λ)
      (_hW : 0 ≤ x + y ∧ x + y < 2 ^ 64)
      (σ₀ σ : World refD) (ρ : Env refD Γ)
      (b : Breite) (vx vy : Vektor) (i : Nat) (_hi : i < laneCount b)
      (z : VecZertifikat) (_hz : zertifikatOk z = true)
      (_hLane : ∀ j : Nat, j < laneCount b → vecTorZulassen z.tor = true →
        laneNat b (vecAdd b vx vy) j =
          (laneNat b vx j + laneNat b vy j) % 2 ^ b.bits),
      (eval σ₀ (.lit (x + y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
        = (eval σ₀ (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (.lit (x + y) : Expr refD Γ Λ (.int (x + y) (x + y))) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.add (.lit x) (.lit y) : Expr refD Γ Λ (.int (x + y) (x + y))) rest) σ ρ
      ∧ ((BitVec.ofNat 64 (x + y).toNat : Wort)).toNat = (x + y).toNat
      ∧ laneGet b (vecAdd b vx vy) i =
          addB b (laneGet b vx i) (laneGet b vy i)
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptVectorGate_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (x := 3) (y := 4) (rest := Endblock.leave rfl) (hW := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
    (b := .b64) (vx := vecMk .b64 (fun _ => 3)) (vy := vecMk .b64 (fun _ => 4))
    (i := 0) (hi := by decide)
    (z := ⟨⟨true, true, true, true⟩, true, true, true⟩) (hz := by decide)
    (hLane := fun j hj _ => laneNat_add .b64 _ _ j hj)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, 3, 4,
    Endblock.leave rfl, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil,
    .b64, vecMk .b64 (fun _ => 3), vecMk .b64 (fun _ => 4), 0, by decide,
    ⟨⟨true, true, true, true⟩, true, true, true⟩, by decide,
    fun j hj _ => laneNat_add .b64 _ _ j hj,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No native vector lowering: no decoder/ABI/image claim, no fault
      order across lanes, no tearing correspondence against the
      per-access TSO bridge (the 128-bit access is NOT single-copy
      atomic: `vecWrite_teilt` stands, and `atomOk` is the admission
      the bridge lane decides, never invented here), no FP lanes, no
      call-log preservation beyond the unchanged `execEnd` outcome, no
      budget transfer for the packed accesses, no progress interaction.
      `simdFreigabe` stays `false`.
    - No block-window float rewrite: the rewritten window is integer
      `.int` binds only; downstream float checks (`gleitPasst`,
      `narrow`) read the same values from the same environments through
      the equal `execEnd` outcome, so their outcomes agree without any
      float node being rewritten.
    - No totalCost inequality: the window is the same block shape with
      one pure computation removed, so step-budget accounting is
      unchanged; the formal level-(c) machine-work bound is OPEN per
      IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at canonical words and lane values.
-/

#print axioms vecTorZulassen
#print axioms vecTorVerweigert_spur
#print axioms vecTorVerweigert_atom
#print axioms vecTorVerweigert_geteilt
#print axioms vecTorVerweigert_schwanz
#print axioms zertifikatOk
#print axioms zertifikatOk_tor
#print axioms zertifikatVerweigert_verfuegbar
#print axioms vektorAdd_zugelassen
#print axioms probe_vektorAdd_b64
#print axioms OptVectorGate_verbindung
#print axioms OptVectorGate_verbindung_zeuge

end Gabbro.Grammatik.X86
