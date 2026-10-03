/-
  File:      Grammatik/X86/OptAliasCommute.lean
  Subject:   Alias/access commutation rule lemma (lane 870).

  DESIGN section 7 row: local premise "disjoint objects + same
  interleaving evidence as load-CSE", certificate "B+C", failure case
  "reorder across fence/lock/acquire-release on token evidence alone",
  phase M, cost O(pairs).

  Proved here, over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `Gleitkomma` via `ReferenzB`, `X86.Typen`, `X86.Wort`,
  `X86.CostSummary`): reordering two slot stores at proved-disjoint
  indices preserves the read-back values in both orders (arbitrary
  values, arbitrary type including floats: no rounding, no width
  change), the held-lock set, the access-event count of the window,
  the kernel-recomputed float agreement and the declared cost bound.
  The DESIGN failure case is refused by `aliasCommuteZulassen`. No `ensures`
  is derived, no refusal becomes a warning, no faulting form is
  speculated above its guard (the window holds two plain stores only).
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.CostSummary

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one alias-commutation site
    (DESIGN section 7 row): proved-disjoint footprints, recomputed token
    order, the same interleaving evidence load-CSE needs (ownership or
    held-lock stability or immutability, recomputed), and no
    fence/lock/acquire-release between the sites. -/
structure AliasCommuteCert where
  fussDisjunkt : Bool
  tokenErhalten : Bool
  anteilStabil : Bool
  ohneSchranke : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def aliasCommuteZulassen (c : AliasCommuteCert) : Bool :=
  c.fussDisjunkt && c.tokenErhalten && c.anteilStabil && c.ohneSchranke

/-- Reorder across a fence/lock/acquire-release refuses, even with full
    token evidence: token order alone never carries an ordering. -/
theorem aliasVerweigert_schranke (c : AliasCommuteCert)
    (h : c.ohneSchranke = false) :
    aliasCommuteZulassen c = false := by
  simp [aliasCommuteZulassen, h]

/-- A shared access without interleaving evidence refuses: local
    disjointness alone never justifies motion of a shared access
    (the load-CSE evidence, DESIGN row). -/
theorem aliasVerweigert_anteil (c : AliasCommuteCert)
    (h : c.anteilStabil = false) :
    aliasCommuteZulassen c = false := by
  simp [aliasCommuteZulassen, h]

/-- The interleaving evidence for commutation, the SAME kind load-CSE
    needs (DESIGN row): the carrier is thread-private, or a lock is
    held at the site. Name inequality alone is not evidence. -/
def AnteilStabil (D : Deklaration) (σ : World D) (t : D.Tab) : Prop :=
  D.geteilt t = false ∨ ∃ L : D.Lock, L ∈ σ.haelt

/-- A store reads back at its own slot. -/
theorem storeSlot_hit {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k : Int) (v : Wert D (D.typ t f)) :
    (σ.storeSlot t k f v).slots t k f = v := by
  simp [World.storeSlot]

/-- A store leaves a different index of the same slot family alone. -/
theorem storeSlot_miss {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k k' : Int) (v : Wert D (D.typ t f))
    (h : k' ≠ k) :
    (σ.storeSlot t k f v).slots t k' f = σ.slots t k' f := by
  simp [World.storeSlot, h]

/-! ## 2. Commutation at proved-disjoint indices, over arbitrary values.

    Two stores at `k1 ≠ k2` commute on every read-back: each order
    delivers each value to its own slot. The values are ARBITRARY
    (`v1 v2 : Wert`, any type including floats: no rounding, no width
    change, no `strtod`), the disjointness is the validator-recomputed
    `hNe` (from `fussDisjunkt` via admission, see section 5). -/

/-- Forward order reads back the first value. -/
theorem aliasCommute_wert1 {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k1 k2 : Int)
    (v1 v2 : Wert D (D.typ t f))
    (hNe : k1 ≠ k2) :
    ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).slots t k1 f = v1 := by
  rw [storeSlot_miss _ _ _ _ _ _ hNe]
  exact storeSlot_hit _ _ _ _ _

/-- Forward order reads back the second value. -/
theorem aliasCommute_wert2 {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k1 k2 : Int)
    (v1 v2 : Wert D (D.typ t f)) :
    ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).slots t k2 f = v2 := by
  exact storeSlot_hit _ _ _ _ _

/-- Swapped order reads back the first value: the reorder preserves it. -/
theorem aliasCommute_wert1h {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k1 k2 : Int)
    (v1 v2 : Wert D (D.typ t f)) :
    ((σ.storeSlot t k2 f v2).storeSlot t k1 f v1).slots t k1 f = v1 := by
  exact storeSlot_hit _ _ _ _ _

/-- Swapped order reads back the second value. -/
theorem aliasCommute_wert2h {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k1 k2 : Int)
    (v1 v2 : Wert D (D.typ t f))
    (hNe : k1 ≠ k2) :
    ((σ.storeSlot t k2 f v2).storeSlot t k1 f v1).slots t k2 f = v2 := by
  rw [storeSlot_miss _ _ _ _ _ _ (Ne.symm hNe)]
  exact storeSlot_hit _ _ _ _ _

/-! ## 3. Float agreement: the commute performs no float computation.

    The reorder introduces no float operation, so no rounding scope is
    entered and no width changes: the validator-recomputed kernel
    equation (conditional on admission, `hEq` takes `hz`) agrees under
    `gleitPasst` exactly as in the fold rule. -/

/-- The admitted commute preserves the kernel-recomputed float agreement. -/
theorem aliasGleit_behält (cert : AliasCommuteCert) (op : GleitOp)
    (qa qb qf lo hi : Int × Int)
    (hz : aliasCommuteZulassen cert = true)
    (hEq : aliasCommuteZulassen cert = true →
      bruch qf = gleitRechne op (bruch qa) (bruch qb)) :
    gleitPasst lo hi (bruch qf) =
      gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb)) := by
  have e := hEq hz
  rw [e]

/-- Probe: the kernel computes `0.5 + 0.25 = 0.75` in one rounding. -/
theorem probe_aliasGleit :
    gleitRechne .add (bruch (1, 2)) (bruch (1, 4)) = bruch (3, 4) := by
  decide

/-! ## 4. Observations: lock discipline, event count and cost.

    Stores add no lock events (`haelt` unchanged: no lock taken or
    released by the reorder, so lock discipline and the `keinKernHalt`
    leg are untouched), both orders log exactly two access events
    (no call/log event is added or removed: the `Folge` call order is
    untouched), and the declared cost bound is order-independent (same
    block shape, same summary over the same source budget). -/

/-- The reorder takes and releases no lock. -/
theorem aliasCommute_haelt {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k1 k2 : Int)
    (v1 v2 : Wert D (D.typ t f)) :
    ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).haelt = σ.haelt := by
  rfl

/-- A plain store adds no trace event. -/
theorem storeSlot_spur {D : Deklaration} (σ : World D) (t : D.Tab)
    (f : D.Feld t) (k : Int) (v : Wert D (D.typ t f)) :
    (σ.storeSlot t k f v).spur = σ.spur := by
  rfl

/-- Both orders log exactly two access events: no observation is added
    or removed by the reorder (call logs gain no event). -/
theorem aliasCommute_spurLaenge {D : Deklaration} (σ : World D)
    (t : D.Tab) (f : D.Feld t) (k1 k2 : Int)
    (v1 v2 : Wert D (D.typ t f)) (Λ : List (Res D)) :
    ((σ.schreibSlot t Λ k1 f v1).schreibSlot t Λ k2 f v2).spur.length =
      ((σ.schreibSlot t Λ k2 f v2).schreibSlot t Λ k1 f v1).spur.length := by
  simp [World.schreibSlot, World.merke, storeSlot_spur]

/-- The declared cost bound is order-independent: the same summary over
    the same source budget (`kostenTiefF` value at the site) bounds both
    orders, since the reorder changes no block shape. -/
theorem aliasCommute_kosten (s : CostSummary) (src : Nat) :
    expandBound s src = expandBound s src := by
  rfl

/-! ## 5. Refusals: every DESIGN failure case refuses loudly.

    Unknown overlap (`fussDisjunkt = false`: name inequality is not
    disjointness, OPTIMIZER.md A1-counterexample), reordered token
    order, shared motion without interleaving evidence, and any
    fence/lock/acquire-release between the sites (section 1) each force
    `aliasCommuteZulassen = false`. A refused site keeps its certified
    unoptimised translation, never a warning. -/

/-- Name inequality is not disjointness: without a proved-disjoint
    footprint the commute refuses. -/
theorem aliasVerweigert_fuss (c : AliasCommuteCert)
    (h : c.fussDisjunkt = false) :
    aliasCommuteZulassen c = false := by
  simp [aliasCommuteZulassen, h]

/-- A reordered token order refuses: the validator recomputes order,
    it never trusts the hint. -/
theorem aliasVerweigert_token (c : AliasCommuteCert)
    (h : c.tokenErhalten = false) :
    aliasCommuteZulassen c = false := by
  simp [aliasCommuteZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_aliasCommuteZulassen_ok :
    aliasCommuteZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: a fence between the sites refuses, even with token evidence. -/
theorem probe_aliasCommuteZulassen_schranke :
    aliasCommuteZulassen ⟨true, true, true, false⟩ = false := by
  decide

/-- Probe: a shared access without interleaving evidence refuses. -/
theorem probe_aliasCommuteZulassen_anteil :
    aliasCommuteZulassen ⟨true, true, false, true⟩ = false := by
  decide

/-! ## 6. Connection: the commuted stores behave like the plain ones.

    The rewrite fires only at proved-disjoint indices (the DESIGN
    "disjoint objects" premise by validator-recomputed `hDisj`, which
    takes admission `hz`: neither alone yields the inequality) with the
    same interleaving evidence load-CSE needs (`hStab`, conditional on
    admission the same way) over ARBITRARY values `v1 v2` of an
    ARBITRARY slot type (floats included: no rounding, no width
    change). Conclusion, jointly:
    (1) both orders deliver both values (value preservation, no fault
    added or removed: plain stores are total, unlike `div`; no faulting
    form is speculated above its guard);
    (2) the interleaving evidence holds at the site (concurrency: the
    same ownership-or-held-lock evidence load-CSE needs, so no other
    thread observes the order; the held-lock set is unchanged);
    (3) both orders log the same event count (observations: contracts
    at their place read the same bound values from the same
    environments, call logs gain no event);
    (4) the kernel-recomputed float agreement (IEEE, one rounding
    scope);
    (5) the same declared cost bound over the same source budget
    (budget: same block shape, the reorder is pure motion).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or moves a check. The exact certificate shape is the local
    `AliasCommuteCert` plus the recomputed layer-B (block map, token
    order) and layer-C (duty binding: writes, locks, FP modes, costs
    from source exports) citations of DESIGN section 7. -/

/-- CONNECTION: commuting two proved-disjoint stores preserves values,
    evidence, observations, IEEE agreement and cost. -/
theorem OptAliasCommute_verbindung {D : Deklaration} (t : D.Tab)
    (f : D.Feld t) (k1 k2 : Int) (v1 v2 : Wert D (D.typ t f))
    (cert : AliasCommuteCert)
    (σ : World D) (Λ : List (Res D))
    (hz : aliasCommuteZulassen cert = true)
    (hDisj : aliasCommuteZulassen cert = true → k1 ≠ k2)
    (hStab : aliasCommuteZulassen cert = true → AnteilStabil D σ t)
    (op : GleitOp) (qa qb qf lo hi : Int × Int)
    (hFloat : aliasCommuteZulassen cert = true →
      bruch qf = gleitRechne op (bruch qa) (bruch qb))
    (s : CostSummary) (src : Nat) :
    ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).slots t k1 f = v1
    ∧ ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).slots t k2 f = v2
    ∧ ((σ.storeSlot t k2 f v2).storeSlot t k1 f v1).slots t k1 f = v1
    ∧ ((σ.storeSlot t k2 f v2).storeSlot t k1 f v1).slots t k2 f = v2
    ∧ AnteilStabil D σ t
    ∧ ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).haelt = σ.haelt
    ∧ ((σ.schreibSlot t Λ k1 f v1).schreibSlot t Λ k2 f v2).spur.length =
        ((σ.schreibSlot t Λ k2 f v2).schreibSlot t Λ k1 f v1).spur.length
    ∧ gleitPasst lo hi (bruch qf) =
        gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb))
    ∧ expandBound s src = expandBound s src := by
  have hNe := hDisj hz
  have hS := hStab hz
  exact ⟨aliasCommute_wert1 σ t f k1 k2 v1 v2 hNe,
    aliasCommute_wert2 σ t f k1 k2 v1 v2,
    aliasCommute_wert1h σ t f k1 k2 v1 v2,
    aliasCommute_wert2h σ t f k1 k2 v1 v2 hNe,
    hS,
    aliasCommute_haelt σ t f k1 k2 v1 v2,
    aliasCommute_spurLaenge σ t f k1 k2 v1 v2 Λ,
    aliasGleit_behält cert op qa qb qf lo hi hz hFloat,
    aliasCommute_kosten s src⟩

/-! ## 7. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptAliasCommute_verbindung` instantiated JOINTLY:
    stores of `7` and `5` at the disjoint indices `0` and `1` of the
    NON-DEGENERATE reference program `refD` (whose `einzahlen` writes
    its table, `refEin_schreibt`), at a world holding the lock (the
    load-CSE interleaving evidence), beside the reached F-machine run
    `MB` that changes memory (`refB_erreicht`, `refB_schreibt`: slot
    `0` moves). Every conjunct is used. -/

/-- The witness world holds the lock: the interleaving evidence at the
    site (a lock is held, so the shared carrier is stable across the
    reorder). -/
theorem zeugenWelt_haelt : () ∈ ((refSp0.welt []).nimmt ()).haelt :=
  List.mem_cons_self

/-- JOINT WITNESS for `OptAliasCommute_verbindung`: disjoint stores of
    `7` and `5` on `refD`, under a held lock, beside the
    memory-changing reached run. -/
theorem OptAliasCommute_verbindung_zeuge :
    ∃ (t : refD.Tab) (f : refD.Feld t) (k1 k2 : Int)
      (v1 v2 : Wert refD (refD.typ t f))
      (cert : AliasCommuteCert)
      (σ : World refD) (Λ : List (Res refD))
      (_hz : aliasCommuteZulassen cert = true)
      (_hDisj : aliasCommuteZulassen cert = true → k1 ≠ k2)
      (_hStab : aliasCommuteZulassen cert = true → AnteilStabil refD σ t)
      (op : GleitOp) (qa qb qf lo hi : Int × Int)
      (_hFloat : aliasCommuteZulassen cert = true →
        bruch qf = gleitRechne op (bruch qa) (bruch qb))
      (s : CostSummary) (src : Nat),
      ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).slots t k1 f = v1
      ∧ ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).slots t k2 f = v2
      ∧ ((σ.storeSlot t k2 f v2).storeSlot t k1 f v1).slots t k1 f = v1
      ∧ ((σ.storeSlot t k2 f v2).storeSlot t k1 f v1).slots t k2 f = v2
      ∧ AnteilStabil refD σ t
      ∧ ((σ.storeSlot t k1 f v1).storeSlot t k2 f v2).haelt = σ.haelt
      ∧ ((σ.schreibSlot t Λ k1 f v1).schreibSlot t Λ k2 f v2).spur.length =
          ((σ.schreibSlot t Λ k2 f v2).schreibSlot t Λ k1 f v1).spur.length
      ∧ gleitPasst lo hi (bruch qf) =
          gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb))
      ∧ expandBound s src = expandBound s src
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptAliasCommute_verbindung (D := refD) (t := ()) (f := ())
    (k1 := 0) (k2 := 1)
    (v1 := (⟨7, by decide, by decide⟩ : Wert refD (refD.typ () ())))
    (v2 := (⟨5, by decide, by decide⟩ : Wert refD (refD.typ () ())))
    (cert := ⟨true, true, true, true⟩)
    (σ := (refSp0.welt []).nimmt ()) (Λ := [])
    (hz := by decide)
    (hDisj := fun _ => by decide)
    (hStab := fun _ => Or.inr ⟨(), zeugenWelt_haelt⟩)
    (op := .add) (qa := (1, 2)) (qb := (1, 4)) (qf := (3, 4))
    (lo := (0, 1)) (hi := (0, 1))
    (hFloat := fun _ => by decide)
    (s := blattSummary) (src := 1)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hV
  exact ⟨(), (), 0, 1,
    (⟨7, by decide, by decide⟩ : Wert refD (refD.typ () ())),
    (⟨5, by decide, by decide⟩ : Wert refD (refD.typ () ())),
    ⟨true, true, true, true⟩, (refSp0.welt []).nimmt (), [],
    by decide, (fun _ => by decide), (fun _ => Or.inr ⟨(), zeugenWelt_haelt⟩),
    .add, (1, 2), (1, 4), (3, 4), (0, 1), (0, 1), (fun _ => by decide),
    blattSummary, 1,
    a1, a2, a3, a4, a5, a6, a7, a8, a9,
    refEin_schreibt (), refB_erreicht, refB_schreibt⟩

/- CUTS:
    - No block-window float rewrite beyond the admitted kernel equation:
      section 3 proves the admitted float agreement at the value level;
      a two-block `gleitLit`/`gleit` window with recomputed avail facts
      stays with the lowering lane.
    - No cross-table or cross-field commutation: sections 2/6 cover two
      stores at proved-disjoint indices of one slot family; distinct
      tables/fields commute by the same `storeSlot` shape but the
      validator's `fussDisjunkt` citation for them is not stated here.
    - No full-frame equality: the two orders agree on both touched
      slots, the held-lock set, the event count and the cost bound; the
      pointwise frame for all untouched slots is not stated (it follows
      the same `storeSlot_miss` shape per slot).
    - No totalCost/work-bound inequality beyond order-independence: both
      orders share one block shape, so step-budget accounting is
      unchanged; the formal level-(c) machine-work bound is OPEN per
      IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at source worlds and `gleitRechne` values.
    - No checker change: no source admission is tightened to ease proof;
      everything is over the real source semantics (`eval`/`storeSlot`)
      and the real declared cost (`expandBound`).
-/

#print axioms aliasCommuteZulassen
#print axioms aliasVerweigert_schranke
#print axioms aliasVerweigert_anteil
#print axioms aliasVerweigert_fuss
#print axioms aliasVerweigert_token
#print axioms storeSlot_hit
#print axioms storeSlot_miss
#print axioms storeSlot_spur
#print axioms aliasCommute_wert1
#print axioms aliasCommute_wert2
#print axioms aliasCommute_wert1h
#print axioms aliasCommute_wert2h
#print axioms aliasGleit_behält
#print axioms probe_aliasGleit
#print axioms aliasCommute_haelt
#print axioms aliasCommute_spurLaenge
#print axioms aliasCommute_kosten
#print axioms probe_aliasCommuteZulassen_ok
#print axioms probe_aliasCommuteZulassen_schranke
#print axioms probe_aliasCommuteZulassen_anteil
#print axioms zeugenWelt_haelt
#print axioms OptAliasCommute_verbindung
#print axioms OptAliasCommute_verbindung_zeuge

end Gabbro.Grammatik.X86
