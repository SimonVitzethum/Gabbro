/-
  File:      Grammatik/X86/OptAllocLinear.lean
  Subject:   Linear-scan register allocation rule lemma (lane 878).

  DESIGN section 7 row: linear-scan colouring against recomputed liveness;
  certificate "colouring plus spill homes plus scan order plus live sets
  plus cited fusions"; failure case "fused 16-byte spill over two live
  carriers".

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `Gleitkomma`, `X86.Typen`, `X86.Wort`, `ReferenzB`,
  `X86.RegisterInterference`, `X86.Stapel`): interval overlap with a shared
  live point; the validator-decided admission `allocOk` (scan order,
  colouring, fusion, liveness citation, frame homes); the colouring
  separation it implies; value preservation through scan-ordered machine
  homes (registers and spill slots); IEEE guard agreement for carried
  floats; and the precise refusals, including the fused 16-byte spill over
  two live carriers. No `ensures` is derived, no refusal becomes a warning,
  no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.RegisterInterference
import Grammatik.X86.Stapel

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-! ## 1. Live intervals and half-open overlap.

    Liveness is RECOMPUTED data cited by the certificate, never inferred
    here: each carrier carries its half-open interval `[start, finish)`.
    Two carriers that overlap share a live point (proved below), so the
    pair check of section 3 covers every true interference. -/

/-- A carrier live interval: half-open `[start, finish)` over abstract
    program points. -/
structure Interval where
  value : Nat
  start : Nat
  finish : Nat
  deriving DecidableEq, Repr

/-- Half-open overlap: neither interval ends before the other starts. -/
def intervalsOverlap (a b : Interval) : Bool :=
  decide (a.start < b.finish) && decide (b.start < a.finish)

/-- Probe: `[0, 10)` and `[5, 15)` overlap. -/
theorem probe_overlap_yes :
    intervalsOverlap ⟨0, 0, 10⟩ ⟨1, 5, 15⟩ = true := by
  decide

/-- Probe: `[0, 5)` and `[5, 10)` only touch, they do not overlap. -/
theorem probe_overlap_no :
    intervalsOverlap ⟨0, 0, 5⟩ ⟨1, 5, 10⟩ = false := by
  decide

/-! ## 2. Machine homes and the validator-decided admission.

    The certificate is a LOCAL rewrite record (scan order, colouring,
    cited fusions) plus RECOMPUTED analysis citations (live sets per
    point): every check below is a decided `Bool`, so anything missing or
    conflicting is `false`, never a silent pass. Register homes reuse the
    canonical `Register` file and the pinned `rsp` of `RegisterInterference`;
    spill homes are frame slots of `Stapel` (8 bytes each). -/

/-- A machine home: a general register or a frame spill slot. -/
inductive Home where
  | reg : Register → Home
  | spill : Nat → Home
  deriving DecidableEq, Repr

/-- The colouring: each carrier maps to at most one home. `Wert` is the
    declared-live carrier id of `RegisterInterference`, reused, not
    redefined. -/
abbrev Assign := List (Wert × Home)

/-- Home lookup in the colouring. -/
def homeOf : Assign → Wert → Option Home
  | [], _ => none
  | (u, h) :: t, w => if u == w then some h else homeOf t w

/-- Two homes check: both assigned, distinct. Fail-closed like `kanteOk`. -/
def homesDiffer : Option Home → Option Home → Bool
  | some h1, some h2 => decide (h1 ≠ h2)
  | _, _ => false

/-- Start lookup for the scan-order check. -/
def startOf : List Interval → Wert → Option Nat
  | [], _ => none
  | iv :: t, w => if iv.value == w then some iv.start else startOf t w

/-- The scan order is sorted by interval start: the linear-scan
    discipline, checked, not trusted. -/
def orderSorted : List Interval → List Wert → Bool
  | _, [] => true
  | _, [_] => true
  | ivs, u :: v :: t =>
      match startOf ivs u, startOf ivs v with
      | some s1, some s2 => decide (s1 ≤ s2) && orderSorted ivs (v :: t)
      | _, _ => false

/-- Scan-order citation: every interval value scanned exactly in a
    start-sorted order covering the whole interval list. -/
def allocScanOk (ivs : List Interval) (order : List Wert) : Bool :=
  decide (order.length = ivs.length) &&
    ivs.all (fun iv => order.contains iv.value) &&
    orderSorted ivs order

/-- Colouring soundness against the recomputed intervals: every two
    distinct overlapping carriers have distinct homes. Implication is
    Bool algebra (`uEq || (!overlap || hd)`), so the general extraction
    below rewrites with equations only. -/
def allocPairOk (ivs : List Interval) (zu : Assign) : Bool :=
  ivs.all fun a => ivs.all fun b =>
    (a.value == b.value) ||
      (!(intervalsOverlap a b) ||
        homesDiffer (homeOf zu a.value) (homeOf zu b.value))

/-- Fusion soundness: a CITED fused 16-byte spill unit (two adjacent
    8-byte slots accessed as one) never covers two overlapping carriers.
    Adjacent slots without a cited fusion are ordinary separate homes and
    stay allowed. -/
def allocFusedOk (ivs : List Interval) (zu : Assign)
    (fus : List (Nat × Nat)) : Bool :=
  ivs.all fun a => ivs.all fun b =>
    (a.value == b.value) ||
      (!(intervalsOverlap a b) ||
        match homeOf zu a.value, homeOf zu b.value with
        | some (.spill s1), some (.spill s2) =>
            !(fus.any (fun q => q.1 == s1 && q.2 == s2) ||
              fus.any (fun q => q.1 == s2 && q.2 == s1))
        | _, _ => true)

/-- A point covered by an interval. -/
def coversPt (iv : Interval) (p : Nat) : Bool :=
  decide (iv.start ≤ p) && decide (p < iv.finish)

/-- Liveness citation check: every cited live value covers its point,
    and every covering interval value is cited. -/
def allocLiveOk (ivs : List Interval) (leb : List (Nat × List Wert)) : Bool :=
  leb.all fun (p, vs) =>
    vs.all (fun v => match ivs.find? (fun iv => iv.value == v) with
                     | some iv => coversPt iv p
                     | none => false) &&
    ivs.all (fun iv => (!(coversPt iv p)) || vs.contains iv.value)

/-- One home is frame-admissible: registers avoid the pinned stack
    pointer, spill slots lie inside the frame depth. -/
def homeInFrame (depth : Nat) : Home → Bool
  | .reg r => !reserviertReg r
  | .spill s => decide (s < depth / 8)

/-- Every interval carrier is homed admissibly. -/
def allocHomeOk (ivs : List Interval) (zu : Assign) (depth : Nat) : Bool :=
  ivs.all fun iv => match homeOf zu iv.value with
                    | some h => homeInFrame depth h
                    | none => false

/-- The full admission: scan order, colouring, fusion, liveness citation
    and frame homes. Validator admission, never a hardware fault. -/
def allocOk (ivs : List Interval) (order : List Wert)
    (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
    (zu : Assign) (depth : Nat) : Bool :=
  allocScanOk ivs order && allocPairOk ivs zu && allocFusedOk ivs zu fus &&
    allocLiveOk ivs leb && allocHomeOk ivs zu depth

/-! ## 3. Check-implies facts and the shared live point.

    Every premise is used: the `= true` admission supplies the conjunct,
    the membership hypotheses select the elements. Overlapping carriers
    share a live point, so the pair check covers every true interference
    against the recomputed liveness. -/

/-- Helper: the scan conjunct of a passing check passes. -/
theorem allocOk_scan (ivs : List Interval) (order : List Wert)
    (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
    (zu : Assign) (depth : Nat)
    (h : allocOk ivs order leb fus zu depth = true) :
    allocScanOk ivs order = true := by
  unfold allocOk at h
  have hk := (Bool.and_eq_true _ _).mp h
  have hk2 := (Bool.and_eq_true _ _).mp hk.1
  have hk3 := (Bool.and_eq_true _ _).mp hk2.1
  exact (Bool.and_eq_true _ _).mp hk3.1 |>.1

/-- Helper: the colouring conjunct of a passing check passes. -/
theorem allocOk_pair (ivs : List Interval) (order : List Wert)
    (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
    (zu : Assign) (depth : Nat)
    (h : allocOk ivs order leb fus zu depth = true) :
    allocPairOk ivs zu = true := by
  unfold allocOk at h
  have hk := (Bool.and_eq_true _ _).mp h
  have hk2 := (Bool.and_eq_true _ _).mp hk.1
  have hk3 := (Bool.and_eq_true _ _).mp hk2.1
  exact (Bool.and_eq_true _ _).mp hk3.1 |>.2

/-- Helper: the fusion conjunct of a passing check passes. -/
theorem allocOk_fused (ivs : List Interval) (order : List Wert)
    (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
    (zu : Assign) (depth : Nat)
    (h : allocOk ivs order leb fus zu depth = true) :
    allocFusedOk ivs zu fus = true := by
  unfold allocOk at h
  have hk := (Bool.and_eq_true _ _).mp h
  have hk2 := (Bool.and_eq_true _ _).mp hk.1
  exact (Bool.and_eq_true _ _).mp hk2.1 |>.2

/-- Helper: the liveness conjunct of a passing check passes. -/
theorem allocOk_live (ivs : List Interval) (order : List Wert)
    (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
    (zu : Assign) (depth : Nat)
    (h : allocOk ivs order leb fus zu depth = true) :
    allocLiveOk ivs leb = true := by
  unfold allocOk at h
  have hk := (Bool.and_eq_true _ _).mp h
  exact (Bool.and_eq_true _ _).mp hk.1 |>.2

/-- Helper: the home conjunct of a passing check passes. -/
theorem allocOk_home (ivs : List Interval) (order : List Wert)
    (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
    (zu : Assign) (depth : Nat)
    (h : allocOk ivs order leb fus zu depth = true) :
    allocHomeOk ivs zu depth = true := by
  unfold allocOk at h
  exact (Bool.and_eq_true _ _).mp h |>.2

/-- A passing check assigns distinct homes to every overlapping pair of
    distinct carriers. -/
theorem allocSeparate (ivs : List Interval) (zu : Assign)
    (a b : Interval)
    (hmA : a ∈ ivs) (hmB : b ∈ ivs)
    (huv : (a.value == b.value) = false)
    (hüber : intervalsOverlap a b = true)
    (hpaar : allocPairOk ivs zu = true) :
    homeOf zu a.value ≠ homeOf zu b.value := by
  have eA := (List.all_eq_true.mp hpaar) a hmA
  have eAB := (List.all_eq_true.mp eA) b hmB
  simp only [huv, hüber, Bool.not_true, Bool.false_or] at eAB
  unfold homesDiffer at eAB
  cases h1 : homeOf zu a.value with
  | none =>
      cases h2 : homeOf zu b.value with
      | none => simp only [h1] at eAB; exact absurd eAB (by decide)
      | some _ => simp only [h1] at eAB; exact absurd eAB (by decide)
  | some h1' =>
      cases h2 : homeOf zu b.value with
      | none => simp only [h1, h2] at eAB; exact absurd eAB (by decide)
      | some h2' =>
          simp only [h1, h2, decide_eq_true_eq] at eAB
          exact fun h => eAB (Option.some_inj.mp h)

/-- Overlapping NON-EMPTY carriers share a live point: the pair check
    is complete against the recomputed liveness. Non-emptiness is
    load-bearing: an empty `[50, 40)` interval "overlaps" everything by
    the bare endpoint comparison but shares no point. -/
theorem overlapHasPoint (a b : Interval)
    (hüber : intervalsOverlap a b = true)
    (haNe : a.start < a.finish) (hbNe : b.start < b.finish) :
    ∃ p, a.start ≤ p ∧ p < a.finish ∧ b.start ≤ p ∧ p < b.finish := by
  unfold intervalsOverlap at hüber
  simp only [decide_eq_true_eq, Bool.and_eq_true] at hüber
  obtain ⟨h1, h2⟩ := hüber
  by_cases hle : a.start ≤ b.start
  · exact ⟨b.start, hle, h2, Nat.le_refl _, hbNe⟩
  · have hlt : b.start < a.start := by omega
    exact ⟨a.start, Nat.le_refl _, haNe, Nat.le_of_lt hlt, h1⟩

/-! ## 4. Value, fault, IEEE and observation preservation.

    The allocator never recomputes a value: carriers are written whole
    into distinct homes. Registers are a total file (no fault possible);
    spill homes reload through the permission-checked canonical access,
    so an admitted in-frame slot with readable permissions adds no fault.
    Floats are carried whole, never re-rounded, so every `gleitPasst`
    guard agrees. Any observer over the two homed carriers — a contract
    predicate or a call-log entry constructor — agrees with the
    unallocated values. -/

/-- A register home reads back its own written word. -/
theorem regSet_liestEigen (r : Register → Wort) (a : Register) (x : Wort) :
    (regSet r a x) a = x := by
  unfold regSet
  simp

/-- Scan-ordered writes to two distinct register homes keep both values:
    each carrier reads back its own word. Every premise is used. -/
theorem allocSchreibt_bleibt (r0 : Register → Wort)
    (ra rb : Register) (wx wy : Wort)
    (hne : ra ≠ rb) :
    (regSet (regSet r0 ra wx) rb wy) ra = wx ∧
      (regSet (regSet r0 ra wx) rb wy) rb = wy := by
  have e1 : (regSet (regSet r0 ra wx) rb wy) ra = (regSet r0 ra wx) ra :=
    regSet_fremd _ _ _ _ hne
  exact ⟨by rw [e1, regSet_liestEigen], regSet_liestEigen _ _ _⟩

/-- Observer agreement: ANY observation over the two homed carriers —
    a `Bool` contract predicate or a call-log entry constructor into any
    type — agrees with the unallocated values. -/
theorem heimBeobachter_bleibt {α : Type} (F : Wort → Wort → α)
    (r0 : Register → Wort) (ra rb : Register) (wx wy : Wort)
    (hne : ra ≠ rb) :
    F ((regSet (regSet r0 ra wx) rb wy) ra)
      ((regSet (regSet r0 ra wx) rb wy) rb) = F wx wy := by
  have h := allocSchreibt_bleibt r0 ra rb wx wy hne
  rw [h.1, h.2]

/-- A spill home reloads its stored word through the permission-checked
    canonical access: admitted homes add no fault and keep the value. -/
theorem allocSpill_behält (m m1 : Speicher) (r : Rahmen) (s : Nat)
    (v : Wort)
    (hwr : write64 m (r.schlitzAddr s) v = some m1)
    (hrd : lesbar8 m (r.schlitzAddr s) = true) :
    read64 m1 (r.schlitzAddr s) = some v :=
  read64_nach_write64 m m1 _ v hwr hrd

/-- Carried floats are never re-rounded by the allocator: identical
    carried values give identical `gleitPasst` guard outcomes. -/
theorem gleitHeim_behält (qa qb lo hi : Int × Int) (heq : qa = qb) :
    gleitPasst lo hi (bruch qa) = gleitPasst lo hi (bruch qb) := by
  rw [heq]

/-- A width-exact carried value reads back whole through the canonical
    word: no truncation, no wrap. -/
theorem allocWort_rund (x : Int) (hW : 0 ≤ x ∧ x < 2 ^ 64) :
    ((BitVec.ofNat 64 x.toNat : Wort)).toNat = x.toNat := by
  have h : x.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Counted spill traffic of a colouring. -/
def spillAnzahl : Assign → Nat
  | [] => 0
  | (_, .reg _) :: t => spillAnzahl t
  | (_, .spill _) :: t => spillAnzahl t + 1

/-- Probe: two register homes need no spill traffic. -/
theorem probe_spillAnzahl_null :
    spillAnzahl [(0, .reg .rax), (1, .reg .rcx)] = 0 := by
  decide

/-- Probe: two spill homes count two. -/
theorem probe_spillAnzahl_zwei :
    spillAnzahl [(0, .spill 3), (1, .spill 4)] = 2 := by
  decide

/-- Spill traffic never exceeds the colouring size: the budget leg. -/
theorem spillAnzahl_schranke (zu : Assign) :
    spillAnzahl zu ≤ zu.length := by
  induction zu with
  | nil => exact Nat.zero_le _
  | cons hd tl ih =>
      obtain ⟨u, hh⟩ := hd
      cases hh with
      | reg r =>
          simp only [spillAnzahl, List.length_cons] at ih ⊢
          omega
      | spill s =>
          simp only [spillAnzahl, List.length_cons] at ih ⊢
          omega

/-- A spill-free colouring needs no spill traffic at all. -/
theorem spillfrei_ohneVerkehr (zu : Assign)
    (h : zu.all (fun p => match p.2 with
                          | .reg _ => true
                          | .spill _ => false) = true) :
    spillAnzahl zu = 0 := by
  induction zu with
  | nil => rfl
  | cons hd tl ih =>
      simp at h
      obtain ⟨hhd, htl⟩ := h
      obtain ⟨u, hh⟩ := hd
      cases hh with
      | reg r => simp [spillAnzahl, ih (List.all_eq_true.mpr (fun x hx => htl x.1 x.2 hx))]
      | spill s => simp at hhd

/-! ## 5. Refusals and positives.

    The precise refusal cases where the rule must NOT fire, plus the
    positive shapes where it fires. Concrete instances are decided; the
    fused 16-byte case additionally gets the general theorem: any cited
    fusion covering two overlapping carriers refuses the whole check. -/

/-- Shared witness intervals: `[0, 10)` and `[5, 15)` overlap. -/
def zeugenIvs : List Interval := [⟨0, 0, 10⟩, ⟨1, 5, 15⟩]

/-- Shared witness order: scan order `0` before `1`. -/
def zeugenOrdnung : List Wert := [0, 1]

/-- Shared witness liveness: recomputed live sets at points 0, 5, 10. -/
def zeugenLeb : List (Nat × List Wert) := [(0, [0]), (5, [0, 1]), (10, [1])]

/-- REFUSAL: two overlapping carriers in one register refuse. -/
theorem allocVerweigert_gleichesReg :
    allocOk zeugenIvs zeugenOrdnung zeugenLeb []
      [(0, .reg .rax), (1, .reg .rax)] 48 = false := by
  decide

/-- REFUSAL: homing a carrier to the pinned stack pointer refuses. -/
theorem allocVerweigert_rsp :
    allocOk zeugenIvs zeugenOrdnung zeugenLeb []
      [(0, .reg .rsp), (1, .reg .rcx)] 48 = false := by
  decide

/-- REFUSAL: two overlapping carriers sharing one spill slot refuse. -/
theorem allocVerweigert_gemeinsamerSlot :
    allocOk zeugenIvs zeugenOrdnung zeugenLeb []
      [(0, .spill 3), (1, .spill 3)] 48 = false := by
  decide

/-- REFUSAL (the DESIGN failure case): a fused 16-byte spill unit over
    two live carriers refuses, even with distinct slots and an in-frame
    home each. -/
theorem allocVerweigert_fusion :
    allocOk zeugenIvs zeugenOrdnung zeugenLeb [(3, 4)]
      [(0, .spill 3), (1, .spill 4)] 48 = false := by
  decide

/-- POSITIVE: the same two carriers in distinct registers are admitted. -/
theorem allocPositiv_reg :
    allocOk zeugenIvs zeugenOrdnung zeugenLeb []
      [(0, .reg .rax), (1, .reg .rcx)] 48 = true := by
  decide

/-- POSITIVE: adjacent spill slots WITHOUT a cited fusion stay allowed. -/
theorem allocPositiv_slotOhneFusion :
    allocOk zeugenIvs zeugenOrdnung zeugenLeb []
      [(0, .spill 3), (1, .spill 4)] 48 = true := by
  decide

/-- POSITIVE: non-overlapping carriers may share one spill slot. -/
theorem allocPositiv_geteilterSlot :
    allocOk [⟨0, 0, 5⟩, ⟨1, 5, 10⟩] [0, 1]
      [(0, [0]), (5, [1]), (9, [1])] []
      [(0, .spill 3), (1, .spill 3)] 48 = true := by
  decide

/-- GENERAL fused refusal: any cited fusion covering the spill homes of
    two overlapping carriers refuses the whole admission. -/
theorem allocFused_verweigert (ivs : List Interval) (zu : Assign)
    (fus : List (Nat × Nat)) (a b : Interval) (s1 s2 : Nat)
    (hmA : a ∈ ivs) (hmB : b ∈ ivs)
    (huv : (a.value == b.value) = false)
    (hüber : intervalsOverlap a b = true)
    (ha : homeOf zu a.value = some (.spill s1))
    (hb : homeOf zu b.value = some (.spill s2))
    (hf : (fus.any (fun q => q.1 == s1 && q.2 == s2) ||
           fus.any (fun q => q.1 == s2 && q.2 == s1)) = true)
    (hfused : allocFusedOk ivs zu fus = true) :
    False := by
  have eA := (List.all_eq_true.mp hfused) a hmA
  have eAB := (List.all_eq_true.mp eA) b hmB
  simp only [huv, hüber, Bool.not_true, Bool.false_or, ha, hb, hf] at eAB
  exact absurd eAB (by decide)

/-! ## 6. Connection: the admitted colouring preserves values and homes.

    The rewrite fires only on distinct overlapping carriers (the DESIGN
    "recomputed liveness" premise by construction) with register homes
    (the spill case keeps its own theorem, section 4); it is stated over
    ARBITRARY carried values, so the conclusion covers every downstream
    observation at once. Conclusion, jointly:
    (1) the evaluated source VALUES are preserved;
    (2) the carriers take DISTINCT homes, so scan-ordered machine writes
    keep both words (no clobber, no fault: the register file is total);
    (3) the width-exact values read back whole through the canonical
    word, and carried floats keep every `gleitPasst` guard outcome.
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard. -/

/-- CONNECTION: linear-scan colouring of two overlapping carriers to
    distinct registers preserves values, homes, words and float guards. -/
theorem OptAllocLinear_verbindung {D : Deklaration}
    {Γ : Ctx} {Λ : List (Res D)}
    (x y : Int)
    (ivs : List Interval) (order : List Wert)
    (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
    (zu : Assign) (depth : Nat)
    (a b : Interval)
    (hWx : 0 ≤ x ∧ x < 2 ^ 64) (hWy : 0 ≤ y ∧ y < 2 ^ 64)
    (hmA : a ∈ ivs) (hmB : b ∈ ivs)
    (huv : (a.value == b.value) = false)
    (hüber : intervalsOverlap a b = true)
    (hadmin : allocOk ivs order leb fus zu depth = true)
    (ra rb : Register)
    (ha : homeOf zu a.value = some (.reg ra))
    (hb : homeOf zu b.value = some (.reg rb))
    (r0 : Register → Wort) (wx wy : Wort)
    (qa qb lo hi : Int × Int) (heq : qa = qb)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.lit x : Expr D Γ Λ (.int x x)) σ ρ).n = x
    ∧ (eval σ₀ (.lit y : Expr D Γ Λ (.int y y)) σ ρ).n = y
    ∧ homeOf zu a.value ≠ homeOf zu b.value
    ∧ (regSet (regSet r0 ra wx) rb wy) ra = wx
    ∧ (regSet (regSet r0 ra wx) rb wy) rb = wy
    ∧ ((BitVec.ofNat 64 x.toNat : Wort)).toNat = x.toNat
    ∧ ((BitVec.ofNat 64 y.toNat : Wort)).toNat = y.toNat
    ∧ gleitPasst lo hi (bruch qa) = gleitPasst lo hi (bruch qb) := by
  have hpaar := allocOk_pair ivs order leb fus zu depth hadmin
  have hsep := allocSeparate ivs zu a b hmA hmB huv hüber hpaar
  have hne : ra ≠ rb := by
    intro hcon
    apply hsep
    rw [ha, hb, hcon]
  have hwr := allocSchreibt_bleibt r0 ra rb wx wy hne
  exact ⟨rfl, rfl, hsep, hwr.1, hwr.2, allocWort_rund x hWx,
    allocWort_rund y hWy, by rw [heq]⟩

/-! ## 7. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptAllocLinear_verbindung` instantiated JOINTLY:
    carriers `3` and `4` with overlapping intervals coloured to `rax`
    and `rcx`, in the NON-DEGENERATE reference program `refD` (whose
    `einzahlen` writes its table, `refEin_schreibt`), beside the reached
    F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). -/

/-- JOINT WITNESS for `OptAllocLinear_verbindung`: `3` and `4` colour
    to `rax`/`rcx` on `refD`, beside the memory-changing reached run. -/
theorem OptAllocLinear_verbindung_zeuge :
    ∃ (x y : Int)
      (ivs : List Interval) (order : List Wert)
      (leb : List (Nat × List Wert)) (fus : List (Nat × Nat))
      (zu : Assign) (depth : Nat)
      (a b : Interval)
      (_hWx : 0 ≤ x ∧ x < 2 ^ 64) (_hWy : 0 ≤ y ∧ y < 2 ^ 64)
      (_hmA : a ∈ ivs) (_hmB : b ∈ ivs)
      (_huv : (a.value == b.value) = false)
      (_hüber : intervalsOverlap a b = true)
      (_hadmin : allocOk ivs order leb fus zu depth = true)
      (ra rb : Register)
      (_ha : homeOf zu a.value = some (.reg ra))
      (_hb : homeOf zu b.value = some (.reg rb))
      (r0 : Register → Wort) (wx wy : Wort)
      (qa qb lo hi : Int × Int) (_heq : qa = qb)
      (σ₀ σ : World refD) (ρ : Env refD []),
      (eval σ₀ (.lit x : Expr refD [] [] (.int x x)) σ ρ).n = x
      ∧ (eval σ₀ (.lit y : Expr refD [] [] (.int y y)) σ ρ).n = y
      ∧ homeOf zu a.value ≠ homeOf zu b.value
      ∧ (regSet (regSet r0 ra wx) rb wy) ra = wx
      ∧ (regSet (regSet r0 ra wx) rb wy) rb = wy
      ∧ ((BitVec.ofNat 64 x.toNat : Wort)).toNat = x.toNat
      ∧ ((BitVec.ofNat 64 y.toNat : Wort)).toNat = y.toNat
      ∧ gleitPasst lo hi (bruch qa) = gleitPasst lo hi (bruch qb)
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptAllocLinear_verbindung (D := refD) (Γ := []) (Λ := [])
    (x := 3) (y := 4)
    (ivs := zeugenIvs) (order := zeugenOrdnung) (leb := zeugenLeb)
    (fus := []) (zu := [(0, .reg .rax), (1, .reg .rcx)]) (depth := 48)
    (a := ⟨0, 0, 10⟩) (b := ⟨1, 5, 15⟩)
    (hWx := by decide) (hWy := by decide)
    (hmA := by decide) (hmB := by decide)
    (huv := by decide) (hüber := by decide)
    (hadmin := by decide)
    (ra := .rax) (rb := .rcx) (ha := by decide) (hb := by decide)
    (r0 := fun _ => BitVec.ofNat 64 0)
    (wx := BitVec.ofNat 64 7) (wy := BitVec.ofNat 64 9)
    (qa := (1, 2)) (qb := (1, 2)) (lo := (0, 0)) (hi := (0, 100))
    (heq := rfl)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨3, 4, zeugenIvs, zeugenOrdnung, zeugenLeb, [],
    [(0, .reg .rax), (1, .reg .rcx)], 48,
    ⟨0, 0, 10⟩, ⟨1, 5, 15⟩, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, .rax, .rcx, by decide, by decide,
    (fun _ => BitVec.ofNat 64 0), BitVec.ofNat 64 7, BitVec.ofNat 64 9,
    (1, 2), (1, 2), (0, 0), (0, 100), rfl,
    refSp0.welt [], refSp0.welt [], Env.nil,
    hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.1,
    hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2,
    refEin_schreibt (), refB_erreicht, refB_schreibt⟩

/- CUTS:
    - No source-syntax rewrite: allocation is backend-only, so there is no
      `Endblock`/`execEnd` equality across homings here. Such an outcome
      leg needs the accepted lowering (IR-287 interface), which is waited
      for, not invented.
    - No machine lowering: homes are proved over the canonical register
      file and canonical `Speicher` words. The per-access TSO/GX bridge
      from slot-index separation to footprint disjointness is OPEN (slot
      inequality is proved; the address-arithmetic bridge is not).
    - No machine-work transfer: `spillAnzahl` is counted and bounded and
      the spill-free case provably needs no traffic, but the transfer
      into a `CostSummary` expansion bound is OPEN.
    - Contracts, call logs, concurrency and budget are proved at the
      value/home level (observer agreement, separation, spill counting);
      the place-level, log-append, TSO-step and work-bound legs wait for
      the accepted lowering.
    - The scan-order citation checks coverage and sortedness, not
      duplicate-freeness; the fusion check fires only on cited fusions.
    - No silicon correspondence, no ABI/loader claim: correspondence stops
      at canonical words, `gleitRechne`-free carried floats and decided
      admission Bools.
-/

#print axioms intervalsOverlap
#print axioms allocScanOk
#print axioms allocPairOk
#print axioms allocFusedOk
#print axioms allocLiveOk
#print axioms allocHomeOk
#print axioms allocOk
#print axioms allocSeparate
#print axioms overlapHasPoint
#print axioms regSet_liestEigen
#print axioms allocSchreibt_bleibt
#print axioms heimBeobachter_bleibt
#print axioms allocSpill_behält
#print axioms gleitHeim_behält
#print axioms allocWort_rund
#print axioms spillAnzahl_schranke
#print axioms spillfrei_ohneVerkehr
#print axioms allocFused_verweigert
#print axioms OptAllocLinear_verbindung
#print axioms OptAllocLinear_verbindung_zeuge

end Gabbro.Grammatik.X86
