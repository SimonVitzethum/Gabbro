/-
  File:      Grammatik/X86/OptUnrollBound.lean
  Subject:   Bounded loop-unroll rule lemma (lane 874).

  DESIGN section 7 row "Loop unroll (bounded)": local premise "explicit `k`
  + trip evidence + remainder path in map; token ops duplicated, never
  fused", certificate "B" (block map + recomputed analysis citations),
  failure case "fuse two token ops into one wide access (tearing /
  visibility change)", phase M, cost O(k*body).

  The optimisation is stated as a generic rule lemma over arbitrary values:
  a loop trip of `n` iterations with per-iteration token list `b` rewrites
  to full groups of `k` plus a remainder of `r`, duplicating (never fusing)
  the token ops. The validator decides the side conditions
  (`unrollZulassen`); a refused optional optimisation falls back to another
  certified translation, never to a warning.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.CostSummary

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Validator-decided side conditions for one bounded-unroll site (DESIGN
    section 7 row): explicit factor `k`, trip evidence present, remainder
    path in the block map, and token ops duplicated, never fused. -/
structure UnrollCert where
  k : Nat
  tripBekannt : Bool
  restPfad : Bool
  keineFusion : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. `decide (0 < c.k)` makes the
    explicit factor positive by decision; anything else refuses. -/
def unrollZulassen (c : UnrollCert) : Bool :=
  decide (0 < c.k) && c.tripBekannt && c.restPfad && c.keineFusion

/-! ## 1. Refusal: every missing side condition refuses the rewrite.

    The DESIGN failure case is `keineFusion = false`: two token ops fused
    into one wide access would change tearing and visibility, so the rule
    must NOT fire. A missing trip count, a missing remainder path, and a
    zero factor refuse the same way. Refusal keeps the certified cheaper
    translation; it never becomes a warning. -/

/-- Fused token ops refuse the unroll (the DESIGN failure case). -/
theorem unrollVerweigert_fusion (c : UnrollCert)
    (h : c.keineFusion = false) :
    unrollZulassen c = false := by
  simp [unrollZulassen, h]

/-- A missing trip count refuses the unroll. -/
theorem unrollVerweigert_trip (c : UnrollCert)
    (h : c.tripBekannt = false) :
    unrollZulassen c = false := by
  simp [unrollZulassen, h]

/-- A missing remainder path refuses the unroll. -/
theorem unrollVerweigert_rest (c : UnrollCert)
    (h : c.restPfad = false) :
    unrollZulassen c = false := by
  simp [unrollZulassen, h]

/-- A zero factor refuses the unroll. -/
theorem unrollVerweigert_kNull (c : UnrollCert)
    (h : c.k = 0) :
    unrollZulassen c = false := by
  have h0 : (decide (0 < c.k)) = false := by
    rw [h]
    decide
  simp [unrollZulassen, h0]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_unrollZulassen_ok :
    unrollZulassen ⟨2, true, true, true⟩ = true := by
  decide

/-- Probe: a fusion-tainted certificate is refused. -/
theorem probe_unrollZulassen_fusion :
    unrollZulassen ⟨2, true, true, false⟩ = false := by
  decide

/-! ## 2. Trace model: duplication, never fusion.

    The loop trip of `n` iterations with per-iteration token list `b` is the
    token list `b` duplicated `n` times (`koerperSpur`). The unrolled shape
    (`entrollt`) is the same tokens regrouped: full groups covering `q * k`
    iterations plus a remainder of `r`. Grouping changes no token, drops no
    token, and merges no two tokens into one wide access. -/

/-- The loop trace: per-iteration token list `b`, duplicated `n` times. -/
def koerperSpur (b : List α) : Nat → List α
  | 0 => []
  | n + 1 => koerperSpur b n ++ b

/-- The unrolled shape: full groups of `k` (`q * k` iterations) followed by
    a remainder of `r` iterations. Same tokens, regrouped. -/
def entrollt (b : List α) (k q r : Nat) : List α :=
  koerperSpur b (q * k) ++ koerperSpur b r

/-- Splitting a trip splits the trace: regrouping is what the rule does. -/
theorem koerperSpur_append (b : List α) (a d : Nat) :
    koerperSpur b (a + d) = koerperSpur b a ++ koerperSpur b d := by
  induction d with
  | zero => simp [koerperSpur]
  | succ m ih =>
    have hstep : a + (m + 1) = (a + m) + 1 := by omega
    rw [hstep]
    simp [koerperSpur, ih, List.append_assoc]

/-- Probe: two iterations of `[1, 2]` duplicate to `[1, 2, 1, 2]`. -/
theorem probe_koerperSpur :
    koerperSpur [1, 2] 2 = [1, 2, 1, 2] := by
  decide

/-! ## 3. Preservation core: the unrolled trace IS the loop trace.

    Trip evidence (`hTrip`: the trip `n` is `q` full groups of `k` plus a
    remainder `r`) makes the unrolled shape equal to the loop trace: same
    values in the same order, so no fault is added or removed, every
    per-position observation agrees, and the step-budget accounting is
    unchanged. The admitted-option wrapper (`entrolltOpt`) fires only where
    the validator admitted the site; anywhere else it returns `none`, so a
    refused site keeps its certified translation. -/

/-- Trip evidence makes the unrolled shape equal to the loop trace. -/
theorem spur_gleich (b : List α) (k q r n : Nat)
    (hTrip : n = q * k + r) :
    koerperSpur b n = entrollt b k q r := by
  rw [hTrip]
  simp [entrollt, koerperSpur_append]

/-- The admitted rewrite: fires only where the validator admitted the site. -/
def entrolltOpt (cert : UnrollCert) (b : List α) (q r : Nat) : Option (List α) :=
  if unrollZulassen cert then some (entrollt b cert.k q r) else none

/-- An admitted site rewrites to exactly the loop trace. -/
theorem entrolltOpt_gilt (cert : UnrollCert) (b : List α) (q r n : Nat)
    (hTrip : n = q * cert.k + r)
    (hAdm : unrollZulassen cert = true) :
    entrolltOpt cert b q r = some (koerperSpur b n) := by
  have hEq : koerperSpur b n = entrollt b cert.k q r :=
    spur_gleich b cert.k q r n hTrip
  simp [entrolltOpt, hAdm, hEq]

/-- A refused site does not rewrite: `none` keeps the certified
    translation. This is the precise refusal case of the DESIGN row: fused
    token ops, a missing trip count, a missing remainder path, or a zero
    factor all force admission to `false`, hence `none`. -/
theorem entrolltOpt_verweigert (cert : UnrollCert) (b : List α) (q r : Nat)
    (h : unrollZulassen cert = false) :
    entrolltOpt cert b q r = none := by
  simp [entrolltOpt, h]

/-! ## 4. Certificate shape: local rewrite record plus recomputed citations.

    The exact certificate the Rust backend emits and the Lean validator
    re-decides is `UnrollNachweis`: the local rewrite record (`regel`: the
    admitted factor `k` and the no-fusion evidence) plus the recomputed
    analysis citations (`blockAbbild`: the remainder path is present in the
    recomputed block map; `analyseNeu`: trip and alias facts recomputed at
    the site, never carried over from a stale analysis). `nachweisOk`
    admits the certificate only where all three hold. -/

/-- The exact certificate shape: local rewrite record plus recomputed
    analysis citations (DESIGN certificate "B"). -/
structure UnrollNachweis where
  regel : UnrollCert
  blockAbbild : Bool
  analyseNeu : Bool
  deriving DecidableEq, Repr

/-- Certificate admission: rule record, block map, and fresh analysis. -/
def nachweisOk (w : UnrollNachweis) : Bool :=
  unrollZulassen w.regel && w.blockAbbild && w.analyseNeu

/-- An admitted certificate carries an admitted rule record. -/
theorem nachweisOk_regel (w : UnrollNachweis)
    (h : nachweisOk w = true) :
    unrollZulassen w.regel = true := by
  unfold nachweisOk at h
  cases hc : unrollZulassen w.regel with
  | true => rfl
  | false => simp [hc] at h

/-- Probe: the full certificate passes. -/
theorem probe_nachweisOk :
    nachweisOk ⟨⟨2, true, true, true⟩, true, true⟩ = true := by
  decide

/-- Probe: a stale-analysis certificate is refused. -/
theorem probe_nachweisOk_analyse :
    nachweisOk ⟨⟨2, true, true, true⟩, true, false⟩ = false := by
  decide

/-! ## 5. Observation preservation: values, faults, contracts, call logs.

    Every per-token observation `f` agrees between the loop trace and the
    unrolled shape: same values at the same positions (contracts at their
    place read the same values), same fault stops in the same order (no
    faulting form is speculated above its guard, no fault is removed), and
    same call-log order (`FolgeG` order is the list order, which is kept).
    Concurrency sees no added or removed shared access: unrolling
    duplicates the token list, it never invents a token. -/

/-- Every per-token observation agrees: values, faults, logs in order. -/
theorem unrollBeob_gleich (b : List α) (k q r n : Nat) (f : α → β)
    (hTrip : n = q * k + r) :
    List.map f (koerperSpur b n) = List.map f (entrollt b k q r) := by
  rw [spur_gleich b k q r n hTrip]

/-- IEEE: the kernel float check per token agrees. Tokens are rational
    literals; `bruch` computes the single kernel rounding and `gleitPasst`
    is the `logik bereich` outcome at the site. Duplication recomputes
    nothing (no host `strtod`, no second rounding) and drops no check, so
    value and fault outcome agree at every position. -/
theorem unrollGleit_behält (b : List (Int × Int)) (k q r n : Nat)
    (lo hi : Int × Int)
    (hTrip : n = q * k + r) :
    List.map (fun t => gleitPasst lo hi (bruch t)) (koerperSpur b n) =
      List.map (fun t => gleitPasst lo hi (bruch t)) (entrollt b k q r) := by
  rw [spur_gleich b k q r n hTrip]

/-! ## 6. Budget, concurrency, and machine work.

    The unrolled shape has exactly the loop trace's token count, so the
    step-budget accounting is unchanged (re-summing declared costs is
    bookkeeping; exhaustion timing stays with the simulation, which is
    OPEN per CostSummary). Every token of the unrolled shape is a token of
    the body: no shared access is added or removed for concurrency, and no
    two tokens are merged into one wide access. Machine work adds over the
    unrolled segments through the reused canonical `targetWork_add`. -/

/-- The loop trace holds `n` copies of the body tokens. -/
theorem koerperSpur_länge (b : List α) (n : Nat) :
    (koerperSpur b n).length = n * b.length := by
  induction n with
  | zero => simp [koerperSpur]
  | succ m ih =>
    simp only [koerperSpur, ih, List.length_append]
    rw [Nat.add_mul, Nat.one_mul]

/-- The unrolled shape keeps the loop trace's token count (budget). -/
theorem unrollBudget_gleich (b : List α) (k q r n : Nat)
    (hTrip : n = q * k + r) :
    (entrollt b k q r).length = (koerperSpur b n).length := by
  rw [spur_gleich b k q r n hTrip]

/-- The unrolled shape costs `n` body copies: no cost hidden, none forged. -/
theorem unrollKosten_gleich (b : List α) (k q r n : Nat)
    (hTrip : n = q * k + r) :
    (entrollt b k q r).length = n * b.length := by
  rw [← spur_gleich b k q r n hTrip, koerperSpur_länge]

/-- Every token of the loop trace is a body token. -/
theorem koerperSpur_mem (b : List α) (t : α) (n : Nat)
    (h : t ∈ koerperSpur b n) : t ∈ b := by
  induction n with
  | zero => simp [koerperSpur] at h
  | succ m ih =>
    simp only [koerperSpur, List.mem_append] at h
    cases h with
    | inl hm => exact ih hm
    | inr hm => exact hm

/-- The unrolled shape adds no token: no shared access added or removed,
    and no two tokens merged into one wide access (concurrency). -/
theorem unrollKeineNeuen (b : List α) (k q r : Nat) (t : α)
    (h : t ∈ entrollt b k q r) : t ∈ b := by
  simp only [entrollt, List.mem_append] at h
  cases h with
  | inl hm => exact koerperSpur_mem b t (q * k) hm
  | inr hm => exact koerperSpur_mem b t r hm

/-- Machine work adds over the unrolled segments, through the reused
    canonical `targetWork_add` (CostSummary): full groups plus remainder. -/
theorem unrollArbeit_additiv (b : List Befehl) (k q r : Nat) :
    targetWork (entrollt b k q r) =
      targetWork (koerperSpur b (q * k)) + targetWork (koerperSpur b r) := by
  simp [entrollt, targetWork_add]

/-! ## 7. Connection: the admitted unroll preserves the trip.

    CONNECTION over arbitrary token values (`b : List (Int × Int)`,
    rational-literal tokens so the IEEE leg is concrete), jointly:
    (1) the admitted rewrite yields exactly the loop trace -- same values
    in the same order, so no fault is added or removed, every downstream
    observation agrees (contracts at their place read the same values,
    call logs keep their order, no shared access is added or removed for
    concurrency), and the step-budget accounting is unchanged;
    (2) the kernel float check per token agrees (IEEE: single rounding,
    `logik bereich` outcome kept at every position);
    (3) the token count is `n` body copies (budget: nothing hidden, nothing
    forged);
    (4) every unrolled token is a body token (concurrency: duplication
    only, never a fused wide access).
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard (a faulting token keeps its
    position and its stop). -/

/-- CONNECTION: the admitted bounded unroll preserves value, fault,
    observation, count, and token membership of the trip. -/
theorem OptUnrollBound_verbindung (cert : UnrollCert) (b : List (Int × Int))
    (q r n : Nat) (lo hi : Int × Int)
    (hTrip : n = q * cert.k + r)
    (hAdm : unrollZulassen cert = true) :
    entrolltOpt cert b q r = some (koerperSpur b n)
    ∧ List.map (fun t => gleitPasst lo hi (bruch t)) (koerperSpur b n)
      = List.map (fun t => gleitPasst lo hi (bruch t)) (entrollt b cert.k q r)
    ∧ (entrollt b cert.k q r).length = n * b.length
    ∧ ∀ t, t ∈ entrollt b cert.k q r → t ∈ b := by
  have hEq : koerperSpur b n = entrollt b cert.k q r :=
    spur_gleich b cert.k q r n hTrip
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [entrolltOpt, hAdm, hEq]
  · rw [hEq]
  · exact unrollKosten_gleich b cert.k q r n hTrip
  · intro t ht
    exact unrollKeineNeuen b cert.k q r t ht

/-! ## 8. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptUnrollBound_verbindung` instantiated JOINTLY:
    factor `k = 2`, one rational-literal token, `q = 3` full groups plus a
    remainder of `r = 1` (`n = 7`), in the NON-DEGENERATE reference program
    `refD` (whose `einzahlen` writes its table, `refEin_schreibt`), beside
    the reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). -/

/-- JOINT WITNESS for `OptUnrollBound_verbindung`: factor 2, three full
    groups plus a remainder of one, on `refD`, beside the memory-changing
    reached run. -/
theorem OptUnrollBound_verbindung_zeuge :
    ∃ (cert : UnrollCert) (b : List (Int × Int)) (q r n : Nat) (lo hi : Int × Int)
      (_hTrip : n = q * cert.k + r) (_hAdm : unrollZulassen cert = true),
      entrolltOpt cert b q r = some (koerperSpur b n)
      ∧ List.map (fun t => gleitPasst lo hi (bruch t)) (koerperSpur b n)
        = List.map (fun t => gleitPasst lo hi (bruch t)) (entrollt b cert.k q r)
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptUnrollBound_verbindung (cert := ⟨2, true, true, true⟩)
    (b := [(1, 2)]) (q := 3) (r := 1) (n := 7)
    (lo := (0, 100)) (hi := (0, 100))
    (hTrip := by decide) (hAdm := by decide)
  exact ⟨⟨2, true, true, true⟩, [(1, 2)], 3, 1, 7, (0, 100), (0, 100),
    by decide, by decide, hV.1, hV.2.1,
    refEin_schreibt (), refB_erreicht, refB_schreibt⟩

/- CUTS:
   - No source-syntax loop rewrite: the rule is proved over token lists
     (the per-iteration token fragment), not over `Syntax` loop forms and
     not against `execStmt`/`exec`. The `while`/`traverse` lowering that
     produces the token lists, with its trip-count evidence, stays with
     the lowering lane; the single accepted IR (lane 287 draft,
     uncommitted) is awaited, not invented here.
   - No totalCost/budget-simulation claim: the unrolled shape keeps the
     loop trace's token count (`unrollKosten_gleich`); relating machine
     work to `passes`-budget exhaustion (`budget_simulation`) is the
     separate OPEN obligation of CostSummary, never derived by re-summing.
   - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
     correspondence stops at token equality, kernel `bruch`/`gleitPasst`
     values, and canonical `targetWork` counts.
   - No remainder-bound check in the rule: `r < k` is re-decided by the
     validator with the block map (`restPfad`), not needed for trace
     equality; entry/lock invariants at unrolled sites stay with the
     invariant lanes (review §10 shapes).
   - No checker change: no source admission is tightened to ease proof;
     refusal keeps the certified cheaper translation, never a warning.
-/

#print axioms unrollVerweigert_fusion
#print axioms unrollVerweigert_trip
#print axioms unrollVerweigert_rest
#print axioms unrollVerweigert_kNull
#print axioms probe_unrollZulassen_ok
#print axioms probe_unrollZulassen_fusion
#print axioms koerperSpur_append
#print axioms probe_koerperSpur
#print axioms spur_gleich
#print axioms entrolltOpt_gilt
#print axioms entrolltOpt_verweigert
#print axioms nachweisOk_regel
#print axioms probe_nachweisOk
#print axioms probe_nachweisOk_analyse
#print axioms unrollBeob_gleich
#print axioms unrollGleit_behält
#print axioms koerperSpur_länge
#print axioms unrollBudget_gleich
#print axioms unrollKosten_gleich
#print axioms koerperSpur_mem
#print axioms unrollKeineNeuen
#print axioms unrollArbeit_additiv
#print axioms OptUnrollBound_verbindung
#print axioms OptUnrollBound_verbindung_zeuge

#print axioms unrollZulassen
#print axioms nachweisOk
#print axioms koerperSpur
#print axioms entrollt
#print axioms entrolltOpt

end Gabbro.Grammatik.X86
