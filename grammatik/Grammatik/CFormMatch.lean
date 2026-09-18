/-
  File:      Grammatik/CFormMatch.lean
  Subject:   Integer-match semantics: exhaustiveness over ranges (lane 228).

  After lane 222 (integer arms `3 =>`, `0 .. 255 =>`, `0 ..< 256 =>` in
  `ast.rs`, not yet lowered: lane 227's `switch` lowering is unmerged)
  this file denotes the arms, states exhaustiveness (covered exactly
  or with an explicit default -- never asserted, a missing arm is a
  refusal downstream, TODO wave B rule), and shows the denotation
  sound against the emitted `switch` (`CS.sw` + default branch):
  one correspondence lemma per arm shape.

  The range of the exhaustiveness check is the scrutinee's TYPE range
  (`.int lo hi` admits exactly `lo .. hi`, G1 `einpassen_voll`):
  coverage is decided over constants, never over user logic.
-/
import Grammatik.CFormen
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-- One integer `match` arm pattern (lane 222 `IntPat`, mirrored):
    an exact value (`3 =>`) or a literal range (`0 .. 255 =>`
    inclusive, `0 ..< 256 =>` exclusive). Bounds are literals on
    purpose: a computed bound would move the coverage decision into
    user logic. -/
inductive IArm where
  | exact (v : Int) : IArm
  | range (lo hi : Int) (excl : Bool) : IArm
  deriving DecidableEq, Repr

/-! ## 1. Denotation: which values an arm matches -/

/-- Decidable match test of one arm against a value. -/
def trifftB : IArm → Int → Bool
  | .exact v, x => x == v
  | .range lo hi false, x => decide (lo ≤ x ∧ x ≤ hi)
  | .range lo hi true, x => decide (lo ≤ x ∧ x < hi)

/-- Denotation of one arm: the values it matches. -/
def trifft (a : IArm) (x : Int) : Prop := trifftB a x = true

/-- Exact arm: it matches exactly its value. -/
theorem exact_trifft (v x : Int) : trifft (.exact v) x ↔ x = v := by
  simp only [trifft, trifftB, beq_iff_eq]

/-- Inclusive range arm: it matches exactly `lo .. hi`. -/
theorem range_incl_trifft (lo hi x : Int) :
    trifft (.range lo hi false) x ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [trifft, trifftB, decide_eq_true_eq]

/-- Exclusive range arm: it matches exactly `lo ..< hi`. -/
theorem range_excl_trifft (lo hi x : Int) :
    trifft (.range lo hi true) x ↔ lo ≤ x ∧ x < hi := by
  simp only [trifft, trifftB, decide_eq_true_eq]

/-! ## 2. Expansion: the `case` labels one arm writes -/

/-- `n` consecutive values from `s`: the finite enumeration behind
    every range expansion and every coverage check. -/
def aufzaehlung : Nat → Int → List Int
  | 0, _ => []
  | n + 1, s => s :: aufzaehlung n (s + 1)

/-- Membership in the enumeration is the interval. -/
theorem mem_aufzaehlung (n : Nat) (s x : Int) :
    x ∈ aufzaehlung n s ↔ s ≤ x ∧ x < s + n := by
  induction n generalizing s with
  | zero => simp [aufzaehlung]
  | succ n ih =>
    simp only [aufzaehlung, List.mem_cons]
    constructor
    · intro h
      rcases h with rfl | hm
      · constructor <;> omega
      · obtain ⟨h1, h2⟩ := (ih (s + 1)).mp hm
        constructor <;> omega
    · intro ⟨h1, h2⟩
      by_cases hx : x = s
      · exact Or.inl hx
      · exact Or.inr ((ih (s + 1)).mpr ⟨by omega, by omega⟩)

/-- The `case` labels one arm writes: the singleton for an exact arm,
    the full enumeration for a range (empty for an inverted range --
    an arm matching nothing, never a default). -/
def armKeys : IArm → List Int
  | .exact v => [v]
  | .range lo hi false =>
      if lo ≤ hi then aufzaehlung ((hi + 1 - lo).toNat) lo else []
  | .range lo hi true =>
      if lo < hi then aufzaehlung ((hi - lo).toNat) lo else []

/-- Exact arm: its label is its value. -/
theorem mem_armKeys_exact (v x : Int) :
    x ∈ armKeys (.exact v) ↔ x = v := by
  simp [armKeys]

/-- Inclusive range arm: its labels are exactly `lo .. hi`. -/
theorem mem_armKeys_incl (lo hi x : Int) :
    x ∈ armKeys (.range lo hi false) ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [armKeys]
  by_cases h : lo ≤ hi
  · rw [if_pos h, mem_aufzaehlung]
    have e1 : ((((hi + 1 - lo).toNat : Nat)) : Int) = hi + 1 - lo :=
      Int.toNat_of_nonneg (by omega)
    rw [e1]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩,
      fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
  · rw [if_neg h, List.mem_nil_iff, false_iff]
    intro ⟨h1, _⟩
    omega

/-- Exclusive range arm: its labels are exactly `lo ..< hi`. -/
theorem mem_armKeys_excl (lo hi x : Int) :
    x ∈ armKeys (.range lo hi true) ↔ lo ≤ x ∧ x < hi := by
  simp only [armKeys]
  by_cases h : lo < hi
  · rw [if_pos h, mem_aufzaehlung]
    have e1 : ((((hi - lo).toNat : Nat)) : Int) = hi - lo :=
      Int.toNat_of_nonneg (by omega)
    rw [e1]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩,
      fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
  · rw [if_neg h, List.mem_nil_iff, false_iff]
    intro ⟨h1, _⟩
    omega

/-- Denotation and labels agree, for every arm shape. -/
theorem trifft_mem_armKeys (a : IArm) (x : Int) :
    trifft a x ↔ x ∈ armKeys a := by
  cases a with
  | exact v => exact (exact_trifft v x).trans (mem_armKeys_exact v x).symm
  | range lo hi excl =>
    cases excl with
    | false =>
      exact (range_incl_trifft lo hi x).trans (mem_armKeys_incl lo hi x).symm
    | true =>
      exact (range_excl_trifft lo hi x).trans (mem_armKeys_excl lo hi x).symm

/-- The emitted `case` table: every covered value with its FIRST arm
    index. `List.lookup` returns the first pair, so dispatch is first
    match -- exactly `CS.sw` with `break;` in every arm. -/
def fallListeAux : List IArm → Nat → List (Int × Nat)
  | [], _ => []
  | a :: as, i => (armKeys a).map (fun k => (k, i)) ++ fallListeAux as (i + 1)

def fallListe (arms : List IArm) : List (Int × Nat) := fallListeAux arms 0

/-- Dispatch: the chosen arm index for a value, `none` for a miss. -/
def wahl (arms : List IArm) (x : Int) : Option Nat :=
  (fallListe arms).lookup x

/-- A member pair makes the lookup succeed. -/
theorem lookup_mem_isSome {l : List (Int × Nat)} {x : Int} {i : Nat}
    (h : (x, i) ∈ l) : (l.lookup x).isSome = true := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.mem_cons] at h
    rcases h with hmem | hm
    · have hx : x = a := congrArg Prod.fst hmem
      have he : ((x == a) = true) := by rw [beq_iff_eq]; exact hx
      simp only [List.lookup, he, Option.isSome_some]
    · by_cases he : (((x == a)) = true)
      · simp only [List.lookup, he, Option.isSome_some]
      · cases hbx : (x == a) with
        | true => exact absurd hbx he
        | false =>
          simp only [List.lookup, hbx]
          exact ih hm

/-- Every value an arm of the list matches reaches the table with
    some index. -/
theorem mem_fallListeAux_of (arms : List IArm) (i : Nat) (a : IArm) (x : Int)
    (ha : a ∈ arms) (hx : x ∈ armKeys a) :
    ∃ j, (x, j) ∈ fallListeAux arms i := by
  induction arms generalizing i with
  | nil => simp at ha
  | cons hd tl ih =>
    simp only [fallListeAux, List.mem_append]
    simp only [List.mem_cons] at ha
    rcases ha with rfl | hm
    · exact ⟨i, Or.inl (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩
    · obtain ⟨j, hj⟩ := ih (i + 1) hm
      exact ⟨j, Or.inr hj⟩

/-- A matched value dispatches to some arm. -/
theorem trifft_wahl_some {arms : List IArm} {x : Int}
    (h : ∃ a ∈ arms, trifft a x) : ∃ i, wahl arms x = some i := by
  obtain ⟨a, ha, ht⟩ := h
  rw [trifft_mem_armKeys] at ht
  obtain ⟨j, hj⟩ := mem_fallListeAux_of arms 0 a x ha ht
  have hs : ((fallListe arms).lookup x).isSome = true :=
    lookup_mem_isSome hj
  cases he : ((fallListe arms).lookup x) with
  | some i => exact ⟨i, he⟩
  | none => rw [he] at hs; simp at hs

/-- A miss refuses every arm: no arm matches the value. -/
theorem wahl_none_weigert {arms : List IArm} {x : Int}
    (hmiss : wahl arms x = none) (a : IArm) (ha : a ∈ arms) :
    ¬ trifft a x := by
  intro ht
  obtain ⟨i, hi⟩ := trifft_wahl_some ⟨a, ha, ht⟩
  rw [hmiss] at hi
  cases hi

/-! ## 3. Exhaustiveness: covered exactly, or with a default -/

/-- An integer match: arms plus whether a default arm stands.
    The default is EXPLICIT (written by the emitter as `default:`,
    admitted by the checker) -- never an inserted catch-all. -/
structure IntMatch where
  arme : List IArm
  hatDefault : Bool

/-- Exhaustiveness over `lo .. hi` (the scrutinee's TYPE range: `.int
    lo hi` admits exactly these values, G1 `einpassen_voll`): every
    value is matched by some arm, or a default stands. -/
def erschoepfend (m : IntMatch) (lo hi : Int) : Prop :=
  ∀ x, lo ≤ x → x ≤ hi → (∃ a ∈ m.arme, trifft a x) ∨ m.hatDefault = true

/-- The value list of `lo .. hi`: the inclusive range arm's expansion. -/
def werteListe (lo hi : Int) : List Int := armKeys (.range lo hi false)

theorem mem_werteListe (lo hi x : Int) :
    x ∈ werteListe lo hi ↔ lo ≤ x ∧ x ≤ hi :=
  mem_armKeys_incl lo hi x

/-- The decidable coverage check: what the checker runs. -/
def erschoepfendB (m : IntMatch) (lo hi : Int) : Bool :=
  m.hatDefault || (werteListe lo hi).all (fun x => m.arme.any (fun a => trifftB a x))

/-- The check decides the predicate. -/
theorem erschoepfendB_richtig (m : IntMatch) (lo hi : Int) :
    erschoepfendB m lo hi = true ↔ erschoepfend m lo hi := by
  simp only [erschoepfendB, erschoepfend, Bool.or_eq_true, List.all_eq_true,
    List.any_eq_true]
  constructor
  · intro h x hlo hhi
    rcases h with hd | hall
    · exact Or.inr hd
    · have hx : x ∈ werteListe lo hi := (mem_werteListe lo hi x).mpr ⟨hlo, hhi⟩
      obtain ⟨a, ha, ht⟩ := hall x hx
      exact Or.inl ⟨a, ha, ht⟩
  · intro h
    by_cases hd : m.hatDefault = true
    · exact Or.inl hd
    · refine Or.inr (fun x hx => ?_)
      obtain ⟨hlo, hhi⟩ := (mem_werteListe lo hi x).mp hx
      rcases h x hlo hhi with ⟨a, ha, ht⟩ | hd'
      · exact ⟨a, ha, ht⟩
      · exact absurd hd' hd

/-- Exhaustiveness leaves no value without an arm or the default:
    the wave-B safety rule (a missing arm is a refusal downstream,
    never an inserted default). -/
theorem erschoepfend_kein_fehlschlag (m : IntMatch) (lo hi x : Int)
    (hcov : erschoepfend m lo hi) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    m.hatDefault = true ∨ ∃ i, wahl m.arme x = some i := by
  rcases hcov x hlo hhi with ⟨a, ha, ht⟩ | hd
  · exact Or.inr (trifft_wahl_some ⟨a, ha, ht⟩)
  · exact Or.inl hd

/-- Without a default, every value in range dispatches to an arm. -/
theorem erschoepfend_ohne_default (m : IntMatch) (lo hi x : Int)
    (hcov : erschoepfend m lo hi) (hkein : m.hatDefault = false)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    ∃ i, wahl m.arme x = some i := by
  rcases erschoepfend_kein_fehlschlag m lo hi x hcov hlo hhi with hd | h
  · rw [hd] at hkein; cases hkein
  · exact h

/-! ## 4. Sound against the emitted `switch` -/

/-- The emitted integer `switch` WITH its default arm: a hit runs the
    chosen arm (every arm ends in `break`, hence `unbreak`), a miss
    runs the default. `CS.sw` has no `default` constructor, so the
    default is denoted here at the `Exec` level; the two coincidence
    lemmas below show each half is exactly `Exec (.sw …)`. -/
def SwDefExec (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR)
    (e : CX) (cases : List (Int × CS)) (dflt : CS)
    (st : CSt) (ρ : CLok) (o : COut) : Prop :=
  ∃ k st1, ev L orc fr e st ρ = some (.int k, st1) ∧
    ((∃ s o', cases.lookup k = some s ∧ Exec L orc fr CR XR s st1 ρ o' ∧
      o = o'.unbreak)
    ∨ (cases.lookup k = none ∧ Exec L orc fr CR XR dflt st1 ρ o))

/-- Hit: scrutinee, chosen arm and its run build the outcome. -/
theorem swDef_hit (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR)
    {e : CX} {cases : List (Int × CS)} {dflt : CS} {st : CSt} {ρ : CLok}
    {k : Int} {st1 : CSt} {s : CS}
    (he : ev L orc fr e st ρ = some (.int k, st1))
    (hl : cases.lookup k = some s)
    {o' : COut} (hs : Exec L orc fr CR XR s st1 ρ o') :
    SwDefExec L orc fr CR XR e cases dflt st ρ o'.unbreak :=
  ⟨k, st1, he, Or.inl ⟨s, o', hl, hs, rfl⟩⟩

/-- Miss: scrutinee, absence and the default run build the outcome. -/
theorem swDef_miss (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR)
    {e : CX} {cases : List (Int × CS)} {dflt : CS} {st : CSt} {ρ : CLok}
    {k : Int} {st1 : CSt} {o : COut}
    (he : ev L orc fr e st ρ = some (.int k, st1))
    (hl : cases.lookup k = none)
    (hd : Exec L orc fr CR XR dflt st1 ρ o) :
    SwDefExec L orc fr CR XR e cases dflt st ρ o :=
  ⟨k, st1, he, Or.inr ⟨hl, hd⟩⟩

/-- The hit half IS the emitted `switch` hit (`Exec.swHit`). -/
theorem exec_sw_hit (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR)
    {e : CX} {cases : List (Int × CS)} {st : CSt} {ρ : CLok}
    {k : Int} {st1 : CSt} {s : CS} {o' : COut}
    (he : ev L orc fr e st ρ = some (.int k, st1))
    (hl : cases.lookup k = some s)
    (hs : Exec L orc fr CR XR s st1 ρ o') :
    Exec L orc fr CR XR (.sw e cases) st ρ o'.unbreak :=
  Exec.swHit he hl hs

/-- The miss half IS the emitted `switch` fall-through
    (`Exec.swMiss`); the default runs next. -/
theorem exec_sw_miss (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR)
    {e : CX} {cases : List (Int × CS)} {st : CSt} {ρ : CLok}
    {k : Int} {st1 : CSt}
    (he : ev L orc fr e st ρ = some (.int k, st1))
    (hl : cases.lookup k = none) :
    Exec L orc fr CR XR (.sw e cases) st ρ (.norm st1 ρ) :=
  Exec.swMiss he hl

/-! ## 5. Witness on the reference fixture -/

/-- The witness arms: `0 .. 99 =>` and `100 =>` over `.int 0 100`. -/
def matchArme : List IArm := [.range 0 99 false, .exact 100]

def matchM : IntMatch := ⟨matchArme, false⟩

/-- Table-driven scrutinee: the `konto[0]` slot read. -/
def matchLeser : Expr refD [] [Res.held (D := refD) ()] (.int 0 100) :=
  .slot () () refIdxLies refDarf

/-- Before the write the slot reads `0`. -/
theorem matchLeser_start :
    (eval (refSp0.welt []) matchLeser (refSp0.welt []) Env.nil).n = 0 := rfl

/-- After the reached run's writing step the slot reads `100`. -/
theorem matchLeser_nach :
    (eval (MB.weltVon 1) matchLeser (MB.weltVon 1) Env.nil).n = 100 := rfl

/-- The arms cover `.int 0 100` exactly, checked by computation: any
    dropped arm turns this `decide` red (planted-defect check). -/
theorem match_erschoepfend : erschoepfend matchM 0 100 :=
  (erschoepfendB_richtig matchM 0 100).mp (by decide)

/-- Dispatch before the write: `0` takes the range arm. -/
theorem match_wahl_vor : wahl matchArme 0 = some 0 := rfl

/-- Dispatch after the write: `100` takes the exact arm. -/
theorem match_wahl_nach : wahl matchArme 100 = some 1 := rfl

/-- Planted defect (negative): value `1` matches neither `0` nor
    `2 .. 5` -- the gap dispatches to `none`. -/
theorem match_luecke_zeigt : wahl [.exact 0, .range 2 5 false] 1 = none := rfl

/-- Planted defect (negative): those arms do NOT cover `0 .. 5` --
    the gap is a refusal downstream, never an inserted default. -/
theorem match_nicht_erschoepfend :
    ¬ erschoepfend ⟨[.exact 0, .range 2 5 false], false⟩ 0 5 := by
  intro hcov
  obtain ⟨i, hi⟩ :=
    erschoepfend_ohne_default _ 0 5 1 hcov rfl (by decide) (by decide)
  rw [match_luecke_zeigt] at hi
  cases hi

/-- ZEUGE `match_exhaustive_zeuge`: everything jointly on the
    NON-DEGENERATE reference program -- the integer match over the
    table-driven scrutinee `matchLeser` (`konto[0]`, type
    `.int 0 100`), dispatched before the memory-changing step (`0`,
    range arm) and after it (`100`, exact arm), with the reached F run
    `refB_erreicht` (lock, writing leaf, call, return) and the memory
    move `refB_schreibt` (`konto[0]`: `0 -> 100`). -/
theorem match_exhaustive_zeuge :
    ∃ (m : IntMatch) (vVor vNach : Int),
      m.arme = matchArme ∧ m.hatDefault = false ∧
      vVor = (eval (refSp0.welt []) matchLeser (refSp0.welt []) Env.nil).n ∧
      vNach = (eval (MB.weltVon 1) matchLeser (MB.weltVon 1) Env.nil).n ∧
      erschoepfend m 0 100 ∧
      wahl m.arme vVor = some 0 ∧ wahl m.arme vNach = some 1 ∧
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
      MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨matchM, 0, 100, rfl, rfl, matchLeser_start.symm, matchLeser_nach.symm,
    match_erschoepfend, match_wahl_vor, match_wahl_nach,
    refB_erreicht, refB_schreibt⟩

/-! ## CUTS: what is not proved.

  - Lane 227's `switch` lowering is UNMERGED (wave B, after lane 221):
    the expansion `armKeys`/`fallListe` (one `case` label per covered
    value, first match wins) is this lane's denotation of what 227
    writes, read off the task's "including the default arm" plus
    `CS.sw` (no `default` constructor, every arm ends in `break`).
    If 227 ranges below stay ranges (nested `if`s) or share one arm
    body across labels, `fallListe` needs a body map and the lookup
    bridge a body-equality premise -- the denotation (`trifft`) and
    the exhaustiveness predicate (`erschoepfend`) stand unchanged.
  - No Gabbro `Stmt` for the integer match: the Lean grammar
    (`Syntax.lean`) has `onOption`/`onTag`/`onGrund` only, so the
    correspondence is stated against the scrutinee VALUE (`k : Int`)
    and `Exec (.sw …)`, not against a `StmtCorr`. A `Stmt` (and the
    `onReason` replacement lane 222's report points at) plugs the
    value-level lemmas in unchanged.
  - The default arm has a denotation (`SwDefExec`, hit/miss) but no
    emitted syntax: `CS.sw` cannot write `default:`, so a `default:`
    in 227's output is denoted by the miss disjunct, not by a
    constructor. If 227 omits `default:` on proved-exhaustive matches
    (the tagged-`switch` precedent, `-Wswitch` as second reader),
    the miss disjunct is dead code under `erschoepfend_ohne_default`.
  - Overlap and order are out of scope: overlapping arms dispatch to
    the FIRST match (C `switch` order); the checker may still refuse
    overlaps (dead arms) -- refused, never reordered.
  - The scrutinee's range comes from its TYPE (`.int lo hi`,
    G1 `einpassen_voll`): a scrutinee whose type range exceeds the
    arms' coverage is refused by `erschoepfendB`, never narrowed.
-/

#print axioms Gabbro.Grammatik.exact_trifft
#print axioms Gabbro.Grammatik.range_incl_trifft
#print axioms Gabbro.Grammatik.range_excl_trifft
#print axioms Gabbro.Grammatik.mem_aufzaehlung
#print axioms Gabbro.Grammatik.mem_armKeys_exact
#print axioms Gabbro.Grammatik.mem_armKeys_incl
#print axioms Gabbro.Grammatik.mem_armKeys_excl
#print axioms Gabbro.Grammatik.trifft_mem_armKeys
#print axioms Gabbro.Grammatik.lookup_mem_isSome
#print axioms Gabbro.Grammatik.mem_fallListeAux_of
#print axioms Gabbro.Grammatik.trifft_wahl_some
#print axioms Gabbro.Grammatik.wahl_none_weigert
#print axioms Gabbro.Grammatik.mem_werteListe
#print axioms Gabbro.Grammatik.erschoepfendB_richtig
#print axioms Gabbro.Grammatik.erschoepfend_kein_fehlschlag
#print axioms Gabbro.Grammatik.erschoepfend_ohne_default
#print axioms Gabbro.Grammatik.swDef_hit
#print axioms Gabbro.Grammatik.swDef_miss
#print axioms Gabbro.Grammatik.exec_sw_hit
#print axioms Gabbro.Grammatik.exec_sw_miss
#print axioms Gabbro.Grammatik.matchLeser_start
#print axioms Gabbro.Grammatik.matchLeser_nach
#print axioms Gabbro.Grammatik.match_erschoepfend
#print axioms Gabbro.Grammatik.match_wahl_vor
#print axioms Gabbro.Grammatik.match_wahl_nach
#print axioms Gabbro.Grammatik.match_luecke_zeigt
#print axioms Gabbro.Grammatik.match_nicht_erschoepfend
#print axioms Gabbro.Grammatik.match_exhaustive_zeuge

end Gabbro.Grammatik
