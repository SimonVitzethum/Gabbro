/-
  File:      Grammatik/CFormMatch.lean
  Subject:   Integer-match semantics: exhaustiveness over ranges (lane 228).

  Lane 222 added integer arms (`3 =>`, `0 .. 255 =>`, `0 ..< 256 =>`);
  lane 227 lowers them to a C `switch` WITHOUT `default` (merged). This
  file denotes the arms (`trifft`), their `case` labels (`armKeys`,
  `fallListe`, first match), and exhaustiveness (`erschoepfend`, decided
  by `erschoepfendB`).

  WHAT IS TIED TO WHAT (review G07 F3, corrected by fix lane F1,
  2026-09-21):
  - The Rust checker refuses a non-exhaustive integer match since fix
    lane F1 (`N411`, `crates/gabbro-check/src/intmatch.rs`). It decides
    `erschoepfend ⟨arms, false⟩ lo hi` with `lo .. hi` = M1's range of
    the scrutinee, by an interval sweep, NOT by running `erschoepfendB`.
    That the sweep computes this predicate is read, not proved.
  - §4b ties `fallListe` to a `CS.sw` whose cases are built from it
    (`swFaelle`): under `erschoepfend`, every run of that `switch` on a
    value in range takes the chosen arm (`sw_erschoepfend_trifft`), and
    a miss is impossible. That lane 227's `emit.rs` writes exactly
    `swFaelle arms rumpf` is read off the emitter, not proved (the chain
    from `emit.rs` to `CS` is the translation-validation work).
  - The range `lo .. hi` is the scrutinee's range as M1 knows it (its
    declared `.int lo hi`, G1 `einpassen_voll`, narrowed by flow facts);
    that the scrutinee's value lies in it is a premise here.
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

/-- The decidable coverage check. The Rust checker (`N411`, fix lane
    F1) decides the same predicate by an interval sweep instead of this
    enumeration; the agreement is by reading. -/
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

/-- Exhaustiveness leaves no value without an arm or the default
    (the rule `N411` enforces: a missing arm is a refusal, never an
    inserted default). -/
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

/-! ## 4. The two `Exec` halves of a `switch`

  `swDef_hit`/`swDef_miss` denote a `switch` WITH a default, which the
  emitter never writes; `exec_sw_hit`/`exec_sw_miss` restate the two
  `Exec` constructors. The statement about the emitted form is §4b. -/

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

/-! ## 4b. The `switch` built from the case table

  `swFaelle arms rumpf` is the `cases` list of `CS.sw`: every label of
  `fallListe arms` with the body of its arm (lane 227 stacks the labels
  of arm `i` in front of body `i`). -/

/-- The `cases` of the `switch` for `arms`, arm `i` running `rumpf i`. -/
def swFaelle (arms : List IArm) (rumpf : Nat → CS) : List (Int × CS) :=
  (fallListe arms).map (fun p => (p.1, rumpf p.2))

/-- Mapping the arm index to its body commutes with the lookup. -/
theorem lookup_map_snd (l : List (Int × Nat)) (f : Nat → CS) (x : Int) :
    (l.map (fun p => (p.1, f p.2))).lookup x = (l.lookup x).map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    cases h : (x == a) with
    | true => simp only [List.map, List.lookup, h, Option.map_some]
    | false => simp only [List.map, List.lookup, h]; exact ih

/-- The `switch` dispatches exactly as `wahl`. -/
theorem swFaelle_lookup (arms : List IArm) (rumpf : Nat → CS) (x : Int) :
    (swFaelle arms rumpf).lookup x = (wahl arms x).map rumpf :=
  lookup_map_snd _ rumpf x

/-- **No miss under coverage.** For arms that cover `lo .. hi` with no
    default, every run of the `switch` built from them, on a scrutinee
    value in range, runs the chosen arm's body; the `swMiss` path (the
    statement skipped) is impossible. This is what `N411` buys. -/
theorem sw_erschoepfend_trifft (L : CLayout) (orc : DevOrc) (fr : Nat)
    (CR XR : CCallR) {arms : List IArm} {rumpf : Nat → CS} {lo hi : Int}
    {e : CX} {st : CSt} {ρ : CLok} {k : Int} {st1 : CSt} {o : COut}
    (hcov : erschoepfend ⟨arms, false⟩ lo hi)
    (he : ev L orc fr e st ρ = some (.int k, st1))
    (hlo : lo ≤ k) (hhi : k ≤ hi)
    (hx : Exec L orc fr CR XR (.sw e (swFaelle arms rumpf)) st ρ o) :
    ∃ i o', wahl arms k = some i ∧ Exec L orc fr CR XR (rumpf i) st1 ρ o' ∧
      o = o'.unbreak := by
  obtain ⟨i, hi⟩ := erschoepfend_ohne_default ⟨arms, false⟩ lo hi k hcov rfl hlo hhi
  have hl : (swFaelle arms rumpf).lookup k = some (rumpf i) := by
    rw [swFaelle_lookup, hi]; rfl
  cases hx with
  | swHit he' hl' h =>
    rw [he] at he'
    injection he' with he1
    injection he1 with hk hst
    injection hk with hk
    subst hk; subst hst
    rw [hl] at hl'
    injection hl' with hs
    subst hs
    exact ⟨i, _, hi, h, rfl⟩
  | swMiss he' hl' =>
    rw [he] at he'
    injection he' with he1
    injection he1 with hk _
    injection hk with hk
    subst hk
    rw [hl] at hl'
    cases hl'

/-- **The miss is real without coverage** (planted defect): the arms
    `0`, `2 .. 5` and a scrutinee evaluating to `1` -- the `switch` built
    from them skips (`swMiss`), the run `N411` refuses. -/
theorem sw_luecke_ueberspringt (L : CLayout) (orc : DevOrc) (fr : Nat)
    (CR XR : CCallR) (rumpf : Nat → CS) (st : CSt) (ρ : CLok) :
    Exec L orc fr CR XR
      (.sw (.lit 1) (swFaelle [.exact 0, .range 2 5 false] rumpf)) st ρ (.norm st ρ) := by
  refine Exec.swMiss (k := 1) rfl ?_
  rw [swFaelle_lookup]
  rfl

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

/-- The witness arm bodies: arm `i` evaluates the literal `i` (distinct
    per arm, so which body ran is visible). -/
def rumpfZ (i : Nat) : CS := .expr (.lit i)

/-- ZEUGE `match_exhaustive_zeuge`: the integer match over the
    table-driven scrutinee `matchLeser` (`konto[0]`, type `.int 0 100`
    on the reference fixture) -- dispatched before the memory-changing
    step (`0`, range arm) and after it (`100`, exact arm) -- and the
    `switch` built from the same arms (`swFaelle`) on the value read
    after the step: it HAS a run, and EVERY run of it executes arm 1's
    body (no miss, `sw_erschoepfend_trifft`). Not claimed (review G07
    F3): the `switch` scrutinee is the literal of the value the fixture
    read, not the emitted load of `konto[0]`; the reached run of the
    fixture program (which contains no `match`) is no longer a conjunct,
    it was decorative. -/
theorem match_exhaustive_zeuge :
    ∃ (m : IntMatch) (vVor vNach : Int),
      m.arme = matchArme ∧ m.hatDefault = false ∧
      vVor = (eval (refSp0.welt []) matchLeser (refSp0.welt []) Env.nil).n ∧
      vNach = (eval (MB.weltVon 1) matchLeser (MB.weltVon 1) Env.nil).n ∧
      erschoepfend m 0 100 ∧
      wahl m.arme vVor = some 0 ∧ wahl m.arme vNach = some 1 ∧
      (∀ (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR) (st : CSt) (ρ : CLok),
        Exec L orc fr CR XR (.sw (.lit vNach) (swFaelle m.arme rumpfZ)) st ρ (.norm st ρ)) ∧
      (∀ (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR) (st : CSt) (ρ : CLok)
          (o : COut),
        Exec L orc fr CR XR (.sw (.lit vNach) (swFaelle m.arme rumpfZ)) st ρ o →
        ∃ o', Exec L orc fr CR XR (rumpfZ 1) st ρ o' ∧ o = o'.unbreak) := by
  refine ⟨matchM, 0, 100, rfl, rfl, matchLeser_start.symm, matchLeser_nach.symm,
    match_erschoepfend, match_wahl_vor, match_wahl_nach, ?_, ?_⟩
  · intro L orc fr CR XR st ρ
    have hl : (swFaelle matchArme rumpfZ).lookup 100 = some (rumpfZ 1) := by
      rw [swFaelle_lookup, match_wahl_nach]; rfl
    exact @Exec.swHit L orc fr CR XR (.lit 100) (swFaelle matchArme rumpfZ) st ρ 100 st
      (rumpfZ 1) (.norm st ρ) rfl hl (Exec.expr rfl)
  · intro L orc fr CR XR st ρ o hx
    obtain ⟨i, o', hi, hr, ho⟩ :=
      sw_erschoepfend_trifft L orc fr CR XR (arms := matchArme) (lo := 0) (hi := 100)
        match_erschoepfend rfl (by decide) (by decide) hx
    rw [match_wahl_nach] at hi
    injection hi with hi
    subst hi
    exact ⟨o', hr, ho⟩

/-! ## CUTS: what is not proved.

  - Review G07 (2026-09-21), read against master after both merges:
    lane 227 IS merged. It writes one `case` per covered value (as
    `fallListe` assumes), refuses duplicate values (so first-match
    never decides anything), and writes NO `default:` on ANY integer
    match. Since fix lane F1 the Rust checker refuses a non-exhaustive
    integer match (`N411`, interval sweep over M1's range -- the same
    predicate as `erschoepfendB`, by reading), overlaps and empty arms
    (`N412`), labels outside the storage type (`N413`) and non-integer
    scrutinees (`N414`). §4b ties `fallListe` to a `CS.sw` built from
    it (`swFaelle`); that `emit.rs` writes exactly that list is read,
    not proved. `exec_sw_hit`/`exec_sw_miss` still only restate the two
    `Exec` constructors.

  - Lane 227 (merged) stacks the labels of a range arm in front of ONE
    shared body; `swFaelle` denotes that by mapping every label of arm
    `i` to the same `rumpf i` (a C `case` list with stacked labels and
    one `{ … } break;` is the same dispatch as one case per label with
    equal bodies -- read, not proved against the C grammar).
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
  - The scrutinee's range is what M1 knows at the `match`: its type
    (`.int lo hi`, G1 `einpassen_voll`) narrowed by flow facts. A
    scrutinee whose range exceeds the arms' coverage is refused by
    `N411`, never narrowed by the match. Here the range is a premise
    (`hlo`, `hhi` of `sw_erschoepfend_trifft`).
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
#print axioms Gabbro.Grammatik.lookup_map_snd
#print axioms Gabbro.Grammatik.swFaelle_lookup
#print axioms Gabbro.Grammatik.sw_erschoepfend_trifft
#print axioms Gabbro.Grammatik.sw_luecke_ueberspringt
#print axioms Gabbro.Grammatik.matchLeser_start
#print axioms Gabbro.Grammatik.matchLeser_nach
#print axioms Gabbro.Grammatik.match_erschoepfend
#print axioms Gabbro.Grammatik.match_wahl_vor
#print axioms Gabbro.Grammatik.match_wahl_nach
#print axioms Gabbro.Grammatik.match_luecke_zeigt
#print axioms Gabbro.Grammatik.match_nicht_erschoepfend
#print axioms Gabbro.Grammatik.match_exhaustive_zeuge

end Gabbro.Grammatik
