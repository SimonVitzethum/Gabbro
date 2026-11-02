module

public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Bausteine.Arena.ArenaZucker

@[expose] public section



namespace Gabbro.Grammatik.ArenaDyn

/-- A dynamic arena: ceiling `M`, commit floor `hi`, committed prefix `c`. -/
structure DynArena where
  M : Nat
  hi : Nat
  c : Nat
  hfloor : hi ≤ c
  hceil : c ≤ M
  hpos : 0 < M

/-- Explicit commit: `grow by n` bumps the prefix, capped refusal beyond `M`.
    Below `M` the runtime may still fail (out of memory is real); that `else`
    is the program's, not modelled here. Beyond `M` there is no branch. -/
def dynGrow (A : DynArena) (n : Nat) : Option DynArena :=
  if h : A.c + n ≤ A.M then
    some ⟨A.M, A.hi, A.c + n, Nat.le_trans A.hfloor (Nat.le_add_right _ _), h, A.hpos⟩
  else none

/-- Commit never shrinks: a successful `grow` keeps the old prefix. -/
theorem dynGrow_monoton (A : DynArena) (n : Nat) (B : DynArena)
    (h : dynGrow A n = some B) : A.c ≤ B.c := by
  unfold dynGrow at h
  split at h
  · cases h
    exact Nat.le_add_right _ _
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- The committed prefix is usable storage: every committed slot is reserved. -/
theorem dynCommit_innerhalb (A : DynArena) (i : Nat) (h : i < A.c) : i < A.M := by
  have := A.hceil
  omega

/-- Over-ceiling commit is a refusal: `grow` past `M` returns `none`. -/
theorem dynGrow_ueber_M (A : DynArena) (n : Nat) (h : A.M < A.c + n) :
    dynGrow A n = none := by
  unfold dynGrow
  split
  · omega
  · rfl

/-- Success is exactly the bound: `grow` answers iff the bump stays in `M`. -/
theorem dynGrow_isSome (A : DynArena) (n : Nat) :
    (dynGrow A n ≠ none) ↔ A.c + n ≤ A.M := by
  unfold dynGrow
  by_cases h : A.c + n ≤ A.M
  · rw [dif_pos h]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, h]
  · rw [dif_neg h]
    simp only [ne_eq, not_true_eq_false, h]

/-- The model arena: `used` is the committed prefix, the bound is the
    ceiling. This is the anchor lane 244's simulation builds on: one
    `grow by 1` is one `Arena.alloc` on `Kap ⟨hi, M⟩`. -/
def arenaModell (A : DynArena) : Arena.Arena ⟨A.hi, A.M⟩ 0 :=
  ⟨A.c, A.hceil⟩

/-- One-slot commit succeeds exactly when the monotone model allocates:
    `dynGrow A 1` and `Arena.alloc` on `Kap ⟨hi, M⟩` agree. Proved from
    `dynGrow_isSome` and the `alloc_erfolg` / `alloc_fehlschlag` pair --
    the `ArenaZucker` transfer target in miniature. -/
theorem dynGrow1_gdw_alloc (A : DynArena) :
    (dynGrow A 1 ≠ none) ↔ Arena.alloc (arenaModell A) ≠ none := by
  rw [dynGrow_isSome]
  constructor
  · intro h
    have hlt : (arenaModell A).used < (⟨A.hi, A.M⟩ : Arena.Kap).hi := by
      show A.c < A.M
      omega
    have he := Arena.alloc_erfolg (arenaModell A) hlt
    rw [he]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · intro h
    by_cases hlt : A.c < A.M
    · omega
    · have hnn : ¬ (arenaModell A).used < (⟨A.hi, A.M⟩ : Arena.Kap).hi := hlt
      exact absurd (Arena.alloc_fehlschlag (arenaModell A) hnn) h

/-- The planted-defect probe: a full `max 64` arena asked to grow fails red.
    An unchecked variant (no `M` guard) would return `some` here; the guard
    is what makes this `none`. Evaluated by `rfl`: the failure line is this
    theorem's statement. -/
def arena64volle : DynArena := ⟨64, 8, 64, by decide, by decide, by decide⟩

theorem planted_ueber_M : dynGrow arena64volle 1 = none := by rfl

/-- Unchecked commit: bumps without consulting `M` (the defect), as raw data. -/
structure DynRoh where
  M : Nat
  hi : Nat
  c : Nat

def dynGrowFalsch (A : DynArena) (n : Nat) : DynRoh := ⟨A.M, A.hi, A.c + n⟩

/-- The defect is visible: the unchecked bump reaches 65 past `M = 64`. -/
theorem planted_defekt_sichtbar : (dynGrowFalsch arena64volle 1).c = 65 := by rfl

/-- Grow cost: `1 + n * faultKosten`. The per-slot commit cost is READ from
    the named hardware assumption (Spec premise (c) latency entry), never
    justified here: it is a function argument, not a proved bound. -/
def growKosten (n faultKosten : Nat) : Nat := 1 + n * faultKosten

theorem growKosten_pos (n faultKosten : Nat) : 0 < growKosten n faultKosten := by
  unfold growKosten
  omega

/-! ### The commit sequence of a run (fix lane F2, review G08 F1/F4)

  The runtime never gives a committed page back (`reset` leaves `committed`
  alone), so over one load the `grow`s of the whole run form ONE sequence of
  amounts, folded through `dynGrow`; a `none` anywhere in the fold is the
  runtime's past-ceiling stop (`abort` in `laufzeit/arena_dyn.c`). The two
  theorems below are the model half of the checker rule `N426` since fix
  lane F2: the stop is avoided on EVERY run exactly when the upper bound of
  the total commit stays within `M - c` -- and a per-path LOWER bound (the
  reading before the fix) is not enough, as the witness shows with two
  commits that each fit alone. -/

/-- Fold a run's commit sequence through `dynGrow`: `none` is the stop. -/
def dynGrowListe (A : DynArena) : List Nat → Option DynArena
  | [] => some A
  | n :: ns =>
    match dynGrow A n with
    | none => none
    | some B => dynGrowListe B ns

/-- One commit inside the ceiling succeeds and moves the prefix by `n`. -/
theorem dynGrow_some (A : DynArena) (n : Nat) (h : A.c + n ≤ A.M) :
    ∃ B, dynGrow A n = some B ∧ B.c = A.c + n ∧ B.M = A.M := by
  refine ⟨⟨A.M, A.hi, A.c + n, Nat.le_trans A.hfloor (Nat.le_add_right _ _), h, A.hpos⟩,
    ?_, rfl, rfl⟩
  unfold dynGrow
  rw [dif_pos h]

/-- **The upper bound suffices:** a commit sequence whose total stays within
    the room above the prefix never reaches the stop, and ends at the prefix
    plus the total. -/
theorem dynGrowListe_gelingt :
    ∀ (ns : List Nat) (A : DynArena), A.c + ns.sum ≤ A.M →
      ∃ B, dynGrowListe A ns = some B ∧ B.c = A.c + ns.sum := by
  intro ns
  induction ns with
  | nil =>
    intro A _
    exact ⟨A, rfl, by simp only [List.sum_nil, Nat.add_zero]⟩
  | cons n ns ih =>
    intro A h
    rw [List.sum_cons] at h
    obtain ⟨B, hB, hc, hM⟩ := dynGrow_some A n (by omega)
    obtain ⟨C, hC, hcC⟩ := ih B (by omega)
    refine ⟨C, ?_, ?_⟩
    · show (match dynGrow A n with
            | none => none
            | some B => dynGrowListe B ns) = some C
      rw [hB]
      exact hC
    · rw [List.sum_cons]
      omega

/-- **And it is necessary:** a commit sequence whose total passes the room
    above the prefix reaches the stop, whatever its order. -/
theorem dynGrowListe_scheitert :
    ∀ (ns : List Nat) (A : DynArena), A.M < A.c + ns.sum →
      dynGrowListe A ns = none := by
  intro ns
  induction ns with
  | nil =>
    intro A h
    have := A.hceil
    simp only [List.sum_nil, Nat.add_zero] at h
    omega
  | cons n ns ih =>
    intro A h
    rw [List.sum_cons] at h
    show (match dynGrow A n with
          | none => none
          | some B => dynGrowListe B ns) = none
    by_cases hn : A.c + n ≤ A.M
    · obtain ⟨B, hB, hc, hM⟩ := dynGrow_some A n hn
      rw [hB]
      exact ih B (by omega)
    · rw [dynGrow_ueber_M A n (by omega)]

/-- The floor-`8` arena under `max 16`: the shape of `beispiele/gift/1133`
    and `/1135`. -/
def Az16 : DynArena := ⟨16, 8, 8, by decide, by decide, by decide⟩

/-- The same floor under `max 24`: the positive twins in `paesse.rs`. -/
def Az24 : DynArena := ⟨24, 8, 8, by decide, by decide, by decide⟩

/-- Witness for `dynGrowListe_gelingt`, non-degenerate: a real two-commit
    sequence (`8, 8`, total `16 > 0`) under `max 24` reaches `24`. -/
theorem dynGrowListe_gelingt_zeuge :
    ∃ (A : DynArena) (ns : List Nat) (B : DynArena),
      0 < ns.sum ∧ A.c + ns.sum ≤ A.M ∧
      dynGrowListe A ns = some B ∧ B.c = A.c + ns.sum :=
  let ⟨B, hB, hc⟩ := dynGrowListe_gelingt [8, 8] Az24 (by decide)
  ⟨Az24, [8, 8], B, by decide, by decide, hB, hc⟩

/-- Witness for `dynGrowListe_scheitert`, and the reason the lower-bound
    reading was wrong: under `max 16` EACH of the two commits fits the room
    alone (`8 + 8 <= 16`, what a per-path check of one `grow` saw), yet the
    run reaches the stop. -/
theorem dynGrowListe_scheitert_zeuge :
    ∃ (A : DynArena) (ns : List Nat),
      (∀ n, n ∈ ns → A.c + n ≤ A.M) ∧ A.M < A.c + ns.sum ∧
      dynGrowListe A ns = none :=
  ⟨Az16, [8, 8], by decide, by decide, dynGrowListe_scheitert [8, 8] Az16 (by decide)⟩

/-- Both directions evaluated on the fixtures (`rfl`, no lemma between). -/
theorem dynGrowListe_zwilling :
    (dynGrowListe Az24 [8, 8]).isSome = true ∧ dynGrowListe Az16 [8, 8] = none :=
  ⟨rfl, rfl⟩

/-! ### The dynamic arena AS A FORM (PLAN-DYNAMIC section 9, server lane 2026-09-28)

end Gabbro.Grammatik.ArenaDyn
