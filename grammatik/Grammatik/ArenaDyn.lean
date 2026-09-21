/-
  File:      Grammatik/ArenaDyn.lean
  Subject:   Dynamic arenas: virtual reservation, committed prefix, and the
             past-ceiling stop over a run's commit sequence
             (PLAN-DYNAMISCH.md section 9, lane 241; reworked by fix lane F2
             after review G08 F4, 2026-09-21).

  A dynamic arena declares a static ceiling `M` (address reserved, never
  touched implicitly) and a committed prefix `c` (`hi <= c <= M`) grown
  explicitly by `grow`. Commit is monotone within a run; growth beyond `M`
  is a refusal, never a runtime surprise. Fault latency/cost arrives as a
  NAMED hardware assumption read as data (`faultKosten`), never justified
  here. The C plug-in point is `CSpeicher.lean` (read-only): the virtual
  region is the arena block's `Fin M` index set, the committed prefix the
  `Fin c` usable part; nothing here edits that file.
-/
import Grammatik.ReferenzB
import Grammatik.ArenaZucker

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
  · exact absurd h (by simp)

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
    simp [h]
  · rw [dif_neg h]
    simp [h]

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
    simp
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

theorem planted_ueber_M : dynGrow arena64volle 1 = none := rfl

/-- Unchecked commit: bumps without consulting `M` (the defect), as raw data. -/
structure DynRoh where
  M : Nat
  hi : Nat
  c : Nat

def dynGrowFalsch (A : DynArena) (n : Nat) : DynRoh := ⟨A.M, A.hi, A.c + n⟩

/-- The defect is visible: the unchecked bump reaches 65 past `M = 64`. -/
theorem planted_defekt_sichtbar : (dynGrowFalsch arena64volle 1).c = 65 := rfl

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
    exact ⟨A, rfl, by simp⟩
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
    simp at h
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

#print axioms dynGrowListe_gelingt
#print axioms dynGrowListe_scheitert
#print axioms dynGrowListe_gelingt_zeuge
#print axioms dynGrowListe_scheitert_zeuge
#print axioms dynGrowListe_zwilling
#print axioms dynGrow_monoton
#print axioms dynGrow_ueber_M
#print axioms dynGrow_isSome
#print axioms dynGrow1_gdw_alloc
#print axioms planted_ueber_M
#print axioms planted_defekt_sichtbar
#print axioms growKosten_pos

end Gabbro.Grammatik.ArenaDyn

/-! CUTS -- what this file does NOT claim.

  * No checker rule is built here: R-max / R-commit / R-grow-else /
    R-grow-const / R-grow-form (PLAN-DYNAMISCH section 4) are lane 240/241
    Rust work; this file is the Lean model half (section 9) only.
  * No emitter or runtime is built: the descriptor (`base`, `committed`),
    `gabbro_arena_reserve` / `gabbro_arena_grow`, and the OS-token guardian
    are lane 242 work; the `_Static_assert` pins are not stated here.
  * No cost arm is built: `growKosten` reads the per-slot commit cost as
    DATA from the named hardware assumption (Spec premise (c) latency
    entry); the `K003` wiring and the `K002`-falls probe are lane 243 work.
  * **No refinement is claimed** (review G08 F4, fix lane F2). `DynArena` is
    a Nat record that carries `c <= M` as a field; a membership fact over it
    (the former `dynVerfein`, "committed slots are reserved slots") restates
    that field, and the former `region_verpflichtet` tied it to a run only
    through a premise its witness discharged without looking at the run
    (the lane-147 pattern). Both are REMOVED, not renamed. What stands in
    their place is a statement about the one runtime fact this record does
    model -- the past-ceiling stop -- over a whole commit sequence
    (`dynGrowListe_gelingt` / `_scheitert`, with non-degenerate witnesses):
    the model half of `N426`'s upper-bound rule. Nothing links `DynArena` to
    the Rust checker's per-path accounting or to the C runtime by proof; the
    link is by name (`N426`, `gabbro_arena_grow`'s ceiling test) only.
    Proved as the linkage anchor to the static model: `dynGrow_isSome`
    (success is exactly the bound) and `dynGrow1_gdw_alloc` (one-slot commit
    agrees with `Arena.alloc` on `Kap ⟨hi, M⟩` via `arenaModell`, from the
    `alloc_erfolg` / `alloc_fehlschlag` pair). What is still missing for
    PLAN-DYNAMISCH section 9: `DynForm` over `ArenaForm D` (table
    `count = M` plus the committed prefix as a second `stand`-style word),
    the four section-9 theorems in full Block form (`dynGrow_commit` with
    the `exec_rahmen` frame lemma, `dynAlloc_unter_commit`,
    `dynAlloc_ueber_commit`; `dynCommit_monoton` is `dynGrow_monoton`),
    and the simulation statement. Blockers, measured: the alloc pair needs
    new narrow-on-committed sugar (a `Block` construction with `Expr.umTyp`
    casts in the style of `Block.arenaAlloc`, estimated 40-80 lines of
    dependent plumbing each); the simulation needs the static-max program
    shape, which is lane 244's scope. Tracked for lane 244; until then
    every dynamic use site re-proves its membership fact instead of citing
    transfer (model-only cost, zero runtime bytes).
  * The `Spec.lean` header diff (the two (d) assumption texts) is not made:
    as an independent reviewer lane this file changes no existing file
    except the `Grammatik.lean` import line.
  * `planted_ueber_M` is the planted-defect check: `dynGrow` on the full
    `max 64` arena returns `none` (by `rfl`); the unchecked `dynGrowFalsch`
     reaches `65`, past the ceiling (`planted_defekt_sichtbar`).
-/
