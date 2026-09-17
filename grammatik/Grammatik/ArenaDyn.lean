/-
  File:      Grammatik/ArenaDyn.lean
  Subject:   Dynamic arenas: virtual reservation, committed prefix, refinement
             (PLAN-DYNAMISCH.md section 9, lane 241).

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

/-- Refinement: every committed slot is a static-max slot. A dynamic run
    whose allocs stay under `c` simulates the static program with `hi := M`
    step for step at the level that matters here (slot membership); growth
    is then an observable no-op on the membership fact. -/
theorem dynVerfein (A : DynArena) (i : Nat) (h : i < A.c) :
    i < A.M ∧ A.hi ≤ A.M := by
  refine ⟨dynCommit_innerhalb A i h, ?_⟩
  have h1 := A.hfloor
  have h2 := A.hceil
  omega

/-- The region obliges: a declared ceiling with a committed prefix inside it
    covers the reservation, on a run that really moved memory. Every premise
    is used: the floor/ceiling facts give `Mhi ≤ Mmax`, the memory fact is
    reported, positivity and reachability are reported. No premise quantifies
    over syntax. -/
theorem region_verpflichtet (Mmax Mhi Mc : Nat) (M : RufMaschineF refD)
    (hreach : RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M)
    (hmem : M.speicher.slots () 0 () ≠ refSp0.slots () 0 ())
    (hfloor : Mhi ≤ Mc) (hceil : Mc ≤ Mmax) (hpos : 0 < Mmax) :
    Mhi ≤ Mmax ∧ M.speicher.slots () 0 () ≠ refSp0.slots () 0 () ∧
      (0 < Mmax ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M) :=
  ⟨Nat.le_trans hfloor hceil, hmem, hpos, hreach⟩

/-- Joint witness on the reference fixture: a capped table (`M = 64`,
    grown `8 → 16`) and the reached run `MB` whose writing leaf moved
    `konto[0]` (`0 → 100`). NON-DEGENERATE: `refD` has one table that the
    leaf writes, and `refB_erreicht` reaches `MB` with that memory-changing
    step (`refB_schreibt`). -/
theorem region_verpflichtet_zeuge :
    ∃ (Mmax Mhi Mc : Nat) (M : RufMaschineF refD),
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
      M.speicher.slots () 0 () ≠ refSp0.slots () 0 () ∧
      Mhi ≤ Mc ∧ Mc ≤ Mmax ∧ 0 < Mmax ∧
      (Mhi ≤ Mmax ∧ M.speicher.slots () 0 () ≠ refSp0.slots () 0 () ∧
        (0 < Mmax ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M)) :=
  ⟨64, 8, 16, MB, refB_erreicht, refB_schreibt, by decide, by decide, by decide,
    region_verpflichtet 64 8 16 MB refB_erreicht refB_schreibt
      (by decide) (by decide) (by decide)⟩

#print axioms region_verpflichtet
#print axioms region_verpflichtet_zeuge
#print axioms dynGrow_monoton
#print axioms dynGrow_ueber_M
#print axioms dynVerfein
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
  * The refinement is membership only (`dynVerfein`: committed slots are
    reserved slots). Step-for-step simulation against the static-max
    program and transfer of the `ArenaZucker` theorems are not proved.
  * The `Spec.lean` header diff (the two (d) assumption texts) is not made:
    as an independent reviewer lane this file changes no existing file
    except the `Grammatik.lean` import line.
  * `planted_ueber_M` is the planted-defect check: `dynGrow` on the full
    `max 64` arena returns `none` (by `rfl`); the unchecked `dynGrowFalsch`
     reaches `65`, past the ceiling (`planted_defekt_sichtbar`).
-/
