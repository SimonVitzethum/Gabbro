/-
  Audit 46, probe F2: `LockSchrittGedeckt` (non-Bei) is dead code.

  Claim (pattern b-adjacent, filed as low severity): `LockSchrittGedeckt`
  (KetteMehrfadenC.lean:105-107) is defined but never referenced in any proof
  term -- not in its own file (every use site says `LockSchrittGedecktBei`),
  not anywhere else in the tree (tree-wide grep for the exact word finds only
  the definition line, its docstring mention, and the lane-11 report).
  Its content is the Bei-shape plus one membership conjunction, by definition
  (shown below as `Iff.rfl`). Deadness itself is grep evidence, cited here;
  the Lean below pins the shape so the claim is checkable.

  No rule-4 violation: every binder below appears in the stated goal.
-/
import Grammatik.KetteMehrfadenC

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `LockSchrittGedeckt` adds exactly one membership conjunction to
    `LockSchrittGedecktBei`, by definition. -/
example (prog : PCProg D) (M : GenMaschine D) (pc : PCStand) (mem : List Faden)
    (M' : GenMaschine D) (pc' : PCStand) :
    LockSchrittGedeckt prog M pc mem M' pc' ↔
      ∃ f0 : Faden, f0 ∈ mem ∧ LockSchrittGedecktBei prog M pc f0 M' pc' :=
  Iff.rfl

#check @Gabbro.Grammatik.LockSchrittGedeckt
#check @Gabbro.Grammatik.LockSchrittGedecktBei

/-
CUTS:
- Deadness rests on tree-wide grep (exact word `LockSchrittGedeckt`, excluding
  `LockSchrittGedecktBei`): hits are the definition line, one docstring line,
  and `messung/muse/MUSE-REPORT-11.md`. No proof term references it.
- No claim is made that the Bei-form is dead: it is used at every routing site
  (`kette_zwei_aus_lauf` lines 821/841, `kette_zwei_schritt` premise line 299).
-/
#print axioms Gabbro.Grammatik.LockSchrittGedeckt
