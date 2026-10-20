/-
  File:      Grammatik/ArenaSperreWachsZeuge.lean
  Subject:   WITNESSES FOR `grow` AS A LOCKED COMMIT (PLAN-DYNAMIC.md section 8a.2) on the shared arena of
             `ArenaSperreWelt.lean`, with the committed word moved below the ceiling (`komm = 2`, ceiling `4`):

    * `grow_zeuge_L`        -- a commit by `1` moves the committed word `2 -> 3`, the arena invariant holds before and
                               after, every liveness and the counter are as before (`grow_atomar` on a real world; the
                               list `2 -> 0` and the free list `[1]` are non-empty, so nothing is vacuous);
    * `grow_ueber_decke`    -- a commit past the ceiling is refused by the guard (`2 + 3 > 4`): the `else` branch runs;
    * `wachs_negativ_schrumpft` -- WHY `Erk.wachs` DEMANDS `0 ≤ n` (repaired in this step; before, it accepted any `n`): the
                               model's `grow` itself accepts a NEGATIVE `n` and then SHRINKS the committed word (`2 -> 1`);
                               the surface forbids it (`n >= 1`, `R-grow-const`). It does not touch the arena invariant
                               (`grow_atomar` holds for every `n`), but it would break a commit bound `stand <= komSt`.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreZeuge
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreWachs

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace SperreZeuge

open InvDynZeuge

/-- The scenario world with the committed word at `2`, below the ceiling `4`. -/
def w0K : World FDL := { w0L with globs := fun g => if g = 1 then zc 2 else w0L.globs g }

theorem komSt_w0K : FAL.komSt w0K = 2 := rfl

theorem stand_w0K : FAL.stand w0K = 4 := rfl

/-- The arena invariant does not read the committed word, so the scenario still meets it. -/
theorem ok_w0K : KLL.Ok w0K :=
  Dekl.ok_gleich_wort (K := KLL) (σ := w0L) (σ' := w0K) rfl
    (fun g hg => by
      have := Dekl.lesGlobs_ne_komm hg
      have h1 : ¬ g = 1 := this
      show w0K.globs g = w0L.globs g
      simp [w0K, h1]) ok_w0L

/-- **A commit by one, on the real world.** -/
theorem grow_zeuge_L (Λ : List (Res FDL)) :
    ∃ (h0 : 0 ≤ FAL.komSt w0K + 1) (h : FAL.komSt w0K + 1 ≤ FDL.count FAL.tab),
      FAL.komSt (nachGrow FAL.toDynForm 1 Λ w0K h0 h) = 3 ∧ KLL.Ok (nachGrow FAL.toDynForm 1 Λ w0K h0 h) ∧
      FAL.stand (nachGrow FAL.toDynForm 1 Λ w0K h0 h) = 4 := by
  have h0 : 0 ≤ FAL.komSt w0K + 1 := by rw [komSt_w0K]; decide
  have h : FAL.komSt w0K + 1 ≤ FDL.count FAL.tab := by rw [komSt_w0K]; decide
  obtain ⟨hok, -, hs, hk⟩ := grow_atomar (K := KLL) 1 Λ w0K h0 h
  refine ⟨h0, h, ?_, hok.mpr ok_w0K, ?_⟩
  · rw [hk, komSt_w0K]; rfl
  · rw [hs, stand_w0K]

/-- **A commit past the ceiling is refused:** `2 + 3 > 4`, so the guard of `grow` fails. -/
theorem grow_ueber_decke : ¬ (0 ≤ FAL.komSt w0K + 3 ∧ FAL.komSt w0K + 3 ≤ FDL.count FAL.tab) := by
  rw [komSt_w0K]; decide

/-- **The gap, as a witness:** with `n = -1` the commit is accepted by the model's guard and SHRINKS the committed word. -/
theorem wachs_negativ_schrumpft (Λ : List (Res FDL)) :
    ∃ (h0 : 0 ≤ FAL.komSt w0K + (-1)) (h : FAL.komSt w0K + (-1) ≤ FDL.count FAL.tab),
      FAL.komSt (nachGrow FAL.toDynForm (-1) Λ w0K h0 h) < FAL.komSt w0K := by
  have h0 : 0 ≤ FAL.komSt w0K + (-1) := by rw [komSt_w0K]; decide
  have h : FAL.komSt w0K + (-1) ≤ FDL.count FAL.tab := by rw [komSt_w0K]; decide
  obtain ⟨-, -, -, hk⟩ := grow_atomar (K := KLL) (-1) Λ w0K h0 h
  exact ⟨h0, h, by rw [hk, komSt_w0K]; decide⟩

end SperreZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.SperreZeuge.grow_zeuge_L
#print axioms Gabbro.Grammatik.SperreZeuge.wachs_negativ_schrumpft
