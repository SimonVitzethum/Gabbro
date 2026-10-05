/-
  File:      Grammatik/X86/PipelineLoops.lean
  Subject:   Bounded source loops (`Stmt.retry`, the `retry until … bounded n`
    form) lowered to one labelled block with rel8/rel32 branches.

    The schema `schleifeProg` lays a body of fall-through unified
    instructions (`Instr`, `ISA.lean`) between a head conditional exit
    (`jcc`) and a back jump (`jmp`), exactly the shape the bounded
    relaxation (`ISARelax.lean`: `relax`, `relaxLayoutOk`, `bild`) lays out
    and connects to fetched byte runs (`laufBytesL_start`,
    `relax_laufBytes`). Finite source runs (`retryLauf`, `Semantik.lean`)
    transfer their iteration budget `n` to the target step budget
    `schleifeSchritte n m`. Unbounded loops (`forever`, source `while`
    without a bound) get NO finite budget here: only finite-prefix
    unfolding (`ewig_ein_schritt`) and the loud budget stop at zero passes
    (proved in `BudgetExecution.lean`, cited in CUTS).

    Reused, not duplicated: `LProg`/`stepL`/`laufL`/`laufL_add`,
    `relax`/`relax_ok`/`relaxLayoutOk`/`layoutOk_zeile`/`bild`,
    `laufBytesL_start`/`relax_laufBytes`, `kanonischI`, `faelltDurchI`,
    `retryLauf`/`foreverLauf`, `bedingung`.
-/
import Grammatik.X86.ISARelax
import Grammatik.Semantik

namespace Gabbro.Grammatik.X86.PipelineLoops

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

/-- The loop schema: head `jcc` to the end label, the body as `op` rows,
    one back jump to label 0. Labels: `0` head, `1 .. n` body,
    `n + 1` back jump, `n + 2` end. -/
def schleifeProg (koerper : List Instr) (c : Bedingung) : LProg :=
  LInstr.jcc c (koerper.length + 2) :: (koerper.map LInstr.op) ++ [LInstr.jmp 0]

/-- The schema length: body rows plus the two branch rows. -/
theorem schleifeProg_laenge (koerper : List Instr) (c : Bedingung) :
    (schleifeProg koerper c).length = koerper.length + 2 := by
  simp [schleifeProg]

/-- The head row is the conditional exit to the end label. -/
theorem schleifeProg_kopf (koerper : List Instr) (c : Bedingung) :
    (schleifeProg koerper c)[0]? = some (LInstr.jcc c (koerper.length + 2)) := rfl

/-- The row after the body is the back jump to label 0. -/
theorem schleifeProg_rueck (koerper : List Instr) (c : Bedingung) :
    (schleifeProg koerper c)[koerper.length + 1]? = some (LInstr.jmp 0) := by
  unfold schleifeProg
  have hlen : ((LInstr.jcc c (koerper.length + 2) :: koerper.map LInstr.op)).length
      = koerper.length + 1 := by simp
  rw [List.getElem?_append_right (by omega), hlen]
  simp

/-- A body row sits at its index shifted by one (past the head row). -/
theorem schleifeProg_mitte (koerper : List Instr) (c : Bedingung) (j : Nat)
    (hj : j < koerper.length) :
    (schleifeProg koerper c)[j + 1]? = some (LInstr.op koerper[j]) := by
  unfold schleifeProg
  have h1 : j + 1 < ((LInstr.jcc c (koerper.length + 2) :: koerper.map LInstr.op)).length := by
    simp only [List.length_cons, List.length_map]
    omega
  rw [List.getElem?_append_left h1, List.getElem?_cons_succ,
    List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]

/-! ## 2. Compilation through the existing relaxation, and refusals -/

/-- Compilation: relax the schema (bounded rounds over rel8/rel32) and take
    its byte image. `none` is refusal, never a guess. -/
def schleifeKompilieren (treibstoff : Nat) (koerper : List Instr) (c : Bedingung) :
    Option (List Byte) :=
  match relax treibstoff (schleifeProg koerper c) with
  | some ws => some (bild ws (schleifeProg koerper c))
  | none => none

/-- Whatever the fuel, a relaxed schema layout validates. -/
theorem schleife_relax_ok (treibstoff : Nat) (koerper : List Instr) (c : Bedingung)
    (ws : List Bool) (h : relax treibstoff (schleifeProg koerper c) = some ws) :
    relaxLayoutOk ws (schleifeProg koerper c) = true :=
  relax_ok treibstoff (schleifeProg koerper c) ws h

/-- REFUSAL: a body row that is not canonical fall-through code (a jump, a
    call, `ret`, a non-canonical row) makes even the all-wide layout fail,
    so relaxation answers `none` at every fuel. -/
theorem schleife_verweigert_schlechten_koerper (treibstoff : Nat) (koerper : List Instr)
    (c : Bedingung) (j : Nat) (hj : j < koerper.length)
    (hschlecht : (kanonischI koerper[j] && faelltDurchI koerper[j]) = false) :
    schleifeKompilieren treibstoff koerper c = none := by
  have hmitte := schleifeProg_mitte koerper c j hj
  by_cases hlay : relaxLayoutOk (alleWeit (schleifeProg koerper c)) (schleifeProg koerper c) = true
  · exfalso
    have hz := layoutOk_zeile _ _ hlay (j + 1) (LInstr.op koerper[j]) hmitte
    have hop : zeileOk (alleWeit (schleifeProg koerper c)) (schleifeProg koerper c)
        (j + 1) (LInstr.op koerper[j])
        = (kanonischI koerper[j] && faelltDurchI koerper[j]) := rfl
    rw [hop, hschlecht] at hz
    cases hz
  · have hrel : relax treibstoff (schleifeProg koerper c) = none := by
      unfold relax
      rw [if_neg hlay]
    unfold schleifeKompilieren
    rw [hrel]

/-- Poison probe: `ret` in the body is refused (it does not fall through). -/
theorem schleife_verweigert_ret (treibstoff : Nat) (c : Bedingung) :
    schleifeKompilieren treibstoff [.pilot .ret] c = none :=
  schleife_verweigert_schlechten_koerper treibstoff [.pilot .ret] c 0
    (by decide) (by decide)

/-- Poison probe: a rel32 jump in the body is refused (control stays in the
    schema's two branch rows). -/
theorem schleife_verweigert_sprung (treibstoff : Nat) (c : Bedingung)
    (d : BitVec 32) :
    schleifeKompilieren treibstoff [.pilot (.jump32 d)] c = none :=
  schleife_verweigert_schlechten_koerper treibstoff [.pilot (.jump32 d)] c 0
    (by simp) (by rfl)

/-
CUTS:
- Pilot ISA only through `Instr`; one core, model memory, no time, no TSO:
  inherited from `ISARelax.lean`.
- No unbounded-loop budget: `forever` at any positive pass count unfolds
  one step (`ewig_ein_schritt` below); exhaustion is loud at zero passes
  (`BudgetExecution.forever_erschoepft_benannt`, not restated here).
- Per-iteration body correspondence (`hSeg` of `schleife_korrekt_endlich`)
  is a premise proved per body by its producer (straight-line bodies by
  the `Pipeline.lean` lemmas); this file lifts it to `n` rounds.
-/
