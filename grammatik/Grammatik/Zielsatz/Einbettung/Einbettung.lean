module
public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Kern.Syntax.Typen.Transport
@[expose] public section


/-!
  File:      Grammatik/Zielsatz/Einbettung/Einbettung.lean
  Subject:   EMBEDDING A DECLARATION INTO A LARGER ONE (`BUILD-SYSTEM.md` §7.10, stage E0).

  A project is proved over its OWN declaration `D`: its tables, globals, locks, marks, functions,
  invariants, axioms, registers and assumptions, and the heads it imports. A program that links
  it has a larger declaration `D'`. `Einbettung D D'` says how `D` sits in `D'`: an injection of
  every sort with its partial inverse, a bijection of the fields of every table, and the
  preservation of every attribute the semantics or the checker reads of an item of `D`. The
  table and signature NUMBERS map injectively (`tnum`, `num`), so a type of `D` translates to a
  type of `D'` (`tyN`: only `fnptr`, `ptr` and `ref` change their number) and the program keeps
  free numbers for its own signatures and tables.

  A diamond of projects is two embeddings into one `D'`; no quotient is needed.

  * `Einbettung` -- the structure; `Einbettung.id` -- the identity (it is inhabited).
  * `valE`, `ergE` -- values; `resE` -- held resources; `sigE` -- signatures; `vertragE` -- contracts.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

/-- **A type under the number maps**: signature numbers by `sn`, table numbers by `tn`. -/
@[reducible] def tyN (sn tn : Nat → Nat) : Ty → Ty := Ty.mapNumbers sn tn

/-- Under the identity maps a type is itself. -/
theorem tyN_id (τ : Ty) : tyN (fun n => n) (fun n => n) τ = τ := Ty.mapNumbers_id τ
