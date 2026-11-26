module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleife

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The result of `m` primitive-recursion steps starting at counter `j` with
    accumulator `v`. The step at offset `t` uses the index `j + t`. -/
def precFolgeVon (cg : Nat.Partrec.Code) (a j : Nat) : Nat → Nat → Part Nat
  | 0, v => Part.some v
  | m + 1, v => (precFolgeVon cg a j m v).bind
      (fun u => Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair (j + m) u)))

theorem precFolgeVonEins (cg : Nat.Partrec.Code) (a j v : Nat) :
    precFolgeVon cg a j 1 v =
      Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair j v)) := by
  simp only [precFolgeVon, Nat.add_zero, Part.bind_some]

/-- Split the first step off the sequence: the remaining steps restart at the
    successor index with the value produced by that first step. -/
theorem precFolgeVonSchritt (cg : Nat.Partrec.Code) (a j m v : Nat) :
    precFolgeVon cg a j (m + 1) v =
      (Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair j v))).bind
        (fun v' => precFolgeVon cg a (j + 1) m v') := by
  induction m generalizing v with
  | zero =>
    simp only [precFolgeVon, Nat.add_zero, Part.bind_some, Part.bind_some_right]
  | succ m ih =>
    change (precFolgeVon cg a j (m + 1) v).bind
        (fun u => Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair (j + (m + 1)) u))) = _
    rw [ih]
    rw [Part.bind_assoc]
    congr 1
    funext v'
    change (precFolgeVon cg a (j + 1) m v').bind
        (fun u => Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair (j + (m + 1)) u))) =
      (precFolgeVon cg a (j + 1) m v').bind
        (fun u => Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair ((j + 1) + m) u)))
    congr 1
    funext u
    rw [show j + (m + 1) = (j + 1) + m by omega]

/-- Mathlib's primitive-recursion evaluation is exactly the step sequence
    starting from the base value computed by `cf`. -/
theorem evalPrecAlsFolge (cf cg : Nat.Partrec.Code) (a k : Nat) :
    Nat.Partrec.Code.eval (Nat.Partrec.Code.prec cf cg) (Nat.pair a k) =
      (Nat.Partrec.Code.eval cf a).bind (fun v => precFolgeVon cg a 0 k v) := by
  induction k with
  | zero =>
    rw [Nat.Partrec.Code.eval_prec_zero]
    simp only [precFolgeVon, Part.bind_some_right]
  | succ k ih =>
    rw [Nat.Partrec.Code.eval_prec_succ, ih]
    rw [Part.bind_eq_bind]
    rw [Part.bind_assoc]
    change ((Nat.Partrec.Code.eval cf a).bind fun x =>
        (precFolgeVon cg a 0 k x).bind fun ih =>
          Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair k ih))) =
      (Nat.Partrec.Code.eval cf a).bind fun v =>
        (precFolgeVon cg a 0 k v).bind
          (fun u => Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair (0 + k) u)))
    rw [Nat.zero_add]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
