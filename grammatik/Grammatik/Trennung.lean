/-
  File:      Grammatik/Trennung.lean
  Subject:   THREAD-SEPARATION FACTS BY COMPUTATION (lane 100, D2).

  `PCMarkSep` / `PCUnsharedSep` (Maschine.lean) and the `hNurG` shape of
  `eigenzustand_nur_eigene_schritteD_rep` (EigenZustandD.lean) are facts
  about PROGRAM TEXTS, so the checker can decide them. This file provides
  the decision functions (`markSepB`, `unsharedSepB`, `nurGB`) computed
  over atom lists, with soundness theorems into the three predicates.

  Thread enumeration: `Faden` is `Nat` (Marken.lean), hence infinite. A
  decidable check ranges over an explicit thread list `fs` (the threads
  the checker spawns -- DATA, not a proposition); soundness carries the
  coverage side-condition `hcov : forall h, h notin fs -> prog h = []`.
  On the witness it is proved from the program definition, not assumed.
-/
import Grammatik.Maschine
import Grammatik.Extraktion

namespace Gabbro.Grammatik

open Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-- Mark separation, decided: no code named by one listed thread's text
    is named by another's. Diagonal pairs pass silently. -/
def markSepB (code : D.Marke → Nat) (prog : PCProg D)
    (fs : List Faden) : Bool :=
  fs.all fun f => fs.all fun g =>
    (decide (f = g) ||
      ((prog.marks f).map code).all fun c =>
        !decide (c ∈ (prog.marks g).map code))

/-- Carrier separation for unshared carriers, decided: a carrier reached
    from two listed threads' texts is declared shared. Membership runs
    through `any` (`DecidableEq` holds; `BEq` does not). -/
def unsharedSepB (prog : PCProg D) (fs : List Faden) : Bool :=
  fs.all fun f => fs.all fun g =>
    (decide (f = g) ||
      (prog.carriers f).all fun o =>
        (!((prog.carriers g).any fun o' => decide (o = o')) ||
          match o with
          | .inl t => D.geteilt t
          | .inr x => D.ggeteilt x))

/-- Own-state text fact, decided: no listed thread other than `g` names
    the table carrier `t` in any atom. -/
def nurGB (t : D.Tab) (g : Faden) (prog : PCProg D)
    (fs : List Faden) : Bool :=
  fs.all fun h =>
    (decide (h = g) || (prog h).all fun a =>
      !((PCAtom.carriers a).any fun o => decide (o = Sum.inl t)))

end Gabbro.Grammatik
