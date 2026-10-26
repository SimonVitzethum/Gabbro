/-
  File:      stage0/Stage0/Lauf/Treiber.lean
  Subject:   The driver of the thread machine: steps of the running threads (`aktiv`), each by `zug`, carrying the
             proof that the machine reached is reachable from the start machine (`RufErreichbarG`) and that every
             thread outside `aktiv` holds no lock (it never steps; `rufSchrittG_fremd`).
-/
import Stage0.Schritt.Zug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-- **A machine on a run**: reachable from `M0`, the threads outside `aktiv` holding nothing. -/
structure Stand (M0 : RufMaschineG D) (aktiv : List Faden) where
  M : RufMaschineG D
  erreicht : RufErreichbarG P O passes M0 M
  ruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []

variable {P O passes}

/-- One step of the first thread in `fs` that steps. -/
def Stand.weiter {M0 : RufMaschineG D} {aktiv : List Faden} (hO : OrakelSpurTreu O) (s : Stand P O passes M0 aktiv) :
    List {f // f ∈ aktiv} → Option (Faden × Stand P O passes M0 aktiv)
  | [] => none
  | ⟨f, hf⟩ :: fs =>
    match zug P O passes hO s.M f aktiv s.ruhe with
    | some z =>
      some (f, ⟨z.1, .schritt _ _ f s.erreicht z.2, fun g hg => by
        rw [rufSchrittG_fremd z.2 g (fun e => hg (e ▸ hf))]
        exact s.ruhe g hg⟩)
    | none => s.weiter hO fs

/-- The threads in round-robin order after `f`: those behind it first. -/
def nachRunde {aktiv' : List Faden} (reihe : List {f // f ∈ aktiv'}) (f : Faden) : List {f // f ∈ aktiv'} :=
  let (vorn, hinten) := reihe.span (fun g => g.1 != f)
  hinten.drop 1 ++ vorn ++ hinten.take 1

/-- **Run** at most `n` steps, round robin over the running threads; also the schedule taken. -/
def Stand.laufe {M0 : RufMaschineG D} {aktiv : List Faden} (hO : OrakelSpurTreu O) :
    Nat → List {f // f ∈ aktiv} → Stand P O passes M0 aktiv → List Faden → Stand P O passes M0 aktiv × List Faden
  | 0, _, s, plan => (s, plan.reverse)
  | n + 1, reihe, s, plan =>
    match s.weiter hO reihe with
    | some (f, s') => Stand.laufe hO n (nachRunde reihe f) s' (f :: plan)
    | none => (s, plan.reverse)

/-- The start of a run: the threads outside `aktiv` hold no lock at the start machine. -/
def Stand.start (M0 : RufMaschineG D) (aktiv : List Faden)
    (h : ∀ g, g ∉ aktiv → offen (M0.faeden g).spur = []) : Stand P O passes M0 aktiv :=
  ⟨M0, .start, h⟩

/-- Thread `f` has ended: its last frame stands at its return. -/
def fertig (M : RufMaschineG D) (f : Faden) : Bool :=
  (M.faeden f).stapel.isEmpty &&
    match (M.faeden f).kopf.rest with
    | ⟨_, _, _, _, .ende (.ret ..)⟩ => true
    | _ => false

end Gabbro.Stage0
