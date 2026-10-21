/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben31.lean
  Subject:   Track P: the pipeline with the declared starts (`uebersetzeMitStarts`): the `concurrent` members and
             the entry dispatch roots (`Starts.roots`), the handlers entered by hardware (`Starts.hands`) and the
             threads of `start { .. };` (`Starts.gestartet`), as functions of the declaration.
-/
import Grammatik.Parser.Elab.UebersetzePipeline

namespace Gabbro.Grammatik.Parser.UebersetzeProben31

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- The function numbers of the declared starts: roots, handlers, started threads. -/
def startNr (s : String) : Option (List Nat × List Nat × List Nat) :=
  match uebersetzeMitStarts s with
  | .error _ => none
  | .ok ⟨_, _, _, st⟩ =>
    some (st.roots.map (fun (f : Fin _) => f.val), st.hands.map (fun (f : Fin _) => f.val),
          st.gestartet.map (fun (f : Fin _) => f.val))

/-- Two concurrent members, one of them also an interrupt handler through an entry with `via`. -/
def starts_ok : String :=
  "module m { impl fn w() { } impl fn r() { } concurrent { r, w }; entry e vector 1 via idt arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"
theorem starts_ok_nr : startNr starts_ok = some ([1, 0, 0], [0], []) := by decide +kernel

/-- A thread created by `start { .. };`. -/
def gestartet_ok : String :=
  "module m { impl fn w() { } impl fn h() { start { w }; } concurrent { h }; }"
theorem gestartet_ok_nr : startNr gestartet_ok = some ([1], [], [0]) := by decide +kernel

/-- A start that names a function with parameters has no form: no starts are returned. -/
def starts_refused : String :=
  "module m { impl fn w(a : u32 in 0 .. 1) { } concurrent { w }; }"
theorem starts_refused_nr : startNr starts_refused = none := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben31
