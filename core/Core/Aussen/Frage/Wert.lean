/-
  File:      core/Core/Aussen/Frage/Wert.lean
  Subject:   THE DECLARED RETURN TYPE AND THE TYPED VALUE OF AN OUTSIDE ANSWER (MK-06,
              `verbrauche` Nacharbeit). The catalogue row of an operation declares which answer
              kind may be bound by `verbrauche`. An ok answer is translated into a frame value
              of that declared kind; an answer of another kind, or an error answer, has no
              translated value and is refused at the state level. The translation is a total
              function of the answer, so the value written into the target slot is determined
              by the answer alone, never by a success constant.
-/
module

public import Core.Katalog.Aussen
public import Core.Ast.Semantik.Runtime.Frame

@[expose] public section

namespace Gabbro.Core.Katalog

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- **The return kind declared by the catalogue row of a question.** It is the type an ok answer
    must have to be bound at the target slot of a `verbrauche`. -/
inductive RueckgabeArt where
  | daten
  | quittung
  | griff
  | register
  deriving DecidableEq, Repr

/-- The row of an operation declares its return kind. -/
def AussenOperation.rueckgabe : AussenOperation → RueckgabeArt
  | .read => .daten
  | .write _bytes => .quittung
  | .resolve _name => .griff
  | .firmware _service _request => .daten
  | .exchange _message => .daten
  | .registerRead _offset => .register
  | .registerWrite _offset _value => .register
  | .waitRegister _offset _expected => .register

/-- The kind carried by an answer value. -/
def AussenWert.rueckgabe : AussenWert → RueckgabeArt
  | .data _bytes => .daten
  | .written _bytes => .quittung
  | .handle _handle => .griff
  | .register _value => .register
  | .registerWritten _offset _value => .register
  | .firmware _service _request _response => .daten
  | .exchanged _request _response => .daten

/-- An answer value fits the declared return kind exactly when the two kinds agree. -/
def AussenWert.passt (v : AussenWert) (deklariert : RueckgabeArt) : Bool :=
  v.rueckgabe == deklariert

/-- Byte payloads bind as a text value whose capacity is the payload length. -/
def bytesWert (bytes : List UInt8) : Dynamisch :=
  ⟨.text bytes.length, ⟨bytes.toByteArray, by
    rw [← ByteArray.size_data, ← Array.length_toList]
    exact le_of_eq (congrArg List.length (List.toList_data_toByteArray (l := bytes)))⟩⟩

/-- A register value binds as an integer with the exact interval of its value. -/
def registerWert (value : Nat) : Dynamisch :=
  ⟨.int 0 (value : Int), ⟨(value : Int), Int.natCast_nonneg value, Int.le_refl _⟩⟩

/-- The frame value of an answer of the matching kind. -/
def AussenWert.alsDynamisch : AussenWert → Dynamisch
  | .data bytes => bytesWert bytes
  | .written bytes => bytesWert bytes
  | .firmware _ _ response => bytesWert response
  | .exchanged _ response => bytesWert response
  | .handle h => ⟨.ownedRegion, h.channel⟩
  | .register value => registerWert value
  | .registerWritten _ value => registerWert value

/-- **The translated answer value.** An ok answer of the declared kind yields the frame value of
    its payload; an error answer or a value of another kind yields nothing. -/
def Antwort.uebersetzt (q : Frage) (a : Antwort) : Option Dynamisch :=
  match a.result with
  | Except.ok v => if v.passt q.operation.rueckgabe then some v.alsDynamisch else none
  | Except.error _fehler => none

/-- A fitting ok answer translates to exactly its own frame value. -/
theorem Antwort.uebersetzt_von_ok (q : Frage) (a : Antwort) (v : AussenWert)
    (result : a.result = Except.ok v) (passt : v.passt q.operation.rueckgabe = true) :
    Antwort.uebersetzt q a = some v.alsDynamisch := by
  simp only [Antwort.uebersetzt, result, passt, if_true]

/-- An answer of another kind translates to nothing. -/
theorem Antwort.uebersetzt_fremd (q : Frage) (a : Antwort) (v : AussenWert)
    (result : a.result = Except.ok v) (passt : v.passt q.operation.rueckgabe = false) :
    Antwort.uebersetzt q a = none := by
  simp only [Antwort.uebersetzt, result, passt, Bool.false_eq_true, if_false]

/-- An error answer translates to nothing. -/
theorem Antwort.uebersetzt_fehler (q : Frage) (a : Antwort) (e : AussenFehler)
    (result : a.result = Except.error e) : Antwort.uebersetzt q a = none := by
  simp only [Antwort.uebersetzt, result]

end Gabbro.Core.Katalog

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Katalog
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- **The matching value case is reachable.** A hosted read of bytes fits the declared kind and
    translates to a frame value. -/
def VerbraucheWertErfuellbarAussage : Prop :=
  ∃ (q : Frage) (a : Antwort) (v : AussenWert),
    a.result = Except.ok v ∧ v.passt q.operation.rueckgabe = true ∧
      Antwort.uebersetzt q a = some v.alsDynamisch

/-- **The mismatch case is reachable.** A register answer to a byte question does not fit and is
    refused, so the binding is not a vacuous success bit. -/
def VerbraucheWertNichtTrivialAussage : Prop :=
  ∃ (q : Frage) (a : Antwort) (v : AussenWert),
    a.result = Except.ok v ∧ v.passt q.operation.rueckgabe = false ∧
      Antwort.uebersetzt q a = none

/-- A hosted read binds its bytes. -/
theorem verbraucheWert_erfuellbar : VerbraucheWertErfuellbarAussage := by
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let a : Antwort := ⟨handle.origin, [handle.origin], .ok (.data [])⟩
  refine ⟨q, a, .data [], ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact Antwort.uebersetzt_von_ok q a (.data []) rfl rfl

/-- A register answer to a byte question is refused. -/
theorem verbraucheWert_nichtTrivial : VerbraucheWertNichtTrivialAussage := by
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let a : Antwort := ⟨handle.origin, [handle.origin], .ok (.register 7)⟩
  refine ⟨q, a, .register 7, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact Antwort.uebersetzt_fremd q a (.register 7) rfl rfl

end Gabbro.Core.Aussenfrage
