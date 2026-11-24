/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Stapel/Form.lean
  Subject:   Shared frame-level facts for the stack effect of an instruction (MK-03). A frame update
             that keeps `fortsetzungen` leaves the stack length alone; a return pops at most one
             continuation; a call pushes at most one, even on the prepared entry of a start. These
             facts are the common basis of the six family lemmas; they speak about every frame alike.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Klasse

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Writing a value into the acting frame never changes the continuation stack. -/
lemma Rahmen.schreibe_fortsetzungen (frame : Rahmen) (ziel : Nat) (value : Option Dynamisch) :
    (frame.schreibe ziel value).fortsetzungen = frame.fortsetzungen := rfl

/-- A halt never changes the continuation stack. -/
lemma Rahmen.halt_fortsetzungen (frame : Rahmen) (reason : Abschluss) :
    (frame.halt reason).fortsetzungen = frame.fortsetzungen := rfl

/-- Installing a schema never changes the continuation stack. -/
lemma Rahmen.installSchema_fortsetzungen (frame : Rahmen) (schema : Dynamisch) :
    (frame.installSchema schema).fortsetzungen = frame.fortsetzungen := rfl

/-- Returning pops at most one continuation. -/
lemma Rahmen.rueckkehrStapel (frame : Rahmen) (result : Option Dynamisch) :
    (frame.rueckkehr result).fortsetzungen.length ≤ frame.fortsetzungen.length := by
  cases h : frame.fortsetzungen with
  | nil =>
      simp only [Rahmen.rueckkehr, h, List.length_nil]
      omega
  | cons saved stack =>
      simp only [Rahmen.rueckkehr, h, List.length_cons]
      omega

/-- A call pushes at most one continuation; every refusal halts and keeps the stack. -/
lemma Rahmen.rufStapel (frame : Rahmen) (name : Identifier)
    (sources : List (Ty .value)) (bind : Option (Ty .value)) :
    (frame.ruf name sources bind).fortsetzungen.length ≤ frame.fortsetzungen.length + 1 := by
  unfold Rahmen.ruf
  cases bind <;> simp only [Id.run, pure, Rahmen.halt, List.length_cons]
  all_goals
    repeat' first
    | simp only [Id.run, pure, Rahmen.halt, List.length_cons, Nat.add_zero]
      omega
    | split

/-- Entry preparation replaces only locals and temporaries; the stack is untouched. -/
lemma Rahmen.eintritt_fortsetzungen (frame : Rahmen) (types : List (Ty .value)) (entry : Rahmen)
    (prepared : frame.eintrittArgumente types = some entry) :
    entry.fortsetzungen = frame.fortsetzungen := by
  unfold Rahmen.eintrittArgumente at prepared
  split at prepared
  · cases prepared
    rfl
  · split at prepared
    · cases prepared
      rfl
    · cases prepared

/-- A call from a prepared entry deepens the original frame by at most one. -/
lemma Rahmen.mitEintrittStapel {frame entry : Rahmen} {name : Identifier}
    {parameter : List (Ty .value)} {bind : Option (Ty .value)}
    (prepared : frame.eintrittArgumente parameter = some entry) :
    (entry.ruf name parameter bind).fortsetzungen.length ≤ frame.fortsetzungen.length + 1 := by
  have same := Rahmen.eintritt_fortsetzungen frame parameter entry prepared
  rw [← same]
  exact Rahmen.rufStapel entry name parameter bind

end Gabbro.Core.Ast.Semantik
