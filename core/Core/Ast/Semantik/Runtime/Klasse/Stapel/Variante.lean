/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Stapel/Variante.lean
  Subject:   Stack effect of the variant instruction family (MK-03). Schemas and carriers install a value,
             options and variants write one slot; `waehleVariante` only halts or writes the acting frame.
             None deepens the continuation stack.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Form
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

theorem varianteStapel (b : Befehl) (familie : b.familie = .variante) :
    b.Stapelwirkung b.klasse.Stapel := by
  intro frame live
  cases b <;> simp only [Befehl.familie] at familie <;> cases familie
  all_goals
    simp only [Befehl.auswerten, Befehl.klasse, Wirkungsklasse.Stapel, Id.run,
      Rahmen.schreibe, Rahmen.installSchema, Rahmen.halt,
      Rahmen.pass, Rahmen.setzeMass, Rahmen.bindeRegion, pure]
  all_goals
    repeat' first
    | simp only [Id.run, pure, Rahmen.halt, List.length_cons, List.length_nil, Nat.add_zero]
      omega
    | exact Rahmen.rufStapel frame _ _ _
    | exact Rahmen.rueckkehrStapel frame _
    | exact Rahmen.mitEintrittStapel (by assumption)
    | split

end Gabbro.Core.Ast.Semantik
