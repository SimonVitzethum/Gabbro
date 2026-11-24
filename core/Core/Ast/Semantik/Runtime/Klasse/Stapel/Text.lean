/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Stapel/Text.lean
  Subject:   Stack effect of the text instruction family (MK-03). Literals, concatenation and length use
             `Rahmen.schreibe`; `textIndex` and `substring` halt on a bad index or bounds and otherwise
             write the acting frame. The continuation stack is unchanged in every case.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Form
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

theorem textStapel (b : Befehl) (familie : b.familie = .text) :
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
