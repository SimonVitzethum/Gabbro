module

public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- The frame relation for expression evaluation uses the resolved de Bruijn slot
    and carries the typed incoming value at every visible binding. -/
def Rahmen.traegt (frame : Rahmen) (env : Umgebung scope) : Prop :=
  ∀ {type} (ref : Local scope type), frame.lokale[ref.index]? = some (some ⟨type, env ref⟩)

def Rahmen.Schritt (code : List Befehl) (before after : Rahmen) : Prop :=
  ∃ b, before.rueckgabe = none ∧ code[before.pc]? = some b ∧ after = b.auswerten before

inductive Rahmen.Lauf (code : List Befehl) : Rahmen → Rahmen → Prop where
  | start : Lauf code frame frame
  | schritt : Lauf code before middle → Schritt code middle after → Lauf code before after

-- Generalise the original expr_ergebnis_typ proof to runtime PC walks and use Logic.skips.
theorem expr_ergebnis_typ (slot : Nat) (tree : Expr scope type) (env : Umgebung scope)
    (frame : Rahmen) (bound : frame.traegt env) (active : frame.rueckgabe = none)
    (atStart : frame.pc = 0) :
    ∃ out, Rahmen.Lauf (expr slot tree).code frame out ∧
      out.pc = (expr slot tree).code.length ∧ out.temp slot = some ⟨type, tree.wert env⟩ ∧
      out.lokale = frame.lokale ∧ out.rueckgabe = none ∧
      ∀ i, i < slot → out.temp i = frame.temp i := by
  sorry

end Gabbro.Core.Ast.Semantik
