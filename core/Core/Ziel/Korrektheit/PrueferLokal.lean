module

public import Core.Ziel.Korrektheit.PrueferKlauseln
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Ast.Semantik

/-- The frame-only effect classes. Guarded operations may belong to these classes:
    their guards are checked independently of locality. -/
def lokalPruefeBefehl (b : Befehl) : Bool :=
  match b.klasse with
  | .lokal | .ruf | .maskiere | .prioritaet | .sendeUnterbrechung | .leiteLeitung => true
  | _ => false

/-- The executable class test agrees with the model's frame-only predicate. -/
theorem lokalPruefeBefehl_iff (b : Befehl) : lokalPruefeBefehl b = true ↔ b.Privat := by
  unfold lokalPruefeBefehl Befehl.Privat
  cases b.klasse <;> simp only [reduceCtorEq, eq_self, true_or, or_true, false_or, or_false,
    Bool.false_eq_true]

/-- Decide whether the instruction list is in the frame-only fragment. -/
def lokalPruefeCode (code : List Befehl) : Bool :=
  code.all lokalPruefeBefehl

theorem lokalPruefeCode_iff (p : Fragment) :
    lokalPruefeCode p.code = true ↔ ∀ b ∈ p.code, b.Privat := by
  simp only [lokalPruefeCode, List.all_eq_true, lokalPruefeBefehl_iff]

theorem lokalAbstrakt (p : Fragment) (platform : Katalog.Plattform)
    (checked : lokalPruefeCode p.code = true) : Annahme.Lokal (p.einheit platform) :=
  p.lokal_rahmen platform ((lokalPruefeCode_iff p).mp checked)

/-- The combined checker uses the frame-only fragment for locality, the clause
    checker for invariants and the interval analysis for guards. -/
def prueferKombiniert : Pruefer where
  pruefeLokal := fun _ t => lokalPruefeCode (fragment .unit t).code
  pruefeKlauseln := prueferKlauselnDecidierbar.pruefeKlauseln
  pruefeWaechter := prueferWaechterDecidierbar.pruefeWaechter
  fragmentLokal := fun _ t => lokalPruefeCode (fragment .unit t).code
  fragmentKlauseln := prueferKlauselnDecidierbar.fragmentKlauseln
  fragmentWaechter := prueferWaechterDecidierbar.fragmentWaechter

theorem prueferKombiniert_lokalKorrekt : PrueferLokalKorrektAussage prueferKombiniert := by
  intro P t checked
  exact lokalAbstrakt (fragment .unit t) P checked

theorem prueferKombiniert_lokalVollstaendig :
    PrueferLokalVollstaendigAussage prueferKombiniert :=
  fun _ _ member _ => member

end Gabbro.Core.Ziel.Korrektheit
