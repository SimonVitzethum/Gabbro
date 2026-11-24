module

public import Core.Ast.Semantik.Auswertung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Count semantic instructions, including a call, return or back-edge. -/
inductive Rahmen.LaufN (code : List Befehl) : Nat → Rahmen → Rahmen → Prop where
  | null : LaufN code 0 frame frame
  | step : before.stopp = none → before.rueckgabe = none →
      code[before.pc]? = some instruction →
      LaufN code n (instruction.auswerten before) after →
      LaufN code (n + 1) before after

def Rahmen.Aktiv (frame : Rahmen) : Prop := frame.stopp = none ∧ frame.rueckgabe = none

def Binnen (code : List Befehl) (budget : Nat) (start : Rahmen) (goal : Rahmen → Prop) : Prop :=
  ∃ n out, n ≤ budget ∧ Rahmen.LaufN code n start out ∧ goal out

theorem Rahmen.LaufN.trans (left : Rahmen.LaufN code n first middle)
    (right : Rahmen.LaufN code m middle last) :
    Rahmen.LaufN code (n + m) first last := by
  induction left generalizing last m with
  | null => simpa only [Nat.zero_add] using right
  | step live returned head _ ih =>
    rw [Nat.add_right_comm _ 1 m]
    exact .step live returned head (ih right)

private def Befehl.Ausdrucksschritt (b : Befehl) : Prop :=
  ∀ frame, let out := b.auswerten frame
    frame.pc < out.pc ∧ out = { frame with pc := out.pc, temp := out.temp }

private theorem expr_ausdrucksschritte (slot : Nat) (tree : Expr scope type) :
    ∀ b ∈ (expr slot tree).code, b.Ausdrucksschritt := by
  induction tree generalizing slot <;>
    simp only [expr, Fragment.anhaengen, Fragment.einzel,
      List.forall_mem_append, List.forall_mem_singleton]
  all_goals repeat' apply And.intro
  all_goals
    first
    | solve_by_elim
    | intro frame
      exact ⟨Nat.lt_succ_self _, by cases frame; rfl⟩
    | intro frame
      change _ < frame.pc + (if (frame.temp slot).bind alsBoolean = _ then _ else 1) ∧ _
      constructor
      · split <;> omega
      · cases frame
        rfl

private theorem Rahmen.Lauf.ausdrucksLaenge
    (edges : ∀ b ∈ code, b.Ausdrucksschritt) (walk : Rahmen.Lauf code first last)
    (active : first.Aktiv) (suffix : List Befehl) :
    ∃ n, first.pc ≤ last.pc ∧ n ≤ last.pc - first.pc ∧ Rahmen.LaufN (code ++ suffix) n first last ∧
      last = { first with pc := last.pc, temp := last.temp } := by
  induction walk with
  | start => exact ⟨0, Nat.le_refl _, Nat.zero_le _, .null, by cases first; rfl⟩
  | @schritt middle last _ step ih =>
    obtain ⟨n, forward, budget, counted, preserved⟩ := ih
    obtain ⟨b, returned, head, rfl⟩ := step
    have ⟨advances, onlyExpr⟩ := edges b (List.mem_of_getElem? head) middle
    have live : middle.stopp = none := (congrArg Rahmen.stopp preserved).trans active.1
    have head' : (code ++ suffix)[middle.pc]? = some b :=
      (List.getElem?_append_left (List.getElem?_eq_some_iff.mp head).1).trans head
    refine ⟨n + 1, by omega, by omega, counted.trans (.step live returned head' .null), ?_⟩
    let out := b.auswerten middle
    calc
      out = { middle with pc := out.pc, temp := out.temp } := onlyExpr
      _ = { first with pc := out.pc, temp := out.temp } :=
        congrArg (fun frame : Rahmen => { frame with pc := out.pc, temp := out.temp }) preserved

/-- Expression evaluation takes at most its code length and changes only its
    program counter and temporaries. Code after the expression is left untouched. -/
theorem expr_laufN (slot : Nat) (tree : Expr scope type) (env : Umgebung scope)
    (frame : Rahmen) (typed : frame.traegt env) (active : frame.Aktiv) (entry : frame.pc = 0)
    (suffix : List Befehl) :
    Binnen ((expr slot tree).code ++ suffix) (expr slot tree).code.length frame (fun out =>
      out.pc = (expr slot tree).code.length ∧ out.temp slot = some ⟨type, tree.wert env⟩ ∧
        out = { frame with pc := out.pc, temp := out.temp }) := by
  obtain ⟨out, walk, atEnd, value, _⟩ := expr_ergebnis_typ slot tree env frame typed active.2 entry
  obtain ⟨n, _, budget, counted, preserved⟩ :=
    walk.ausdrucksLaenge (expr_ausdrucksschritte slot tree) active suffix
  exact ⟨n, out, by simpa only [atEnd, entry, Nat.sub_zero] using budget, counted, atEnd, value, preserved⟩

end Gabbro.Core.Ast.Semantik
