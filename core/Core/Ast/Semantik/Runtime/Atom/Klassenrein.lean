/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Klassenrein.lean
  Subject:   FRAGMENTS WITH ACCESS INSTRUCTIONS (MK-04b). A fragment is FRAME-ONLY (`Fragment.Rein`) when every instruction
             of its code is frame-only. A source form that elaborates to an access instruction
             (`Zugriffsquelle`) makes a fragment that is not. `Fragment.KlassenRein` is the next predicate: every
              instruction is frame-only or an access instruction. The access classes the source reaches are `lesen`,
              `schreiben` and `rmw` (the lifecycle instructions of MK-07 and the interrupt-control instructions of
              MK-20 have no source form), so `KlassenRein` is the predicate the generic proofs of the units of the
             source take once an access form is in the grammar. `Fragment.MitZugriff` is the part that is not
             frame-only: exactly the fragments whose statements rest on the duties of the access classes
             (`KlassenAussagen`, `ZugriffBefehlAussage`, `AtomAussagen`) and on the pinned statements of
             `Ziel/Korrektheit/Zugriff`, and not on the template step of the frame-only classes.
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Rein
public import Core.Ast.Semantik.Runtime.Atom.Form
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- **An instruction is frame-only or an access instruction.** -/
def Befehl.Klassengut (b : Befehl) : Prop := b.Privat ∨ ∃ z, b = .zugriff z

/-- **Every instruction of the fragment is frame-only or an access instruction.** -/
def Fragment.KlassenRein (p : Fragment) : Prop := ∀ b ∈ p.code, b.Klassengut

/-- **The fragments that contain an access instruction**: not frame-only, but with no instruction outside the
    two classes. -/
def Fragment.MitZugriff (p : Fragment) : Prop := p.KlassenRein ∧ ¬ p.Rein

/-- A frame-only fragment has only instructions of the two classes. -/
theorem Fragment.rein_klassenrein {p : Fragment} (h : p.Rein) : p.KlassenRein :=
  fun b mem => Or.inl (h b mem)

theorem Fragment.klassenrein_leer : Fragment.leer.KlassenRein := fun _ hb => absurd hb List.not_mem_nil

theorem Fragment.klassenrein_einzel_iff (b : Befehl) : (Fragment.einzel b).KlassenRein ↔ b.Klassengut := by
  constructor
  · intro h
    exact h b (List.mem_singleton_self b)
  · intro h x hx
    rw [List.mem_singleton.mp hx]
    exact h

theorem Fragment.klassenrein_anhaengen_iff (a b : Fragment) :
    (a.anhaengen b).KlassenRein ↔ a.KlassenRein ∧ b.KlassenRein := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append.mpr (Or.inl hx)), fun x hx => h x (List.mem_append.mpr (Or.inr hx))⟩
  · intro h x hx
    exact (List.mem_append.mp hx).elim (h.1 x) (h.2 x)

/-- Elaboration emits local operations, calls and accesses. Interrupt control has no source form. -/
def Fragment.QuellklassenRein (p : Fragment) : Prop :=
  p.alle (fun b => (b.klasse = .lokal ∨ b.klasse = .ruf) ∨ ∃ z, b = .zugriff z)

theorem Fragment.QuellklassenRein.klassenrein {p : Fragment} (h : p.QuellklassenRein) :
    p.KlassenRein := by
  intro b mem
  rcases h b mem with (lokal | ruf) | zugriff
  · exact Or.inl (Or.inl lokal)
  · exact Or.inl (Or.inr (Or.inl ruf))
  · exact Or.inr zugriff

private theorem expr_quellklassenrein (slot : Nat) (tree : Expr scope type) :
    (expr slot tree).QuellklassenRein :=
  fun b mem => Or.inl (expr_lokal_ruf slot tree b mem)

theorem expr_klassenrein (slot : Nat) (tree : Expr scope type) : (expr slot tree).KlassenRein :=
  (expr_quellklassenrein slot tree).klassenrein

/-- A fragment of the two classes is frame-only or has an access instruction. -/
theorem Fragment.klassenrein_rein_oder {p : Fragment} (h : p.KlassenRein) : p.Rein ∨ p.MitZugriff := by
  by_cases r : p.Rein
  · exact Or.inl r
  · exact Or.inr ⟨h, r⟩

/-- An access instruction is not frame-only: the class of every access is `lesen`, `schreiben` or `rmw`. -/
theorem Befehl.zugriff_nicht_privat (z : Zugriffsform) : ¬ (Befehl.zugriff z).Privat := by
  intro h
  exact Befehl.privat_ne_zugriff_klasse _ h z rfl

/-- **The fragment that consists of one access instruction has an access instruction.** The pinned statements about
    the fragments `MitZugriff` quantify over a nonempty set: the unit of a single load is one. -/
theorem Fragment.einzel_zugriff_mitZugriff (z : Zugriffsform) : (Fragment.einzel (.zugriff z)).MitZugriff := by
  refine ⟨?_, ?_⟩
  · intro b mem
    rw [List.mem_singleton.mp mem]
    exact Or.inr ⟨z, rfl⟩
  · intro h
    exact Befehl.zugriff_nicht_privat z ((Fragment.rein_einzel_iff _).mp h)

private theorem Fragment.quellklassenrein_leer : Fragment.leer.QuellklassenRein := Fragment.alle_leer _

private theorem Fragment.quellklassenrein_einzel_iff (b : Befehl) :
    (Fragment.einzel b).QuellklassenRein ↔
      (b.klasse = .lokal ∨ b.klasse = .ruf) ∨ ∃ z, b = .zugriff z :=
  Fragment.alle_einzel_iff _ b

private theorem Fragment.quellklassenrein_anhaengen_iff (a b : Fragment) :
    (a.anhaengen b).QuellklassenRein ↔ a.QuellklassenRein ∧ b.QuellklassenRein :=
  Fragment.alle_anhaengen_iff _ a b

/-- **The code of an access form is frame-only or access.** -/
private theorem accessCode_quellklassenrein (form : Access before after) : (accessCode form).QuellklassenRein := by
  cases form <;>
    simp only [accessCode, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff,
      expr_quellklassenrein, true_and] <;>
    first
      | exact Or.inr ⟨_, rfl⟩
      | exact ⟨Or.inr ⟨_, rfl⟩, Or.inl (Or.inl rfl)⟩


private theorem argsCode_quellklassenrein (slot : Nat) (args : List (TypedExpr scope)) : (argsCode slot args).QuellklassenRein := by
  induction args generalizing slot with
  | nil => exact Fragment.quellklassenrein_leer
  | cons value rest ih =>
    simp only [argsCode, Fragment.quellklassenrein_anhaengen_iff]
    exact ⟨expr_quellklassenrein _ _, ih _⟩

private theorem optionCode_quellklassenrein (slot : Nat) (value : OptionInitializer scope count) :
    (optionCode slot value).QuellklassenRein := by
  simp only [optionCode, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff]
  refine ⟨?_, ?_⟩
  · cases value with
    | absent => exact Fragment.quellklassenrein_leer
    | present value _ => exact expr_quellklassenrein _ _
  · first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr rfl)

private theorem stmt_quellklassenrein (tree : Stmt result before after) : (stmt tree).QuellklassenRein := by
  refine @Stmt.rec result
    (fun _ _ t => (stmt t).QuellklassenRein)
    (fun _ _ t => (block t).QuellklassenRein)
    (fun _ t => (bracedBlock t).QuellklassenRein)
    (fun _ _ _ _ t => (variantArms t).body.QuellklassenRein)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after tree
  all_goals
    intros
    simp_all only [stmt, accessCode_quellklassenrein, block, bracedBlock, variantArms, callCode, MatchCode.prepend, Bool.false_eq_true,
      ↓reduceIte, Fragment.quellklassenrein_leer, Fragment.quellklassenrein_einzel_iff, Fragment.quellklassenrein_anhaengen_iff, expr_quellklassenrein,
      argsCode_quellklassenrein, optionCode_quellklassenrein, true_and, and_true]
  all_goals
    repeat' first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr rfl)
      | exact (Fragment.quellklassenrein_einzel_iff _).2 (Or.inl (Or.inl rfl))
      | refine ⟨?_, ?_⟩

private theorem bracedBlock_quellklassenrein (tree : BracedBlock result scope) : (bracedBlock tree).QuellklassenRein := by
  have both := stmt_quellklassenrein (Stmt.ite .trueLit tree tree)
  simp only [stmt, expr, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff] at both
  exact both.1.1.2

private theorem functionCode_quellklassenrein {result : Option WrittenType} {scope : Scope}
    (measure : Option (Measure scope)) (body : BracedBlock (writtenResult result) scope) :
    (functionCode result measure body).QuellklassenRein := by
  cases measure with
  | none =>
    simp only [functionCode, measurePrologue, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff, Fragment.quellklassenrein_leer,
      bracedBlock_quellklassenrein, true_and]
    exact Or.inl (Or.inl rfl)
  | some m =>
    simp only [functionCode, measurePrologue, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff, expr_quellklassenrein,
      bracedBlock_quellklassenrein, true_and]
    repeat' first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr rfl)
      | exact trivial
      | refine ⟨?_, ?_⟩

private theorem decl_quellklassenrein {before after : Scope} (d : Decl before after) : (decl d).QuellklassenRein := by
  cases d with
  | constant name ordinary written valid value staticValue fits =>
    simp only [decl, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff, expr_quellklassenrein, true_and]
    exact Or.inl (Or.inl rfl)
  | function name ordinary parameters result valid decreases body distinct returns effects =>
    simp only [decl, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff, functionCode_quellklassenrein, and_true]
    exact Or.inl (Or.inl rfl)
  | record exported name fields valid distinct =>
    simp only [decl, Fragment.quellklassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | tagged exported name first tail valid distinct =>
    simp only [decl, Fragment.quellklassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | table item =>
    simp only [decl, Fragment.quellklassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | effectGroup item =>
    simp only [decl, Fragment.quellklassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | environment name abi row =>
    simp only [decl, Fragment.quellklassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)

private theorem unitBody_quellklassenrein {before after : Scope} (body : UnitBody before after) : (unitBody body).QuellklassenRein := by
  induction body with
  | done => exact Fragment.quellklassenrein_leer
  | step first rest ih =>
    simp only [unitBody, Fragment.quellklassenrein_anhaengen_iff]
    exact ⟨decl_quellklassenrein first, ih⟩

private theorem programm_quellklassenrein (tree : Ast.Unit) : (programm tree).QuellklassenRein := by
  simp only [programm, Fragment.quellklassenrein_anhaengen_iff, Fragment.quellklassenrein_einzel_iff, unitBody_quellklassenrein, true_and]
  exact ⟨Or.inl (Or.inr rfl), Or.inl (Or.inl rfl)⟩

/-- Every elaborated category emits local operations, calls and accesses. -/
theorem fragment_quellklassenrein (category : Category) (tree : category.Tree) : (fragment category tree).QuellklassenRein := by
  cases category with
  | expression scope => exact expr_quellklassenrein _ _
  | statement scope result => exact stmt_quellklassenrein _
  | block scope result => exact bracedBlock_quellklassenrein _
  | unit => exact programm_quellklassenrein tree
  | declaration scope => exact decl_quellklassenrein _

theorem accessCode_klassenrein (form : Access before after) : (accessCode form).KlassenRein :=
  (accessCode_quellklassenrein form).klassenrein

theorem stmt_klassenrein (tree : Stmt result before after) : (stmt tree).KlassenRein :=
  (stmt_quellklassenrein tree).klassenrein

theorem bracedBlock_klassenrein (tree : BracedBlock result scope) : (bracedBlock tree).KlassenRein :=
  (bracedBlock_quellklassenrein tree).klassenrein

theorem programm_klassenrein (tree : Ast.Unit) : (programm tree).KlassenRein :=
  (programm_quellklassenrein tree).klassenrein

theorem fragment_klassenrein (category : Category) (tree : category.Tree) : (fragment category tree).KlassenRein :=
  (fragment_quellklassenrein category tree).klassenrein

end Gabbro.Core.Ast.Semantik
