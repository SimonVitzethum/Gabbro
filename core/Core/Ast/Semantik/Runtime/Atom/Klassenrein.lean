/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Klassenrein.lean
  Subject:   FRAGMENTS WITH ACCESS INSTRUCTIONS (MK-04b). A fragment is FRAME-ONLY (`Fragment.Rein`) when every instruction
             of its code is frame-only. A source form that elaborates to an access instruction
             (`Zugriffsquelle`) makes a fragment that is not. `Fragment.KlassenRein` is the next predicate: every
             instruction is frame-only or an access instruction. The two classes `lesen`/`schreiben`/`rmw`
             of the access instructions are the only non-frame classes the source reaches (the lifecycle instructions
             of MK-07 have no source form), so `KlassenRein` is the predicate the generic proofs of the units of the
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

theorem expr_klassenrein (slot : Nat) (tree : Expr scope type) : (expr slot tree).KlassenRein :=
  Fragment.rein_klassenrein (expr_rein slot tree)

/-- **The code of an access form is frame-only or access.** -/
theorem accessCode_klassenrein (form : Access before after) : (accessCode form).KlassenRein := by
  cases form <;>
    simp only [accessCode, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff,
      expr_klassenrein, true_and] <;>
    first
      | exact Or.inr ⟨_, rfl⟩
      | exact ⟨Or.inr ⟨_, rfl⟩, Or.inl (Or.inl rfl)⟩


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

private theorem argsCode_klassenrein (slot : Nat) (args : List (TypedExpr scope)) : (argsCode slot args).KlassenRein := by
  induction args generalizing slot with
  | nil => exact Fragment.klassenrein_leer
  | cons value rest ih =>
    simp only [argsCode, Fragment.klassenrein_anhaengen_iff]
    exact ⟨expr_klassenrein _ _, ih _⟩

private theorem optionCode_klassenrein (slot : Nat) (value : OptionInitializer scope count) :
    (optionCode slot value).KlassenRein := by
  simp only [optionCode, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff]
  refine ⟨?_, ?_⟩
  · cases value with
    | absent => exact Fragment.klassenrein_leer
    | present value _ => exact expr_klassenrein _ _
  · first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr rfl)

theorem stmt_klassenrein (tree : Stmt result before after) : (stmt tree).KlassenRein := by
  refine @Stmt.rec result
    (fun _ _ t => (stmt t).KlassenRein)
    (fun _ _ t => (block t).KlassenRein)
    (fun _ t => (bracedBlock t).KlassenRein)
    (fun _ _ _ _ t => (variantArms t).body.KlassenRein)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after tree
  all_goals
    intros
    simp_all only [stmt, accessCode_klassenrein, block, bracedBlock, variantArms, callCode, MatchCode.prepend, Bool.false_eq_true,
      ↓reduceIte, Fragment.klassenrein_leer, Fragment.klassenrein_einzel_iff, Fragment.klassenrein_anhaengen_iff, expr_klassenrein,
      argsCode_klassenrein, optionCode_klassenrein, true_and, and_true]
  all_goals
    repeat' first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr rfl)
      | refine ⟨?_, ?_⟩

theorem bracedBlock_klassenrein (tree : BracedBlock result scope) : (bracedBlock tree).KlassenRein := by
  have both := stmt_klassenrein (Stmt.ite .trueLit tree tree)
  simp only [stmt, expr, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff] at both
  exact both.1.1.2

private theorem functionCode_klassenrein {result : Option WrittenType} {scope : Scope}
    (measure : Option (Measure scope)) (body : BracedBlock (writtenResult result) scope) :
    (functionCode result measure body).KlassenRein := by
  cases measure with
  | none =>
    simp only [functionCode, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff, Fragment.klassenrein_leer,
      bracedBlock_klassenrein, true_and]
    exact Or.inl (Or.inl rfl)
  | some m =>
    simp only [functionCode, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff, expr_klassenrein,
      bracedBlock_klassenrein, true_and]
    repeat' first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr rfl)
      | exact trivial
      | refine ⟨?_, ?_⟩

private theorem decl_klassenrein {before after : Scope} (d : Decl before after) : (decl d).KlassenRein := by
  cases d with
  | constant name ordinary written valid value staticValue fits =>
    simp only [decl, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff, expr_klassenrein, true_and]
    exact Or.inl (Or.inl rfl)
  | function name ordinary parameters result valid decreases body distinct returns effects =>
    simp only [decl, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff, functionCode_klassenrein, and_true]
    exact Or.inl (Or.inl rfl)
  | record exported name fields valid distinct =>
    simp only [decl, Fragment.klassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | tagged exported name first tail valid distinct =>
    simp only [decl, Fragment.klassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | table item =>
    simp only [decl, Fragment.klassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | effectGroup item =>
    simp only [decl, Fragment.klassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)
  | environment name abi row =>
    simp only [decl, Fragment.klassenrein_einzel_iff]
    exact Or.inl (Or.inl rfl)

private theorem unitBody_klassenrein {before after : Scope} (body : UnitBody before after) : (unitBody body).KlassenRein := by
  induction body with
  | done => exact Fragment.klassenrein_leer
  | step first rest ih =>
    simp only [unitBody, Fragment.klassenrein_anhaengen_iff]
    exact ⟨decl_klassenrein first, ih⟩

theorem programm_klassenrein (tree : Ast.Unit) : (programm tree).KlassenRein := by
  simp only [programm, Fragment.klassenrein_anhaengen_iff, Fragment.klassenrein_einzel_iff, unitBody_klassenrein, true_and]
  exact ⟨Or.inl (Or.inr rfl), Or.inl (Or.inl rfl)⟩

/-- **Every elaborated fragment of every category is frame-only.** -/
theorem fragment_klassenrein (category : Category) (tree : category.Tree) : (fragment category tree).KlassenRein := by
  cases category with
  | expression scope => exact expr_klassenrein _ _
  | statement scope result => exact stmt_klassenrein _
  | block scope result => exact bracedBlock_klassenrein _
  | unit => exact programm_klassenrein tree
  | declaration scope => exact decl_klassenrein _

end Gabbro.Core.Ast.Semantik
