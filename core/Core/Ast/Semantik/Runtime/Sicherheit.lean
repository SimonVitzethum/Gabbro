module

public import Core.Ast.Semantik.Pflichten
public import Core.Ast.Semantik.Runtime.Mehrkontext.System
public import Core.Sicherheit.Regel

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Sicherheit Katalog

def Fragment.sicherheitsEinheit (p : Fragment) (platform : Plattform) :
    Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl :=
  ⟨p.einheit platform, p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩)⟩

theorem Befehl.sicher (p : Fragment) (platform : Plattform)
    (keine : p.klauseln.invariant = []) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
    RegelSicher (p.sicherheitsEinheit platform) b := by
  intro H ρ t c w vor zwischen nach stepPlan spur head impl execute
  obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) impl execute h
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Zelle Int) := List.not_mem_nil
  have wirkungen :
      NeueWirkungen vor (b.nach c vor) (⟨[], []⟩ : SchrittSpur Zelle Int) [] :=
    Or.inr ⟨ohneAbsturz, (List.append_nil _).symm⟩
  refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, fun ordered => ordered, ?_, ?_⟩
  · intro i actor access recorded _
    cases recorded
  · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
    intro _ obj alive lost
    exact nomatch alive.symm.trans lost
  · intro _
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared _
    change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at declared
    rw [keine] at declared
    cases declared
  · intro _ l changeOwner
    exact (changeOwner rfl).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩

/-- The local value transfer leaves the question ledger and its authority unchanged. -/
theorem Befehl.antwortSicher (p : Fragment) (platform : Plattform) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
    Sicherheit.RegelAntwortSicher (p.sicherheitsEinheit platform) b := by
  intro t c w vor zwischen nach stepPlan spur _ impl execute befugt
  obtain ⟨_, rfl⟩ := b.vollzug_genau (w := w) impl execute h
  exact befugt

theorem Befehl.sicherheitsPflichten (p : Fragment) (platform : Plattform)
    (keine : p.klauseln.invariant = []) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
    RegelPflichten (p.sicherheitsEinheit platform) b :=
  ⟨b.sicher p platform keine h, b.antwortSicher p platform h⟩

/-- **Every form carries the safety duties of its unit when the code of the unit is frame-only.** A form that is
    not frame-only never stands at a head of a unit whose code is, so its duties are vacuous; a frame-only form pays
    its class (`Befehl.sicherheitsPflichten`). An access instruction owes the memory legs of its class
    (`KlassenSicherheitAussage`) and the race leg (`RennfreiAusLokalAussage`) instead. -/
theorem Fragment.sicherheitsPflichten_alle (p : Fragment) (platform : Plattform)
    (keine : p.klauseln.invariant = []) (rein : ∀ b ∈ p.code, b.Privat) (f : Befehl) :
    RegelPflichten (p.sicherheitsEinheit platform) f := by
  by_cases h : f.Privat
  · exact f.sicherheitsPflichten p platform keine h
  · refine ⟨?_, ?_⟩
    · intro H ρ t c w vor zwischen nach plan spur head
      exact absurd (rein f (kopf_mem (code := p.code) head)) h
    · intro t c w vor zwischen nach plan spur head
      exact absurd (rein f (kopf_mem (code := p.code) head)) h

theorem expr_keine_invarianten (slot : Nat) (tree : Expr scope type) :
    (expr slot tree).klauseln.invariant = [] := by
  refine @Expr.rec scope
    (fun _ t => ∀ i, (expr i t).klauseln.invariant = [])
    (fun _ t => ∀ i, (itemCode i t).klauseln.invariant = [])
    (fun _ _ t => ∀ i, (labeledCode i t).klauseln.invariant = [])
    (fun _ t => ∀ i, (caseCode i t).klauseln.invariant = [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ type tree slot
  all_goals
    intros
    simp_all only [expr, itemCode, labeledCode, caseCode, Fragment.leer, Fragment.anhaengen,
      Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer, List.nil_append]

private theorem argsCode_keine_invarianten (slot : Nat) (args : List (TypedExpr scope)) :
    (argsCode slot args).klauseln.invariant = [] := by
  induction args generalizing slot with
  | nil => rfl
  | cons value rest ih =>
    simp only [argsCode, Fragment.anhaengen, Quellklauseln.anhaengen,
      expr_keine_invarianten, ih, List.nil_append]

private theorem optionCode_keine_invarianten (slot : Nat) (value : OptionInitializer scope count) :
    (optionCode slot value).klauseln.invariant = [] := by
  cases value <;>
    simp only [optionCode, optionOperand, Fragment.leer, Fragment.anhaengen, Fragment.einzel,
      Quellklauseln.anhaengen, Quellklauseln.leer, expr_keine_invarianten, List.nil_append]

theorem stmt_keine_invarianten (tree : Stmt result before after) :
    (stmt tree).klauseln.invariant = [] := by
  refine @Stmt.rec result
    (fun _ _ t => (stmt t).klauseln.invariant = [])
    (fun _ _ t => (block t).klauseln.invariant = [])
    (fun _ t => (bracedBlock t).klauseln.invariant = [])
    (fun _ _ _ _ t => (variantArms t).body.klauseln.invariant = [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after tree
  all_goals
    intros
    simp_all only [stmt, block, bracedBlock, variantArms, callCode, MatchCode.prepend, Bool.false_eq_true,
      ↓reduceIte, Fragment.leer, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
      Quellklauseln.leer, expr_keine_invarianten, argsCode_keine_invarianten,
      optionCode_keine_invarianten, List.nil_append]

theorem bracedBlock_keine_invarianten (tree : BracedBlock result scope) :
    (bracedBlock tree).klauseln.invariant = [] := by
  have both := stmt_keine_invarianten (Stmt.ite .trueLit tree tree)
  simp only [stmt, expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
    Quellklauseln.leer, List.nil_append, List.append_nil] at both
  exact (List.eq_nil_of_append_eq_nil both).1

private theorem functionCode_keine_invarianten {result : Option WrittenType} {scope : Scope}
    (measure : Option (Measure scope)) (body : BracedBlock (writtenResult result) scope) :
    (functionCode result measure body).klauseln.invariant = [] := by
  cases measure with
  | none =>
      simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Fragment.leer,
        Quellklauseln.anhaengen, Quellklauseln.leer, List.nil_append,
        bracedBlock_keine_invarianten]
  | some m =>
      simp only [functionCode, Fragment.anhaengen, Fragment.einzel, Fragment.leer,
        Quellklauseln.anhaengen, Quellklauseln.leer, List.nil_append,
        expr_keine_invarianten, bracedBlock_keine_invarianten]

private theorem decl_keine_invarianten {before after : Scope} (d : Decl before after) :
    (decl d).klauseln.invariant = [] := by
  cases d with
  | constant name ordinary written valid value staticValue fits =>
      simp only [decl, Fragment.anhaengen, Fragment.einzel, Fragment.leer,
        Quellklauseln.anhaengen, Quellklauseln.leer, List.nil_append,
        expr_keine_invarianten]
  | function name ordinary parameters result valid decreases body distinct returns effects =>
      simp only [decl, Fragment.anhaengen, Fragment.einzel, Fragment.leer,
        Quellklauseln.anhaengen, Quellklauseln.leer, List.nil_append,
        functionCode_keine_invarianten]
  | record exported name fields valid distinct => rfl
  | tagged exported name first tail valid distinct => rfl
  | table item => rfl
  | effectGroup item => rfl
  | environment name abi row => rfl

private theorem unitBody_keine_invarianten {before after : Scope} (body : UnitBody before after) :
    (unitBody body).klauseln.invariant = [] := by
  induction body with
  | done => rfl
  | step first rest ih =>
      simp only [unitBody, Fragment.anhaengen, Quellklauseln.anhaengen,
        List.nil_append, decl_keine_invarianten, ih]

theorem programm_keine_invarianten (tree : Ast.Unit) :
    (programm tree).klauseln.invariant = [] := by
  simp only [programm, Fragment.anhaengen, Fragment.einzel, Fragment.leer,
    Quellklauseln.anhaengen, Quellklauseln.leer, List.nil_append, unitBody_keine_invarianten]

end Gabbro.Core.Ast.Semantik
