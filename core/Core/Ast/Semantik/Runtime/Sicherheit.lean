module

public import Core.Ast.Semantik.Pflichten
public import Core.Sicherheit.Regel
public import Core.Ast.Pruefung.Praedikat

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Sicherheit Katalog

def Fragment.sicherheitsEinheit (p : Fragment) (platform : Plattform) :
    Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl :=
  ⟨p.einheit platform, p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩)⟩

theorem Befehl.sicher (p : Fragment) (platform : Plattform) (ps : List Pruefung.Praedikat)
    (tab : p.klauseln.invariant = ps.map Pruefung.Praedikat.gilt)
    (ok : ∀ b ∈ p.code, Pruefung.pruefeBefehlErhalt ps b = true) (b : Befehl) :
    RegelSicher (p.sicherheitsEinheit platform) b := by
  intro H ρ t c w vor zwischen nach plan spur head impl execute
  obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) impl execute
  have okB := ok b (kopf_mem p.code vor c b head)
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
  · intro vorSicher
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared writersNach
    change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at declared
    rw [tab, List.getElem?_map] at declared
    obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp declared
    rw [List.getElem?_map] at hinner
    obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
    rw [← List.getElem?_map] at declared
    have hok := Pruefung.pruefeBefehlErhalt_richtig ps b q
      (List.mem_of_getElem? hsome) okB
    have writersVor : ∀ c', vor.status c' = .laeuft → ¬ vor.buchung.schreibt c' i :=
      writersNach
    have vorGilt : q.gilt vor := vorSicher.2 i _ declared writersVor
    exact q.gilt_nach b c vor hok vorGilt
  · intro _ l changeOwner
    exact (changeOwner rfl).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩

/-- The local value transfer leaves the question ledger and its authority unchanged. -/
theorem Befehl.antwortSicher (p : Fragment) (platform : Plattform) (b : Befehl) :
    Sicherheit.RegelAntwortSicher (p.sicherheitsEinheit platform) b := by
  intro t c w vor zwischen nach stepPlan spur _ impl execute befugt
  obtain ⟨_, rfl⟩ := b.vollzug_genau (w := w) impl execute
  exact befugt

theorem Befehl.sicherheitsPflichten (p : Fragment) (platform : Plattform)
    (ps : List Pruefung.Praedikat)
    (tab : p.klauseln.invariant = ps.map Pruefung.Praedikat.gilt)
    (ok : ∀ b ∈ p.code, Pruefung.pruefeBefehlErhalt ps b = true) (b : Befehl) :
    RegelPflichten (p.sicherheitsEinheit platform) b :=
  ⟨b.sicher p platform ps tab ok, b.antwortSicher p platform⟩

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

end Gabbro.Core.Ast.Semantik
