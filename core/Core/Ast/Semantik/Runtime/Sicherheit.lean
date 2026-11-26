module

public import Core.Ast.Semantik.Pflichten
public import Core.Ast.Semantik.Runtime.Mehrkontext.System
public import Core.Sicherheit.Regel
public import Core.Ast.Semantik.Runtime.Praedikat

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Sicherheit Katalog

def Fragment.sicherheitsEinheit (p : Fragment) (platform : Plattform) :
    Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl :=
  ⟨p.einheit platform, p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩)⟩

theorem Befehl.sicher (p : Fragment) (platform : Plattform) (ps : List Praedikat)
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (ok : ∀ b ∈ p.code, pruefeBefehlErhalt ps b = true) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Quellform.privat _ _) :
    RegelSicher (p.sicherheitsEinheit platform) b := by
  intro H ρ t c w vor zwischen nach plan spur head impl execute
  obtain ⟨hspur, _, hstatus, _, _, _, _, hinitial, hgraph, hbuchung,
    hrechte, _, _, _, _, hsperren⟩ :=
    b.vollzug_genau_privat h (w := w) impl execute
  subst hspur
  obtain ⟨_, hnach⟩ := (b.impl_privat h c vor w [plan] zwischen).1 impl
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Zelle Int) := List.not_mem_nil
  have hub : nach.buchung = vor.buchung := by rw [hbuchung, hnach]; rfl
  have wirkungen :
      NeueWirkungen vor nach (⟨[], []⟩ : SchrittSpur Zelle Int) [] :=
    Or.inr ⟨ohneAbsturz, by rw [hub, List.append_nil]⟩
  have hgr : vor.graph = nach.graph := by rw [hgraph, hnach]; rfl
  refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, fun ordered => hgr ▸ ordered, ?_, ?_⟩
  · intro i actor l recorded _
    cases recorded
  · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
    intro _ obj alive lost
    have hrech : nach.rechte = vor.rechte := by rw [hrechte, hnach]; rfl
    rw [hrech] at lost
    exact nomatch alive.symm.trans lost
  · intro vorSicher
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared writersNach
    change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at declared
    rw [tab, List.getElem?_map] at declared
    obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp declared
    rw [List.getElem?_map] at hinner
    obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
    rw [← tab, ← List.getElem?_map] at declared
    have hstNach : ∀ c', vor.status c' = .laeuft → nach.status c' = .laeuft := by
      intro c' hst
      rw [hstatus, hnach]
      exact hst
    have writersVor : ∀ c', vor.status c' = .laeuft → ¬ vor.buchung.schreibt c' i := by
      intro c' hst
      have h1 := writersNach c' (hstNach c' hst)
      rw [hub] at h1
      exact h1
    have vorGilt : q.gilt vor := vorSicher.2 i _ declared writersVor
    have hinit : nach.initial = vor.initial := by rw [hinitial, hnach]; rfl
    exact q.gilt_of_initial vor nach hinit.symm vorGilt
  · intro _ l changeOwner
    have hbes : (nach.sperren l).besitzer = (vor.sperren l).besitzer := by
      rw [hsperren, hnach]; rfl
    exact (changeOwner hbes.symm).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩

/-- The local value transfer leaves the question ledger and its authority unchanged: the machine
    step keeps the questions, answers, epoch and outside ledger, so pending authority carries over. -/
theorem Befehl.antwortSicher (p : Fragment) (platform : Plattform) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Quellform.privat _ _) :
    Sicherheit.RegelAntwortSicher (p.sicherheitsEinheit platform) b := by
  intro t c w vor zwischen nach stepPlan spur _ impl execute befugt
  obtain ⟨hspur, _, _, hfragen, hantworten, _, _, _, _, hbuchung, _, _, _, hepoche, _⟩ :=
    b.vollzug_genau_privat h (w := w) impl execute
  subst hspur
  obtain ⟨_, hnach⟩ := (b.impl_privat h c vor w [stepPlan] zwischen).1 impl
  have hfr : nach.fragen = vor.fragen := by rw [hfragen, hnach]; rfl
  have hep : nach.epoche = vor.epoche := by rw [hepoche, hnach]; rfl
  have hant : nach.antworten = vor.antworten := by rw [hantworten, hnach]; rfl
  have hb : nach.buchung = vor.buchung := by rw [hbuchung, hnach]; rfl
  intro q mem le unanswered
  rw [hfr] at mem
  rw [hep] at le
  rw [hant] at unanswered
  obtain ⟨⟨c', nummer, griffe⟩, register⟩ := befugt q mem le unanswered
  refine ⟨⟨c', nummer, ?_⟩, ?_⟩
  · intro z hz
    have hz' := griffe z hz
    simp only [EigeneGriffe, hb] at hz' ⊢
    exact hz'
  · intro reg
    have hr := register reg
    simp only [RegisterErlaubt, hb] at hr ⊢
    exact hr

theorem Befehl.sicherheitsPflichten (p : Fragment) (platform : Plattform)
    (ps : List Praedikat)
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (ok : ∀ b ∈ p.code, pruefeBefehlErhalt ps b = true) (b : Befehl)
    (h : b.Privat := by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Quellform.privat _ _) :
    RegelPflichten (p.sicherheitsEinheit platform) b :=
  ⟨b.sicher p platform ps tab ok h, b.antwortSicher p platform h⟩

/-- **Every form carries the safety duties of its unit when the code of the unit is frame-only.** A form that is
    not frame-only never stands at a head of a unit whose code is, so its duties are vacuous; a frame-only form pays
    its class (`Befehl.sicherheitsPflichten`). An access instruction owes the memory legs of its class
    (`KlassenSicherheitAussage`) and the race leg (`RennfreiAusLokalAussage`) instead. -/
theorem Fragment.sicherheitsPflichten_alle (p : Fragment) (platform : Plattform)
    (ps : List Praedikat)
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (ok : ∀ b ∈ p.code, pruefeBefehlErhalt ps b = true)
    (rein : ∀ b ∈ p.code, b.Privat) (f : Befehl) :
    RegelPflichten (p.sicherheitsEinheit platform) f := by
  by_cases h : f.Privat
  · exact f.sicherheitsPflichten p platform ps tab ok h
  · refine ⟨?_, ?_⟩
    · intro H ρ t c w vor zwischen nach plan spur head
      exact absurd (rein f (kopf_mem head)) h
    · intro t c w vor zwischen nach plan spur head
      exact absurd (rein f (kopf_mem head)) h

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

theorem accessCode_keine_invarianten (form : Access before after) :
    (accessCode form).klauseln.invariant = [] := by
  cases form <;>
    simp only [accessCode, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen, Quellklauseln.leer,
      expr_keine_invarianten, List.nil_append, List.append_nil]

private theorem Fragment.anhaengen_invariant (a b : Fragment) :
    (a.anhaengen b).klauseln.invariant = a.klauseln.invariant ++ b.klauseln.invariant := rfl

theorem stmt_keine_invarianten (tree : Stmt result before after) :
    (stmt tree).klauseln.invariant = [] := by
  refine @Stmt.rec result
    (fun _ _ t => (stmt t).klauseln.invariant = [])
    (fun _ _ t => (block t).klauseln.invariant = [])
    (fun _ t => (bracedBlock t).klauseln.invariant = [])
    (fun _ _ _ _ t => (variantArms t).body.klauseln.invariant = [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after tree
  all_goals
    intros
    simp_all only [stmt, block, bracedBlock, variantArms, callCode, MatchCode.prepend, Bool.false_eq_true,
      ↓reduceIte, Fragment.leer, Fragment.anhaengen_invariant, Fragment.einzel, Quellklauseln.anhaengen,
      Quellklauseln.leer, expr_keine_invarianten, accessCode_keine_invarianten, argsCode_keine_invarianten,
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
