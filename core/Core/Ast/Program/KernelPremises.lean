module

public import Core.Ast.Semantik.ProgramRegistry

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Lean (Name)

def Befehl.programConstructor : Befehl → Option Name
  | .bindeWert .. => some ``Befehl.bindeWert
  | .definiere .. => some ``Befehl.definiere
  | .rufe .. => some ``Befehl.rufe
  | .rueckVoid .. => some ``Befehl.rueckVoid
  | .pruefeMass .. => some ``Befehl.pruefeMass
  | .setzePasszahl .. => some ``Befehl.setzePasszahl
  | .whileTest .. => some ``Befehl.whileTest
  | .forAnfang .. => some ``Befehl.forAnfang
  | .forTest .. => some ``Befehl.forTest
  | .forNaechster .. => some ``Befehl.forNaechster
  | .zurueckSprung .. => some ``Befehl.zurueckSprung
  | .starte .. => some ``Befehl.starte
  | .ende .. => some ``Befehl.ende
  | _ => none

/-- A program-level instruction is frame-only: only the access instructions are not, and they have no program constructor. -/
theorem Befehl.privat_von_programConstructor {b : Befehl} {n : Name}
    (h : b.programConstructor = some n) : b.Privat :=
  b.privat_von_kein_zugriff (fun form eq => by subst eq; cases h) (fun form eq => by subst eq; cases h)

def programConstructors : List Name :=
  [``Befehl.bindeWert,
    ``Befehl.definiere,
    ``Befehl.rufe,
    ``Befehl.rueckVoid,
    ``Befehl.pruefeMass,
    ``Befehl.setzePasszahl,
    ``Befehl.whileTest,
    ``Befehl.forAnfang,
    ``Befehl.forTest,
    ``Befehl.forNaechster,
    ``Befehl.zurueckSprung,
    ``Befehl.starte,
    ``Befehl.ende]

/-- The core instruction has a source occurrence reachable from the canonical entry. -/
def ProgramInstructionPremises (constructor : Name) (platform : Plattform) (start : AussenStart) : Prop :=
  ∃ (category : Category) (tree : category.Tree) (text : Text.RawText) (s : Zustand) (b : Befehl),
    b.programConstructor = some constructor ∧ Ast.Parse text tree ∧
    let E := elaborieren platform tree
    E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s eintritt = some b ∧
      E.system.ISchritt eintritt s () [plan] (b.nach eintritt s) ∧
      E.system.ImplSchritt eintritt s () [plan] (b.nach eintritt s)

private theorem at_source {category : Category} {tree : category.Tree}
    {platform : Plattform} {start : AussenStart} {s : Zustand} {b : Befehl}
    (tag : b.programConstructor = some constructor)
    (reach : (elaborieren platform tree).system.IErreichbar (I.start (elaborieren platform tree) start).2 s)
    (head : (elaborieren platform tree).system.kopf s eintritt = some b) :
    ProgramInstructionPremises constructor platform start :=
  ⟨category, tree, Ast.print tree, s, b, tag, Ast.parse_print tree, reach, head,
    ⟨b, head, (b.ideal_privat (Befehl.privat_von_programConstructor tag) eintritt s () [plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩,
      ⟨b, head, (b.impl_privat (Befehl.privat_von_programConstructor tag) eintritt s () [plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩⟩

private theorem Quellform.program_occurrence {category : Category} {args : Type}
    (form : Quellform category args) {platform : Plattform} {start : AussenStart}
    {a : args} (occurrence : form.ErfuellbarAm platform start a)
    (tag : (form.befehl a).programConstructor = some constructor) :
    ProgramInstructionPremises constructor platform start := by
  obtain ⟨text, s, parsed, _, reach, realized, _⟩ := occurrence
  obtain ⟨_, head, ideal, concrete⟩ := realized
  exact ⟨category, form.produktion.tree a, text, s, form.befehl a, tag, parsed, reach, head, ideal, concrete⟩

private theorem reach_step {p : Fragment} {platform : Plattform} {start : Zustand} {s : Zustand} {b : Befehl}
    (reach : (p.einheit platform).system.IErreichbar start s)
    (head : (p.einheit platform).system.kopf s eintritt = some b)
    (priv : b.Privat := by first | exact Or.inl rfl | exact Or.inr rfl | exact Quellform.privat _ _) :
    (p.einheit platform).system.IErreichbar start (b.nach eintritt s) :=
  .schritt eintritt () [plan] reach
      ⟨b, head, (b.ideal_privat priv eintritt s () [plan] (b.nach eintritt s)).2 ⟨rfl, rfl⟩⟩

private theorem while_occurrences :
    (∀ platform start, ProgramInstructionPremises ``Befehl.setzePasszahl platform start) ∧
      (∀ platform start, ProgramInstructionPremises ``Befehl.zurueckSprung platform start) := by
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)
  let a : Surface.BoundedWhileArgs [] none :=
    ⟨.trueLit, 1, 1, .lit 1, trivial, by omega, name, .braces .done⟩
  let form := boundedWhileForm [] none
  let setup : Befehl := .setzePasszahl 0 2
  let test : Befehl := form.befehl a
  have cut (platform : Plattform) (start : AussenStart) :
      let E := form.einheit platform a
      let s₀ := (I.start E start).2
      let s₁ := (Befehl.literal 0 1).nach eintritt s₀
      E.system.IErreichbar s₀ s₁ ∧ E.system.kopf s₁ eintritt = some setup := by
    dsimp only
    exact ⟨reach_step (b := .literal 0 1) .start rfl, rfl⟩
  constructor
  · intro platform start
    obtain ⟨reach, head⟩ := cut platform start
    exact at_source (tree := form.produktion.tree a) (b := setup) rfl reach head
  · intro platform start
    obtain ⟨reach, head⟩ := cut platform start
    have hs := reach_step reach head
    have hc := reach_step (b := .wahrheitswert 0 true) hs rfl
    have ht := reach_step (b := test) hc rfl
    have hb := reach_step (b := .blockEnde 0) ht rfl
    exact at_source (tree := form.produktion.tree a) (b := .zurueckSprung 3) rfl hb rfl

private theorem for_occurrences :
    (∀ platform start, ProgramInstructionPremises ``Befehl.forAnfang platform start) ∧
      (∀ platform start, ProgramInstructionPremises ``Befehl.forNaechster platform start) := by
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)
  have ordinary : ordinaryLocal name := (directName_of_singleton (name := name) rfl).1
  let a : Surface.ForRangeArgs [] none :=
    ⟨name, ordinary, 1, 1, 3, 3, .lit 1, .lit 3, ⟨trivial, trivial⟩, none, .braces .done⟩
  let form := forRangeForm [] none
  let index := (rangeBinding name 1 3).type
  let setup : Befehl := .forAnfang 0 1 index 5 false false
  have cut (platform : Plattform) (start : AussenStart) :
      let E := form.einheit platform a
      let s₀ := (I.start E start).2
      let s₂ := (Befehl.literal 1 3).nach eintritt ((Befehl.literal 0 1).nach eintritt s₀)
      E.system.IErreichbar s₀ s₂ ∧ E.system.kopf s₂ eintritt = some setup := by
    dsimp only
    exact ⟨reach_step (b := .literal 1 3) (reach_step (b := .literal 0 1) .start rfl) rfl, rfl⟩
  constructor
  · intro platform start
    obtain ⟨reach, head⟩ := cut platform start
    exact at_source (tree := form.produktion.tree a) (b := setup) rfl reach head
  · intro platform start
    obtain ⟨reach, head⟩ := cut platform start
    have hs := reach_step reach head
    have ht := reach_step (b := form.befehl a) hs rfl (form.privat a)
    have hb := reach_step (b := .blockEnde 0) ht rfl
    exact at_source (tree := form.produktion.tree a) (b := .forNaechster 2 index) rfl hb rfl

private theorem unit_occurrences :
    (∀ platform start, ProgramInstructionPremises ``Befehl.pruefeMass platform start) ∧
      (∀ platform start, ProgramInstructionPremises ``Befehl.ende platform start) := by
  have ordinary : directName mainName := mainName_direct
  let main : Decl [] [] := .function mainName ordinary [] none (by intro _ h; cases h)
    (some ⟨0, 0, .lit 0, by omega⟩) (.braces .done) List.nodup_nil (by intro h; cases h) none
  let unit : Ast.Unit := ⟨[], .step main .done⟩
  let define : Befehl := .definiere mainName [] none 0 5 true [] none
  have cut (platform : Plattform) (start : AussenStart) :
      let E := elaborieren platform (category := .unit) unit
      let s₀ := (I.start E start).2
      let s₁ := define.nach eintritt s₀
      let s₂ := (Befehl.starte mainName).nach eintritt s₁
      let s₃ := (Befehl.literal 0 0).nach eintritt s₂
      E.system.IErreichbar s₀ s₃ ∧ E.system.kopf s₃ eintritt = some (.pruefeMass 0) := by
    dsimp only
    refine ⟨reach_step (b := .literal 0 0) (reach_step (b := .starte mainName)
      (reach_step (b := define) .start rfl) rfl) rfl, rfl⟩
  constructor
  · intro platform start
    obtain ⟨reach, head⟩ := cut platform start
    exact at_source (category := .unit) (tree := unit) rfl reach head
  · intro platform start
    obtain ⟨reach, head⟩ := cut platform start
    have hm := reach_step reach head
    have hb := reach_step (b := .blockEnde 0) hm rfl
    have hr := reach_step (b := .rueckVoid) hb rfl
    exact at_source (category := .unit) (tree := unit) (b := .ende) rfl hr rfl

theorem programInstruction_erfuellbar (constructor : Name) (registered : constructor ∈ programConstructors) :
    ∀ platform start, ProgramInstructionPremises constructor platform start := by
  simp only [programConstructors, List.mem_cons, List.not_mem_nil, or_false] at registered
  rcases registered with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro platform start
    obtain ⟨scope, _, occurrence⟩ := constant_erfuellbar platform start
    exact (constantForm scope).program_occurrence occurrence rfl
  · intro platform start
    obtain ⟨scope, _, occurrence⟩ := function_erfuellbar platform start
    exact (functionForm scope).program_occurrence occurrence rfl
  · intro platform start
    obtain ⟨ctx, _, occurrence, _⟩ := directCall_erfuellbar platform start
    exact (directCallForm ctx.1 ctx.2).program_occurrence occurrence rfl
  · intro platform start
    obtain ⟨_, occurrence⟩ := returnVoid_erfuellbar platform start
    exact (returnVoidForm [] none).program_occurrence occurrence rfl
  · exact unit_occurrences.1
  · exact while_occurrences.1
  · intro platform start
    obtain ⟨ctx, _, occurrence⟩ := boundedWhile_erfuellbar platform start
    exact (boundedWhileForm ctx.1 ctx.2).program_occurrence occurrence rfl
  · exact for_occurrences.1
  · intro platform start
    obtain ⟨ctx, _, occurrence⟩ := forRange_erfuellbar platform start
    exact (forRangeForm ctx.1 ctx.2).program_occurrence occurrence rfl
  · exact for_occurrences.2
  · exact while_occurrences.2
  · intro platform start
    obtain ⟨_, occurrence, _⟩ := program_erfuellbar platform start
    exact programForm.program_occurrence occurrence rfl
  · exact unit_occurrences.2

end Gabbro.Core.Ast.Semantik
