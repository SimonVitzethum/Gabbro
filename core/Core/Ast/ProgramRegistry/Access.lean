/-
  File:      core/Core/Ast/ProgramRegistry/Access.lean
  Subject:   THE REGISTRY PROOFS OF THE ACCESS STATEMENTS (MK-04b). `mem load` and `mem store` elaborate to ONE
              access instruction each (`accessCode`): the index (and the value) are evaluated into the temporaries
              `0` (and `1`), then a load or a store names the region by the position of its owner local. The nine
              statements of the frame (`Zugriffsquelle`) hold for both: the grammar proof mirrors the surface entry,
              the elaboration is definitional, the occurrence is the end of the evaluated operands, and the joint
              satisfiability exhibits a load and a store over one owned region in a unit stepped from canonical
              initialisation. Neither form is trivial: a load reads without writing, a store writes.
-/
module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

-- Mirror assignVar_parse using the corresponding surface entry.
theorem access_parse (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.access_entry args result).parse lexed production

-- Mirror forRange_elaboriert at the compositional access fragment.
theorem access_elaboriert (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

/-- The access instruction is at the end of the evaluated operands: after the index for a load, after the
    index and the value for a store. -/
theorem access_am_ort (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).RegelAmOrt := by
  intro ⟨after, form⟩
  cases form with
  | load name ordinary written valid region visible receiverOrdinary index mode =>
    change ((((expr 0 index).anhaengen
      (.einzel (Befehl.zugriff (.lade 0 region.index 0 written.type mode.modus)))).anhaengen
      (.einzel (Befehl.bindeWert 0 written.type false))).code[(expr 0 index).code.length]? =
      some (Befehl.zugriff (.lade 0 region.index 0 written.type mode.modus)))
    simp only [Fragment.anhaengen, Fragment.einzel]
    have hlt : (expr 0 index).code.length <
      ((expr 0 index).code ++ [Befehl.zugriff (.lade 0 region.index 0 written.type mode.modus)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.getElem?_append_left hlt]
    rw [List.getElem?_append_right]
    · simp only [Nat.sub_self, List.getElem?_cons_zero]
    · omega
  | store region visible receiverOrdinary index value mode =>
    change ((((expr 0 index).anhaengen (expr 1 value)).anhaengen
      (.einzel (Befehl.zugriff (.speichere region.index 0 1 mode.modus)))).code[(expr 0 index).code.length + (expr 1 value).code.length]? =
      some (Befehl.zugriff (.speichere region.index 0 1 mode.modus)))
    simp only [Fragment.anhaengen, Fragment.einzel]
    rw [List.getElem?_append_right]
    · simp only [List.length_append, List.length_cons, List.length_nil, Nat.sub_self,
        List.getElem?_cons_zero]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega

-- Mirror forRange_realisiert at the actual access instruction.
theorem access_realisiert (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  exact (accessForm scope result).realisiert (access_am_ort scope result) platform args s running active live atPc

theorem access_annahme (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).AnnahmeAussage :=
  (accessForm scope result).annahme

theorem access_ideal (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).IdealAussage :=
  (accessForm scope result).ideal (access_am_ort scope result)

theorem access_einheit (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).EinheitAussage :=
  (accessForm scope result).einheitAussage

theorem access_impl (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).ImplAussage :=
  (accessForm scope result).impl

theorem access_erhaltung (scope : Scope) (result : Option (Ty .value)) :
    (accessForm scope result).ErhaltungsAussage :=
  (accessForm scope result).erhaltung

/-- **The load form occurs in an elaborated unit**: a load of cell `0` of one owned region, stepped from
    canonical initialisation to its occurrence. -/
theorem load_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (scope : Scope) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int 0 0)),
      (accessForm scope none).ErfuellbarAm platform start
        ⟨_, .load name ordinary written valid region visible receiverOrdinary index .na⟩ := by
  let rname : Identifier := keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryR : ordinaryLocal rname := (directName_of_singleton (name := rname) rfl).1
  let xname : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryX : ordinaryLocal xname := (directName_of_singleton (name := xname) rfl).1
  have xne : xname.val ≠ "mut".toList := by decide
  let scope : Scope := [⟨rname, .ownedRegion, false, false⟩]
  let region : Local scope .ownedRegion := .here
  let written := WrittenType.integer false 8 none
  have valid : written.valid scope := by
    change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  let index : Expr scope (.int 0 0) := Expr.lit 0
  let form := (accessForm scope none)
  let a : AccessStatement scope :=
    ⟨_, .load xname ⟨xne, ordinaryX⟩ written valid region trivial ordinaryR index .na⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  have reached : E.system.IErreichbar s₀ s₁ :=
    .schritt eintritt () [plan] .start ⟨Befehl.literal 0 0, rfl, rfl, rfl⟩
  refine ⟨scope, xname, ⟨xne, ordinaryX⟩, written, valid, region, trivial, ordinaryR, index,
    Ast.print (form.produktion.tree a), s₁, Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (access_am_ort scope none) platform a s₁ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

/-- **The store form occurs in an elaborated unit**: a store to cell `0` of one owned region, stepped from
    canonical initialisation to its occurrence. -/
theorem store_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (scope : Scope) (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int 0 0)) (value : Expr scope (.int 5 5)),
      (accessForm scope none).ErfuellbarAm platform start
        ⟨_, .store region visible receiverOrdinary index value .na⟩ := by
  let rname : Identifier := keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryR : ordinaryLocal rname := (directName_of_singleton (name := rname) rfl).1
  let scope : Scope := [⟨rname, .ownedRegion, false, false⟩]
  let region : Local scope .ownedRegion := .here
  let index : Expr scope (.int 0 0) := Expr.lit 0
  let value : Expr scope (.int 5 5) := Expr.lit 5
  let form := (accessForm scope none)
  let a : AccessStatement scope :=
    ⟨_, .store region trivial ordinaryR index value .na⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  let s₂ := (Befehl.literal 1 5).nach eintritt s₁
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start
      ⟨Befehl.literal 0 0, rfl, rfl, rfl⟩) ⟨Befehl.literal 1 5, rfl, rfl, rfl⟩
  refine ⟨scope, region, trivial, ordinaryR, index, value,
    Ast.print (form.produktion.tree a), s₂, Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (access_am_ort scope none) platform a s₂ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

/-- **The load statement is not trivial.** A load reads without writing: its class does not write, so a load
    lowered to a store would invent a write the footprint does not cover. -/
theorem load_nichtTrivial :
    (.lade 0 0 0 (.int 0 255) .na : Zugriffsform).klasse.schreibend = false := rfl

/-- **The store statement is not trivial.** A store writes: its class writes, so a store lowered to a load
    would lose the write the footprint covers. -/
theorem store_nichtTrivial :
    (.speichere 0 0 1 .na : Zugriffsform).klasse.schreibend = true := rfl

-- Mirror forRange_erfuellbar through the load witness.
theorem access_erfuellbar : accessJoint := by
  intro platform start
  obtain ⟨scope, name, ordinary, written, valid, region, visible, receiverOrdinary, index, h⟩ :=
    load_erfuellbar platform start
  exact ⟨(scope, none),
    ⟨_, .load name ordinary written valid region visible receiverOrdinary index .na⟩, h⟩

def accessProofs : RegistryEntry ``Stmt.access
    ⟨.surface, Zugriffsquelle.statements (Context := StatementContext) (fun ctx => accessForm ctx.1 ctx.2) accessJoint ``Stmt.access⟩ where
  realization := .surface (fun ctx => access_parse ctx.1 ctx.2) (fun ctx => access_elaboriert ctx.1 ctx.2) (fun ctx => access_realisiert ctx.1 ctx.2)
  acceptanceRule := fun ctx => access_annahme ctx.1 ctx.2
  idealRule := fun ctx => access_ideal ctx.1 ctx.2
  unitsAndCommutation := fun ctx => access_einheit ctx.1 ctx.2
  implementationRule := fun ctx => access_impl ctx.1 ctx.2
  preservation := fun ctx => access_erhaltung ctx.1 ctx.2
  jointlySatisfiable := access_erfuellbar

def accessEntry : RegistryEntry ``Stmt.access (stmtSchema ``Stmt.access) := by
  rw [stmtSchema,
    if_neg (differentLabels (a := "access") (b := "letValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "assignVar") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "ret") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "ite") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "retVoid") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "letMutable") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "directCall") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "bindDirect") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "whileBounded") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "forRange") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "tupleBind") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "assignField") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "letMutableValue") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "variantMatch") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "letOption") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "retOption") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "access") (b := "forever") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact accessProofs

end Gabbro.Core.Ast.Semantik
