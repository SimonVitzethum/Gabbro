module

public import Core.Ast.ProgramRegistry.Access
public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Semantik.ProgramObligations
public import Core.Ast.Semantik.Formen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

/-- **The swap form occurs in an elaborated unit**: an atomic exchange of cell `0` of one owned region, stepped from
     canonical initialisation to its occurrence. -/
theorem swap_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (scope : Scope) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int 0 0)) (value : Expr scope (.int 5 5)),
      (accessForm scope none).ErfuellbarAm platform start
        ⟨_, .swap name ordinary written valid region visible receiverOrdinary index value .ra⟩ := by
  let rname : Identifier := keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryR : ordinaryLocal rname := (directName_of_singleton (name := rname) rfl).1
  let xname : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryX : ordinaryLocal xname := (directName_of_singleton (name := xname) rfl).1
  have xne : xname.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro same
    cases same
  let scope : Scope := [⟨rname, .ownedRegion, false, false⟩]
  let region : Local scope .ownedRegion := .here
  let written := WrittenType.integer false 8 none
  have valid : written.valid scope := by
    change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  let index : Expr scope (.int 0 0) := Expr.lit 0
  let value : Expr scope (.int 5 5) := Expr.lit 5
  let form := (accessForm scope none)
  let a : AccessStatement scope :=
    ⟨_, .swap xname ⟨xne, ordinaryX⟩ written valid region trivial ordinaryR index value .ra⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  let s₂ := (Befehl.literal 1 5).nach eintritt s₁
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start
      ⟨Befehl.literal 0 0, rfl, rfl, rfl⟩) ⟨Befehl.literal 1 5, rfl, rfl, rfl⟩
  refine ⟨scope, xname, ⟨xne, ordinaryX⟩, written, valid, region, trivial, ordinaryR, index, value,
    Ast.print (form.produktion.tree a), s₂, Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (access_am_ort scope none) platform a s₂ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

/-- **The compare-and-swap form occurs in an elaborated unit**: a conditional atomic exchange of cell `0` of one
     owned region, stepped from canonical initialisation to its occurrence. -/
theorem cas_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (scope : Scope) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int 0 0)) (expected : Expr scope (.int 5 5)) (neu : Expr scope (.int 7 7)),
      (accessForm scope none).ErfuellbarAm platform start
        ⟨_, .vergleicheTausche name ordinary written valid region visible receiverOrdinary
          index expected neu .ra⟩ := by
  let rname : Identifier := keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryR : ordinaryLocal rname := (directName_of_singleton (name := rname) rfl).1
  let xname : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryX : ordinaryLocal xname := (directName_of_singleton (name := xname) rfl).1
  have xne : xname.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro same
    cases same
  let scope : Scope := [⟨rname, .ownedRegion, false, false⟩]
  let region : Local scope .ownedRegion := .here
  let written := WrittenType.integer false 8 none
  have valid : written.valid scope := by
    change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  let index : Expr scope (.int 0 0) := Expr.lit 0
  let expected : Expr scope (.int 5 5) := Expr.lit 5
  let neu : Expr scope (.int 7 7) := Expr.lit 7
  let form := (accessForm scope none)
  let a : AccessStatement scope :=
    ⟨_, .vergleicheTausche xname ⟨xne, ordinaryX⟩ written valid region trivial ordinaryR
      index expected neu .ra⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  let s₂ := (Befehl.literal 1 5).nach eintritt s₁
  let s₃ := (Befehl.literal 2 7).nach eintritt s₂
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start
      ⟨Befehl.literal 0 0, rfl, rfl, rfl⟩) ⟨Befehl.literal 1 5, rfl, rfl, rfl⟩)
      ⟨Befehl.literal 2 7, rfl, rfl, rfl⟩
  refine ⟨scope, xname, ⟨xne, ordinaryX⟩, written, valid, region, trivial, ordinaryR, index, expected, neu,
    Ast.print (form.produktion.tree a), s₃, Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (access_am_ort scope none) platform a s₃ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

/-- **The fetch-and-add form occurs in an elaborated unit**: an atomic addition to cell `0` of one owned region,
     stepped from canonical initialisation to its occurrence. -/
theorem fetch_add_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (scope : Scope) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int 0 0)) (betrag : Expr scope (.int 3 3)),
      (accessForm scope none).ErfuellbarAm platform start
        ⟨_, .holeUndAddiere name ordinary written valid region visible receiverOrdinary index betrag .ra⟩ := by
  let rname : Identifier := keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryR : ordinaryLocal rname := (directName_of_singleton (name := rname) rfl).1
  let xname : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryX : ordinaryLocal xname := (directName_of_singleton (name := xname) rfl).1
  have xne : xname.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro same
    cases same
  let scope : Scope := [⟨rname, .ownedRegion, false, false⟩]
  let region : Local scope .ownedRegion := .here
  let written := WrittenType.integer false 8 none
  have valid : written.valid scope := by
    change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  let index : Expr scope (.int 0 0) := Expr.lit 0
  let betrag : Expr scope (.int 3 3) := Expr.lit 3
  let form := (accessForm scope none)
  let a : AccessStatement scope :=
    ⟨_, .holeUndAddiere xname ⟨xne, ordinaryX⟩ written valid region trivial ordinaryR index betrag .ra⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  let s₂ := (Befehl.literal 1 3).nach eintritt s₁
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start
      ⟨Befehl.literal 0 0, rfl, rfl, rfl⟩) ⟨Befehl.literal 1 3, rfl, rfl, rfl⟩
  refine ⟨scope, xname, ⟨xne, ordinaryX⟩, written, valid, region, trivial, ordinaryR, index, betrag,
    Ast.print (form.produktion.tree a), s₂, Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (access_am_ort scope none) platform a s₂ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

/-- **The confirming observation occurs in an elaborated unit**: an await of cell `0` of one owned region,
     stepped from canonical initialisation to its occurrence. -/
theorem await_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (scope : Scope) (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int 0 0)) (marker : Int),
      (accessForm scope none).ErfuellbarAm platform start
        ⟨_, .erwarte name ordinary written valid region visible receiverOrdinary index marker .ra⟩ := by
  let rname : Identifier := keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryR : ordinaryLocal rname := (directName_of_singleton (name := rname) rfl).1
  let xname : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryX : ordinaryLocal xname := (directName_of_singleton (name := xname) rfl).1
  have xne : xname.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro same
    cases same
  let scope : Scope := [⟨rname, .ownedRegion, false, false⟩]
  let region : Local scope .ownedRegion := .here
  let written := WrittenType.integer false 8 none
  have valid : written.valid scope := by
    change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  let index : Expr scope (.int 0 0) := Expr.lit 0
  let marker : Int := 1
  let form := (accessForm scope none)
  let a : AccessStatement scope :=
    ⟨_, .erwarte xname ⟨xne, ordinaryX⟩ written valid region trivial ordinaryR index marker .ra⟩
  let E := form.einheit platform a
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  have reached : E.system.IErreichbar s₀ s₁ :=
    .schritt eintritt () [plan] .start ⟨Befehl.literal 0 0, rfl, rfl, rfl⟩
  refine ⟨scope, xname, ⟨xne, ordinaryX⟩, written, valid, region, trivial, ordinaryR, index, marker,
    Ast.print (form.produktion.tree a), s₁, Ast.parse_print (form.produktion.tree a), rfl, reached,
    form.realisiert (access_am_ort scope none) platform a s₁ rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

/-- **The publication form occurs in an elaborated unit**: a release store of cell `0` of one owned region,
     stepped from canonical initialisation to its occurrence. -/
theorem publish_erfuellbar (platform : Plattform) (start : AussenStart) :
    ∃ (scope : Scope) (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int 0 0)) (value : Expr scope (.int 5 5)),
      (accessForm scope none).ErfuellbarAm platform start
        ⟨_, .veroeffentliche region visible receiverOrdinary index value .ra⟩ := by
  let rname : Identifier := keywordName 'r' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryR : ordinaryLocal rname := (directName_of_singleton (name := rname) rfl).1
  let scope : Scope := [⟨rname, .ownedRegion, false, false⟩]
  let region : Local scope .ownedRegion := .here
  let index : Expr scope (.int 0 0) := Expr.lit 0
  let value : Expr scope (.int 5 5) := Expr.lit 5
  let form := (accessForm scope none)
  let a : AccessStatement scope :=
    ⟨_, .veroeffentliche region trivial ordinaryR index value .ra⟩
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

/-- **The swap statement is not trivial.** An exchange reads and writes one cell: its class writes, so a swap
    lowered to a load would lose the write the footprint covers. -/
theorem swap_nichtTrivial :
    (.tausche 0 0 0 1 (.int 0 255) .ra : Zugriffsform).klasse.schreibend = true := rfl

/-- **The compare-and-swap statement is not trivial.** A conditional exchange reads and writes one cell: its class
    writes, so lowering it to a load would lose the write the footprint covers. -/
theorem cas_nichtTrivial :
    (.vergleicheTausche 0 0 0 1 2 (.int 0 255) .ra : Zugriffsform).klasse.schreibend = true := rfl

/-- **The fetch-and-add statement is not trivial.** An addition updates one cell: its class writes, so lowering it
    to a load would lose the write the footprint covers. -/
theorem fetch_add_nichtTrivial :
    (.holeUndAddiere 0 0 0 1 (.int 0 255) .ra : Zugriffsform).klasse.schreibend = true := rfl

/-- **The confirming observation is not trivial.** It reads without writing, so lowering it to a store would
    invent a write the footprint does not cover. -/
theorem await_nichtTrivial :
    (.erwarte 0 0 0 1 (.int 0 255) .ra : Zugriffsform).klasse.schreibend = false := rfl

/-- **The publication is not trivial.** It writes the flag cell: its class writes, so lowering it to a load would
    lose the write the footprint covers. -/
theorem publish_nichtTrivial :
    (.veroeffentliche 0 0 1 .ra : Zugriffsform).klasse.schreibend = true := rfl

end Gabbro.Core.Ast.Semantik
