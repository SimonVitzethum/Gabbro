module

public import Core.Ast.LowLevel.Obligations
public import Core.Ast.LowLevel.Proofs.Syntax
public import Core.Ast.LowLevel.Proofs.Elaboration
public import Core.Ast.LowLevel.Proofs.Execution
public import Core.Ast.LowLevel.Proofs.Preservation
public import Core.Ast.LowLevel.Proofs.Meaning
public import Core.Ast.LowLevel.Proofs.Satisfiability
public import Core.Ast.LowLevel.Proofs.EnvironmentPacket
public import Core.Ast.Semantik.Formen
public import Core.Ast.Semantik.Kernregister

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

/-- The full low-level promise for an occurrence: every obligation of the form
    and its form-specific meaning hold jointly. The component proofs are shared
    across all forms; only the printer and the satisfiability witnesses are
    form-specific. -/

theorem addressType_aussage : AddressTypeAussage := by
  unfold AddressTypeAussage MeaningAussage
  constructor
  · exact ⟨parseAussage .addressType, inversionAussage .addressType,
      eindeutigAussage .addressType, druckAussage_addressType,
      elaboriert_form .addressType, realisiert_form .addressType,
      annahme_form .addressType, execution_ideal .addressType,
      execution_einheit .addressType, execution_impl .addressType,
      execution_fortschritt .addressType, erhaltung .addressType,
      regelSicher .addressType, regelAntwortSicher .addressType,
      aussenLokal .addressType, kosten .addressType,
      addressType_erfuellbar⟩
  · exact addressTypeMeaning

theorem regionAddress_aussage : RegionAddressAussage := by
  unfold RegionAddressAussage MeaningAussage
  constructor
  · exact ⟨parseAussage .regionAddress, inversionAussage .regionAddress,
      eindeutigAussage .regionAddress, druckAussage_regionAddress,
      elaboriert_form .regionAddress, realisiert_form .regionAddress,
      annahme_form .regionAddress, execution_ideal .regionAddress,
      execution_einheit .regionAddress, execution_impl .regionAddress,
      execution_fortschritt .regionAddress, erhaltung .regionAddress,
      regelSicher .regionAddress, regelAntwortSicher .regionAddress,
      aussenLokal .regionAddress, kosten .regionAddress,
      regionAddress_erfuellbar⟩
  · exact regionAddressMeaning

theorem environment_aussage : EnvironmentAussage := by
  unfold EnvironmentAussage MeaningAussage
  constructor
  · exact ⟨parseAussage .environment, inversionAussage .environment,
      eindeutigAussage .environment, druckAussage_environment,
      elaboriert_form .environment, realisiert_form .environment,
      annahme_form .environment, execution_ideal .environment,
      execution_einheit .environment, execution_impl .environment,
      execution_fortschritt .environment, erhaltung .environment,
      regelSicher .environment, regelAntwortSicher .environment,
      aussenLokal .environment, kosten .environment,
      environment_erfuellbar⟩
  · exact environmentMeaning

end Gabbro.Core.Ast.LowLevel

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Waechter

/-- The environment declaration is proved; bundle its component obligations into
    the typed registry entry for its surface form. -/
def environmentProofs : RegistryEntry ``Decl.environment
    ⟨.surface, Quellform.statements (Context := PUnit) (fun _ => environmentUnitForm)
      EnvironmentUnitErfuellbarAussage ``Decl.environment⟩ where
  realization := .surface (fun _ => environmentUnit_parse) (fun _ _ _ => rfl)
    (fun _ => environmentUnit_realisiert)
  acceptanceRule := fun _ => environmentUnit_annahme
  idealRule := fun _ => environmentUnit_ideal
  unitsAndCommutation := fun _ => environmentUnit_einheit
  implementationRule := fun _ => environmentUnit_impl
  preservation := fun _ => environmentUnit_erhaltung
  jointlySatisfiable := environmentUnit_erfuellbar

def environmentDeclEntry : RegistryEntry ``Decl.environment (declSchema ``Decl.environment) := by
  rw [declSchema,
    if_neg (differentLabels (a := "environment") (b := "constant") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "environment") (b := "function") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "environment") (b := "record") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "environment") (b := "tagged") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "environment") (b := "table") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "environment") (b := "effectGroup") (by intro same; simp only [String.reduceEq] at same)),
    if_pos rfl]
  exact environmentProofs

/-- The core instruction inherits the environment declaration's proofs. -/
def environmentBefehlProofs : RegistryEntry ``Befehl.waehleUmgebung
    ⟨.core, Quellform.kernStatements (Context := PUnit) (fun _ => environmentUnitForm)
      EnvironmentUnitErfuellbarAussage ``Befehl.waehleUmgebung⟩ :=
  Quellform.kernEintrag (constructor := ``Befehl.waehleUmgebung) environmentProofs

theorem waehleUmgebung_nicht_program : ``Befehl.waehleUmgebung ∉ programConstructors := by
  simp only [programConstructors, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, or_false]
  exact ⟨differentLabels (a := "waehleUmgebung") (b := "bindeWert") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "definiere") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "rufe") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "rueckVoid") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "pruefeMass") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "setzePasszahl") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "whileTest") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "forAnfang") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "forTest") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "forNaechster") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "zurueckSprung") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "starte") (by intro same; simp only [String.reduceEq] at same),
    differentLabels (a := "waehleUmgebung") (b := "ende") (by intro same; simp only [String.reduceEq] at same)⟩

def environmentBefehlEntry : RegistryEntry ``Befehl.waehleUmgebung
    (befehlSchema ``Befehl.waehleUmgebung) := by
  rw [befehlSchema,
    if_neg (differentLabels (a := "waehleUmgebung") (b := "literal") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "binaer") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "binden") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "wahrheitswert") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "lesen") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "negativ") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "negieren") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "verneinen") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "teilen") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "vergleichen") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "springeWenn") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "zuweisen") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "zurueck") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "springe") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "blockEnde") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "baueArray") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "liesArray") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "baueTupel") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "liesTupelfeld") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "baueRecord") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "liesRecordFeld") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "bindeTupel") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "setzeRecordFeld") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "definiereRecord") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "baueVariante") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "waehleVariante") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "definiereVariante") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "textLiteral") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "textConcat") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "textIndex") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "textLength") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "substring") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "definiereTraeger") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "optionIstBesetzt") (by intro same; simp only [String.reduceEq] at same)),
    if_neg (differentLabels (a := "waehleUmgebung") (b := "definiereEffektgruppe") (by intro same; simp only [String.reduceEq] at same)),
    if_neg waehleUmgebung_nicht_program,
    if_pos rfl]
  exact environmentBefehlProofs

end Gabbro.Core.Ast.Semantik

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Waechter Gabbro.Core.Ast.Semantik

/-- Turn a bundled form promise into the typed registry entry for that form. -/
def aussageEntry (c : Lean.Name) (form : Form)
    (h : obligations form ∧ MeaningAussage form) :
    RegistryEntry c ⟨.surface, statements c form⟩ := by
  rcases h.1 with ⟨hp, hi, he, hd, hel, hr, ha, hid, hiu, him, hfo, her, hs, har, hau, hk, hsa⟩
  refine ⟨?_, ⟨ha, hau, h.2⟩, hid, hiu, him, ⟨her, hfo, hs, har, hk⟩, hsa⟩
  exact OriginProofs.surface ⟨hp, hi, he, hd⟩ hel hr

def addressTypeTreeEntry : RegistryEntry ``Gabbro.Core.Ast.LowLevel.Tree.addressType
    (schema ``Gabbro.Core.Ast.LowLevel.Tree.addressType) := by
  rw [schema, if_pos (by rw [beq_iff_eq])]
  exact aussageEntry ``Gabbro.Core.Ast.LowLevel.Tree.addressType .addressType
    addressType_aussage

def regionAddressTreeEntry : RegistryEntry ``Gabbro.Core.Ast.LowLevel.Tree.regionAddress
    (schema ``Gabbro.Core.Ast.LowLevel.Tree.regionAddress) := by
  rw [schema,
    if_neg (by
      rw [beq_iff_eq]
      exact differentLabels (a := "regionAddress") (b := "addressType")
        (by intro same; simp only [String.reduceEq] at same)),
    if_pos (by rw [beq_iff_eq])]
  exact aussageEntry ``Gabbro.Core.Ast.LowLevel.Tree.regionAddress .regionAddress
    regionAddress_aussage

def environmentTreeEntry : RegistryEntry ``Gabbro.Core.Ast.LowLevel.Tree.environment
    (schema ``Gabbro.Core.Ast.LowLevel.Tree.environment) := by
  rw [schema,
    if_neg (by
      rw [beq_iff_eq]
      exact differentLabels (a := "environment") (b := "addressType")
        (by intro same; simp only [String.reduceEq] at same)),
    if_neg (by
      rw [beq_iff_eq]
      exact differentLabels (a := "environment") (b := "regionAddress")
        (by intro same; simp only [String.reduceEq] at same)),
    if_neg (by
      rw [beq_iff_eq]
      exact differentLabels (a := "environment") (b := "view")
        (by intro same; simp only [String.reduceEq] at same))]
  exact aussageEntry ``Gabbro.Core.Ast.LowLevel.Tree.environment .environment
    environment_aussage

end Gabbro.Core.Ast.LowLevel
