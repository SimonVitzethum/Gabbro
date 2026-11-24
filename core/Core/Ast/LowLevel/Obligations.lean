module

public import Core.Ast.LowLevel.Execution
public import Core.Verfeinerung.Maschine
public import Core.Waechter.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter

def ParseAussage (form : Form) : Prop :=
  ∀ (tree : Tree form) text pieces, Lexed text pieces → tree.production (canonicalTokens pieces) →
    Parse text tree

def InversionAussage (form : Form) : Prop :=
  ∀ (tree : Tree form) text, Parse text tree →
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)

def EindeutigAussage (form : Form) : Prop :=
  ∀ (a b : Tree form) text, Parse text a → Parse text b → a = b

def DruckAussage (form : Form) : Prop :=
  ∀ tree : Tree form, tree.production (tree.printPieces.map PrintedToken.value) ∧ Parse tree.print tree

def ElaboriertAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) E,
    Elaboriert k scope tree E ↔ ∃ op, elaborate k scope tree = some op ∧ E = unit op

/-- Neither a caller-supplied guard nor a synthetic machine step can make a
    missing region, layout check, or catalogue row denote an admitted occurrence. -/
def RealisiertAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op start,
    elaborate k scope tree = some op →
    (op.evaluate (I.start (unit op) start).2 entryContext).isSome →
    (unit op).system.kopf (I.start (unit op) start).2 entryContext = some op

def AnnahmeAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    Annahme.RegelLokal (unit op) op ∧
    ∀ s c w plans next, op.ideal c s w plans next → plans = [plan]

def IdealAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    Ideal.RegelBestimmt op.rule ∧
    ∀ c s w plans next, op.rule.ideal c s w plans next ↔
      ∃ transfer, op.evaluate s c = some transfer ∧ plans = [plan] ∧ next = transfer.apply c s

def EinheitAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    (unit op).stotterLaenge op = 0 ∧ (unit op).lokalerBezug = Eq ∧
    ∀ other, Kommutation (fun (_ _ : State k) => False) (fun _ _ => False) other

def ImplAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    ∀ c s w plans next, op.rule.impl c s w plans next ↔ op.rule.ideal c s w plans next

def FortschrittAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    Ideal.RegelFortschritt (unit op).system op

def ErhaltungAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    I.RegelAbgleich (unit op) op ∧ I.RegelKomponierbar (unit op).einrichtung (unit op).system op

def RegelSicherAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    Sicherheit.RegelSicher (safetyUnit op) op

/-- The local registration and region-metadata forms have no reply event and
    cannot consume an outstanding answer as a side effect. -/
def RegelAntwortSicherAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      (∀ ev : AntwortEreignis, Ereignis.antwort ev ∉ trace.aussen) ∧
      next.verbraucht = s.verbraucht

def AussenLokalAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    Annahme.AussenLokal (unit op)

/-- M9 can account for these occurrences as one model step, with no memory
    graph event, external event, or additional private step. -/
def KostenAussage (form : Form) : Prop :=
  ∀ k scope (tree : Tree form) op, elaborate k scope tree = some op →
    ∀ t c s w middle next p trace, op.impl c s w [p] middle →
      FuehrtSchrittAus (unit op).einrichtung t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (unit op).stotterLaenge op = 0

/-- Syntax, admission at the catalogue boundary, realization, and both transfer
    rules must hold jointly at the initial live occurrence. -/
def ErfuellbarAussage (form : Form) : Prop :=
  ∃ (k : Katalog) (scope : RegionScope) (tree : Tree form) (op : Instruction k)
    (env : Umgebung) (start : AussenStart) (text : RawText) (transfer : Transfer k),
    KatalogWohlgeformt k ∧ (scope.map Subtype.val).Nodup ∧ scope.length = start.regions.length ∧
    (unit op).ZulStart env start ∧ Parse text tree ∧ elaborate k scope tree = some op ∧
    Elaboriert k scope tree (unit op) ∧
    let s := (I.start (unit op) start).2
    (unit op).system.kopf s entryContext = some op ∧ op.evaluate s entryContext = some transfer ∧
    op.ideal entryContext s () [plan] (transfer.apply entryContext s) ∧
    op.impl entryContext s () [plan] (transfer.apply entryContext s)

def obligations (form : Form) : Prop :=
  ParseAussage form ∧ InversionAussage form ∧ EindeutigAussage form ∧ DruckAussage form ∧
  ElaboriertAussage form ∧ RealisiertAussage form ∧ AnnahmeAussage form ∧ IdealAussage form ∧
  EinheitAussage form ∧ ImplAussage form ∧ FortschrittAussage form ∧ ErhaltungAussage form ∧
  RegelSicherAussage form ∧ RegelAntwortSicherAussage form ∧ AussenLokalAussage form ∧
  KostenAussage form ∧ ErfuellbarAussage form

def AddressTypeMeaningAussage : Prop :=
  ∀ k scope space op, elaborate k scope (.addressType space) = some op →
    ∃ width h, op = .denoteAddress space width h

def RegionAddressMeaningAussage : Prop :=
  ∀ k scope region op s c transfer, elaborate k scope (.regionAddress region) = some op →
    op.evaluate s c = some transfer →
    ∃ slot handle extent address, scope.slot region = some slot ∧ heldRegion s c slot = some (handle, extent) ∧
      transfer.value = .address address ∧ address.number = extent.von ∧ transfer.loan = none

def ViewMeaningAussage : Prop :=
  ∀ k scope region type op s c transfer, elaborate k scope (.view region type) = some op →
    op.evaluate s c = some transfer →
    ∃ slot handle extent shape, scope.slot region = some slot ∧ heldRegion s c slot = some (handle, extent) ∧
      layout k.plattform.ziel type = some shape ∧ shape.endian = ByteOrder.ofTarget k.plattform.ziel ∧
      extent.von % shape.alignment = 0 ∧ extent.von + shape.bytes ≤ extent.bis ∧
      transfer.value = .view slot handle ⟨extent.von, extent.von + shape.bytes⟩ shape ∧
      transfer.loan = some handle ∧ heldRegion (transfer.apply c s) c slot = none

def EnvironmentMeaningAussage : Prop :=
  ∀ k scope name abi row, (∃ op, elaborate k scope (.environment name abi row) = some op) ↔
    k.enthaelt (.endpoint row.endpunkt) ∧ k.plattform.firmwareAbi row.endpunkt = some abi

def MeaningAussage : Form → Prop
  | .addressType => AddressTypeMeaningAussage
  | .regionAddress => RegionAddressMeaningAussage
  | .view => ViewMeaningAussage
  | .environment => EnvironmentMeaningAussage

def AddressTypeAussage : Prop := obligations .addressType ∧ MeaningAussage .addressType
def RegionAddressAussage : Prop := obligations .regionAddress ∧ MeaningAussage .regionAddress
def ViewAussage : Prop := obligations .view ∧ MeaningAussage .view
def EnvironmentAussage : Prop := obligations .environment ∧ MeaningAussage .environment

def statements (constructor : Lean.Name) (form : Form) : RegistryStatements constructor .surface where
  realization := .surface (ParseAussage form ∧ InversionAussage form ∧ EindeutigAussage form ∧ DruckAussage form)
    (ElaboriertAussage form) (RealisiertAussage form)
  acceptanceRule := AnnahmeAussage form ∧ AussenLokalAussage form ∧ MeaningAussage form
  idealRule := IdealAussage form
  unitsAndCommutation := EinheitAussage form
  implementationRule := ImplAussage form
  preservation := ErhaltungAussage form ∧ FortschrittAussage form ∧ RegelSicherAussage form ∧
    RegelAntwortSicherAussage form ∧ KostenAussage form
  jointlySatisfiable := ErfuellbarAussage form

def schema (constructor : Lean.Name) : RegistrySchema constructor :=
  let form := if constructor == ``Tree.addressType then Form.addressType
    else if constructor == ``Tree.regionAddress then .regionAddress
    else if constructor == ``Tree.view then .view
    else .environment
  ⟨.surface, statements constructor form⟩

end Gabbro.Core.Ast.LowLevel
