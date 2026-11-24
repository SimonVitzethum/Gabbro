module

public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text Katalog Maschine

/-- Every ordinary occurrence of a signature admits the address space it names.
    The type production and printer agree on the same space discriminator. -/
def AddressTypeUnitAussage : Prop :=
  (∀ space suffix, TypeReads []
    ((WrittenType.address space).printPieces.map PrintedToken.value ++ suffix) (.address space) suffix) ∧
  ∀ platform (unit : Ast.Unit) E name parameters result globals skip measure calls effects space,
    ZugelassenElaboriert (category := .unit) platform unit E →
    Befehl.definiere name parameters result globals skip measure calls effects ∈ (programm unit).code →
    Ty.address space ∈ parameters ++ result.toList → (space.width platform).isSome = true

theorem addressTypeUnit : AddressTypeUnitAussage := by
  refine ⟨?_, ?_⟩
  · intro space suffix
    change TypeReads [] (space.printPieces.map PrintedToken.value ++ suffix) (.address space) suffix
    rw [space.printTokens]
    exact .address space
  · intro platform _ _ _ _ _ _ _ _ _ _ space meaning occurs present
    have admitted := (List.all_eq_true.mp meaning.2.2) _ occurs
    simpa only [platformType] using (List.all_eq_true.mp admitted) (.address space) present

/-- One ordinary binding at the beginning of the entry body. The region slot is
    supplied by the checked platform arrival and visible as the sole parameter. -/
structure RegionEntryArgs where
  region : Identifier
  ordinaryRegion : ordinaryLocal region
  binder : Identifier
  ordinary : binder.val ≠ "mut".toList
  entryName : directName mainName

def RegionEntryArgs.unit (args : RegionEntryArgs) (init : RegionInitializer) : Ast.Unit :=
  let parameter : Parameter [] := ⟨args.region, .ownedRegion, True.intro, args.ordinaryRegion⟩
  let receiver : Local [parameter.binding] .ownedRegion := Local.here
  let body : BracedBlock none [parameter.binding] :=
    .braces (.step (.letRegion args.binder args.ordinary receiver (by exact True.intro) args.ordinaryRegion init) .done)
  ⟨[], .step (.function mainName args.entryName [parameter] none
    (fun _ absent => (List.not_mem_nil absent).elim) none body
    (List.nodup_singleton _) (fun impossible => nomatch impossible) none) .done⟩

def regionEntryInUnit : Surface.Rule .unit (RegionEntryArgs × RegionInitializer) where
  tree := fun (args, init) => args.unit init
  production := fun (args, init) tokens =>
    UnitReads [] tokens (args.unit init)

def regionUnitForm : Quellform .unit (RegionEntryArgs × RegionInitializer) where
  produktion := regionEntryInUnit
  befehl := fun (_, init) => .bindeRegion 0 init
  position := fun _ => 1

def RegionUnitRealizedAussage : Prop :=
  regionUnitForm.RegelAmOrt ∧ regionUnitForm.ParseAussage ∧
    regionUnitForm.ElaboriertAussage ∧ regionUnitForm.RealisiertAussage

theorem regionUnit_realized : RegionUnitRealizedAussage := by
  have position : regionUnitForm.RegelAmOrt := by
    rintro ⟨args, init⟩
    rfl
  exact ⟨position, fun _ _ pieces lexed read =>
    (Category.unit.syntax.parse_iff).mpr ⟨pieces, lexed, read⟩,
    fun _ _ => rfl, regionUnitForm.realisiert position⟩

/-- A successful bind uses the live slot named by the receiver, and returns
    exactly the target-indexed value determined by that checked extent. -/
def RegionUnitTransferAussage (init : RegionInitializer) : Prop :=
  ∀ (frame : Rahmen) (receiver : Nat) (live : Nat → Bool) (slot : Nat) (extent : Strecke) (value : Dynamisch),
    frame.lokale[receiver]?.join.bind (wertAls .ownedRegion) = some slot →
    frame.arrivalRegions[slot]? = some extent →
    live slot = true → frame.borrowsRegion slot = false →
    LowLevel.RegionInitializer.value frame.platform.ziel slot extent init = some value →
    frame.bindeRegion receiver init live =
      { frame with pc := frame.pc + 1, lokale := some value :: frame.lokale }

theorem regionUnit_transfer (init : RegionInitializer) : RegionUnitTransferAussage init := by
  intro frame receiver live slot extent value resolved granted owns unborrowed result
  simp only [Rahmen.bindeRegion, Id.run, resolved, granted, owns, unborrowed, result,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
  rfl

def RegionUnitErfuellbarAussage (init : RegionInitializer) : Prop :=
  ∃ platform args start env text s after,
    let a := (args, init)
    let E := regionUnitForm.einheit platform a
    Ast.Parse (category := .unit) text (args.unit init) ∧ Bezeichnet platform .unit text E ∧
    Annahme.Akzeptiert E ∧ Hardware E.katalog env ∧ E.ZulStart env start ∧
    E.system.IErreichbar (I.start E start).2 s ∧ Realisiert regionUnitForm platform a s ∧
    after = (regionUnitForm.befehl a).nach eintritt s ∧
    (after.lokal eintritt).pc = (s.lokal eintritt).pc + 1 ∧
    ∃ value, (after.lokal eintritt).lokale.head? = some (some ⟨init.type, value⟩)

def RegionAddressUnitAussage : Prop :=
  RegionUnitRealizedAussage ∧ RegionUnitTransferAussage .address ∧
    RegionUnitErfuellbarAussage .address

def ViewUnitAussage : Prop :=
  RegionUnitRealizedAussage ∧ (∀ written valid, RegionUnitTransferAussage (.view written valid)) ∧
    ∃ written valid, RegionUnitErfuellbarAussage (.view written valid)

def RegionBindUnitAussage : Prop := RegionAddressUnitAussage ∧ ViewUnitAussage

end Gabbro.Core.Ast.Semantik
