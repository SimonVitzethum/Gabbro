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

private theorem unitImage : bild.gueltig Plattform.x86_64.ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a v h
    change (if a = 0 then some 0 else none) = some v at h
    split at h
    · rename_i atZero
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases h
  · intro a mem
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨0, rfl⟩

private def entryExtent : Strecke := ⟨0, 4096⟩

private theorem entryExtent_valid :
    ∀ r ∈ [entryExtent], r.von < r.bis ∧ r.bis ≤ 2 ^ Plattform.x86_64.ziel.physicalBits ∧
      ∀ e d, Plattform.x86_64.geraet e = some d → d.bus = .mmio → r.getrennt d.window := by
  intro extent member
  obtain rfl := List.mem_singleton.mp member
  refine ⟨by change 0 < 4096; omega, by change 4096 ≤ 2 ^ (52 : Nat); omega, ?_⟩
  intro endpoint device selected mmio
  cases endpoint <;> cases selected
  · cases mmio
  · exact Or.inl (by change 4096 ≤ 0x10000000; omega)

private def entryArgs : RegionEntryArgs := by
  let region := keywordName 'r' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)
  let binder := keywordName 'v' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)
  refine ⟨region, ?_, binder, ?_, ?_⟩
  · change ['r'] ≠ ['t', 'r', 'u', 'e'] ∧ ['r'] ≠ ['f', 'a', 'l', 's', 'e']
    constructor <;> intro equality <;> cases equality
  · intro equality
    exact nomatch (List.cons.inj equality).1
  · simp only [directName, ordinaryLocal, mainName, keywordName, String.reduceToList,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, List.cons.injEq,
      Char.reduceEq, false_and, and_false, false_or, or_false, not_false_eq_true, and_true]
    constructor <;> intro same
    all_goals
      have equal := (List.cons.inj same).1
      simp only [Char.reduceEq] at equal

private theorem regionUnitErfuellbar_joint (init : RegionInitializer) (value : Wert init.type)
    (allowed : Befehl.platformAllowed .x86_64 (.bindeRegion 0 init) = true)
    (yields : LowLevel.RegionInitializer.value Plattform.x86_64.ziel 0 entryExtent init =
      some ⟨init.type, value⟩) : RegionUnitErfuellbarAussage init := by
  let a := (entryArgs, init)
  let p := regionUnitForm.fragment a
  let E := regionUnitForm.einheit .x86_64 a
  obtain ⟨env, _, hardware, _⟩ := katalog_nichtLeer E.katalog Plattform.x86_64.katalog_wohlgeformt
  obtain ⟨empty, boot⟩ := zulStart_erfuellbar hardware unitImage
  let start := { empty with regions := [entryExtent], inputBytes := fun _ => none }
  obtain ⟨image, core, assigned, fits, _, _, _, outside⟩ := boot
  have admitted : E.ZulStart env start :=
    ⟨image, core, assigned, fits, List.pairwise_singleton _ _,
      entryExtent_valid, (fun _ _ impossible => nomatch impossible), outside⟩
  let definition := Befehl.definiere mainName [.ownedRegion] none 0 4 false [] none
  have instructions :
      p.code = [definition, .bindeRegion 0 init, .blockEnde 1, .rueckVoid, .starte mainName, .ende] := rfl
  have sourceAllowed : zugelassen .x86_64 .unit (entryArgs.unit init) := by
    change p.environmentAllowed _ ∧ p.code.all (Befehl.platformAllowed .x86_64) = true
    rw [instructions]
    refine ⟨⟨List.nodup_nil, fun _ mem => (List.not_mem_nil mem).elim⟩, ?_⟩
    simp only [Befehl.platformAllowed] at allowed
    simp only [List.all_cons, List.all_nil, definition, Befehl.platformAllowed,
      Option.toList, List.append_nil, platformType, Bool.true_and, Bool.and_true]
    exact allowed
  have accepted : Annahme.Akzeptiert E := by
    refine Fragment.akzeptiert_ohne_bedarf p .x86_64 rfl ?_
    intro b occurs frame
    rw [instructions] at occurs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at occurs
    rcases occurs with same | same | same | same | same | same <;> cases same <;> rfl
  let initial := (I.start E start).2
  let defined := definition.nach eintritt initial
  let s := (Befehl.starte mainName).nach eintritt defined
  have state : E.system.IErreichbar initial s := by
    apply System.IErreichbar.schritt eintritt () [plan]
    · exact .schritt eintritt () [plan] .start ⟨definition, rfl, rfl, rfl⟩
    · exact ⟨.starte mainName, rfl, rfl, rfl⟩
  have executed := regionUnit_realized.2.2.2 .x86_64 a s rfl rfl rfl rfl
  let next := (regionUnitForm.befehl a).nach eintritt s
  have transfer := regionUnit_transfer init (s.lokal eintritt) 0
    (fun slot => eintritt == Kontext.faden 0 && s.rechte.lebt slot && s.rechte.gen slot == 0 &&
      (match s.leihen slot with | .eigen => true | .verliehen _ => false))
    0 entryExtent ⟨init.type, value⟩ rfl rfl rfl rfl yields
  have frame : next.lokal eintritt =
      { s.lokal eintritt with
        pc := (s.lokal eintritt).pc + 1
        lokale := some ⟨init.type, value⟩ :: (s.lokal eintritt).lokale } := by
    change Function.update s.lokal eintritt _ eintritt = _
    rw [Function.update_self]
    exact transfer
  let text := Ast.print (category := .unit) (entryArgs.unit init)
  have reads : Ast.Parse (category := .unit) text (entryArgs.unit init) := Ast.parse_print _
  exact ⟨.x86_64, entryArgs, start, env, text, s, next, reads,
    ⟨entryArgs.unit init, reads, ⟨rfl, sourceAllowed⟩⟩, accepted, hardware, admitted, state, executed,
    rfl, congrArg Rahmen.pc frame, value, congrArg (fun out => out.lokale.head?) frame⟩

private theorem regionAddressUnitErfuellbar_local : RegionUnitErfuellbarAussage .address := by
  let value : AddressValue := ⟨Plattform.x86_64.ziel.physicalBits, 0, by change 0 < 2 ^ (52 : Nat); omega⟩
  exact regionUnitErfuellbar_joint .address value rfl rfl

private theorem viewUnitErfuellbar_local : ∃ written valid, RegionUnitErfuellbarAussage (.view written valid) := by
  let written := WrittenType.integer false 8 none
  have valid : written.valid [] := by
    change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  exact ⟨written, valid, regionUnitErfuellbar_joint (.view written valid) ⟨0, 0, 1, false⟩ rfl rfl⟩

theorem regionAddressUnit : RegionAddressUnitAussage :=
  ⟨regionUnit_realized, regionUnit_transfer _, regionAddressUnitErfuellbar_local⟩

theorem viewUnit : ViewUnitAussage :=
  ⟨regionUnit_realized, fun _ _ => regionUnit_transfer _, viewUnitErfuellbar_local⟩

end Gabbro.Core.Ast.Semantik
