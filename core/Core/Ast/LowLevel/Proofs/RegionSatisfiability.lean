module

public import Core.Ast.LowLevel.Proofs.RegionUnit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text Katalog Maschine

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

private theorem regionUnit_joint (init : RegionInitializer) (value : Wert init.type)
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
  let definition := Befehl.definiere mainName [.ownedRegion] none 0 4 false []
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

theorem regionAddressUnit_erfuellbar : RegionUnitErfuellbarAussage .address := by
  let value : AddressValue := ⟨Plattform.x86_64.ziel.physicalBits, 0, by change 0 < 2 ^ (52 : Nat); omega⟩
  exact regionUnit_joint .address value rfl rfl

theorem viewUnit_erfuellbar : ∃ written valid, RegionUnitErfuellbarAussage (.view written valid) := by
  let written := WrittenType.integer false 8 none
  have valid : written.valid := by
    change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
    omega
  exact ⟨written, valid, regionUnit_joint (.view written valid) ⟨0, 0, 1, false⟩ rfl rfl⟩

theorem regionBindUnit : RegionBindUnitAussage :=
  ⟨⟨regionUnit_realized, regionUnit_transfer _, regionAddressUnit_erfuellbar⟩,
    regionUnit_realized, fun _ _ => regionUnit_transfer _, viewUnit_erfuellbar⟩

end Gabbro.Core.Ast.Semantik
