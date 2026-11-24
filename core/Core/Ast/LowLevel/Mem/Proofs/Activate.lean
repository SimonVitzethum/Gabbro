module

public import Core.Ast.LowLevel.Mem.Proofs.ActivatePreservation

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter Aussen Annahme

private def lowName : Identifier :=
  ⟨['r'], ⟨'r', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private theorem lowName_slot : RegionScope.slot [lowName] lowName = some 0 := by
  change [lowName.val].idxOf? lowName.val = some 0
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]

private def spaceName : Identifier :=
  ⟨['s'], ⟨'s', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private theorem spaceName_slot : [spaceName.val].idxOf? spaceName.val = some 0 := by
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]

private def lowStart (h : Katalog.Umgebung) (regions : List Strecke) : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none), regions, (fun _ => none), h.politik.sicht 0 []⟩

private theorem imageGueltigX86 : image.gueltig (Plattform.x86_64).ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · rename_i atZero
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro a mem
    have h : a = 0 := List.mem_singleton.mp mem
    subst a
    exact ⟨0, rfl⟩

private theorem lowZulStart {k : Katalog} {h : Katalog.Umgebung} {regions : List Strecke}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel)
    (pairwise : regions.Pairwise Strecke.getrennt)
    (ok : ∀ r ∈ regions, r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window) :
    Katalog.ZulStart k h image (lowStart h regions) := by
  refine ⟨img, hw.kerne, ?_, ?_, pairwise, ok, ?_, rfl⟩
  · intro i hi
    refine ⟨0, ?_⟩
    change (if i = 0 then some 0 else none) = some 0
    change i < 1 at hi
    have : i = 0 := by omega
    subst i
    rfl
  · intro i c hc
    change (if i = 0 then some 0 else none) = some c at hc
    split at hc
    · rename_i hi
      subst i
      cases hc
      constructor
      · change 0 < 1
        omega
      · simpa using hw.kerne
    · cases hc
  · intro a byte hb
    change (none : Option UInt8) = some byte at hb
    cases hb

private theorem x86RegionsOk (extent : Strecke)
    (hbounds : extent.von < extent.bis ∧ extent.bis ≤ 2 ^ (Plattform.x86_64).ziel.physicalBits)
    (hsep : extent.getrennt (Plattform.x86_64.virtio.window)) :
    ∀ r ∈ [extent], r.von < r.bis ∧ r.bis ≤ 2 ^ (Plattform.x86_64).ziel.physicalBits ∧
      ∀ e d, Plattform.x86_64.geraet e = some d → d.bus = .mmio → r.getrennt d.window := by
  intro r hr
  have : r = extent := List.mem_singleton.mp hr
  subst r
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  intro e d hdev hmmio
  cases e with
  | uart =>
      change some Plattform.x86_64.uart = some d at hdev
      cases hdev
      change GeratBus.ioPorts = GeratBus.mmio at hmmio
      cases hmmio
  | virtio =>
      change some Plattform.x86_64.virtio = some d at hdev
      cases hdev
      exact hsep
  | bios | uefi | psci | sbi | hosted | cProcess =>
      change none = some d at hdev
      cases hdev

private theorem memKlauselnWahr (k : Katalog) (code : List MemInstruction) :
    KlauselnWahr (memProgram k code) := by
  intro ρ lauf
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    cases hp
  · intro t p hp
    cases hp
  · intro t done p hp
    cases hp

private theorem memWaechterHalten (k : Katalog) (code : List MemInstruction) :
    WaechterHalten (memProgram k code) := by
  constructor
  · intro ρ lauf t op args bedarf
    change False at bedarf
    exact False.elim bedarf
  · intro ρ lauf t h
    rcases h with ⟨C, nonempty, blocked⟩
    obtain ⟨c, hc⟩ := nonempty
    obtain ⟨b, hb, _, _⟩ := blocked c hc
    exact hb

private theorem memAkzeptiertX86 (code : List MemInstruction) :
    Akzeptiert (memProgram Plattform.x86_64.katalog code) := by
  refine ⟨?_, memKlauselnWahr _ code, memWaechterHalten _ code⟩
  refine ⟨by simpa [memProgram, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64, ?_, ?_⟩
  · intro i
    -- every instruction has an empty footprint at its ideal step
    intro c s u w p hideal
    rcases hideal with ⟨frame, heval, hp, hu⟩
    have hp' : p = plan := by simpa using hp
    subst p
    unfold Annahme.Befugt
    constructor
    · intro x hx
      cases hx
    · intro l hl
      cases hl
  · exact ⟨zulassung_m2 _, by
      apply aussen_gueltig_aus_kontext
      intro run t s c w spur s' step
      cases step with
      | kontext _ _ regel execute =>
          obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
          cases (List.cons.inj planEq).1
          obtain ⟨rfl, rfl⟩ := MemInstruction.genauInternal execute
          exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
            (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩⟩

theorem activateJoint : ActivateJointAussage := by
  let k : Katalog := Plattform.x86_64.katalog
  let target := k.plattform.ziel
  let extent : Strecke := ⟨0x1000, 0x2000⟩
  let tablesName : Identifier := lowName
  let space : Identifier := spaceName
  let scope : MemScope := ⟨[tablesName], [space], []⟩
  let op : MemInstruction := .activateSpace 0
  let pre : List MemInstruction := [.newSpace 0]
  let tree : MemTree .activateSpace := .activateSpace space
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start := lowStart env [extent]
  let text : RawText := tree.print
  let E := memProgram k (pre ++ [op])
  let s0 := (I.start E start).2
  have hw : Hardware k env := Katalog.Umgebung.referenz_hardware k 1 sicht
    (by simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
  have hbounds : extent.von < extent.bis ∧ extent.bis ≤ 2 ^ (Plattform.x86_64).ziel.physicalBits := by
    constructor
    · change 0x1000 < 0x2000
      omega
    · change 0x2000 ≤ 2 ^ (52 : Nat)
      omega
  have hsep : extent.getrennt (Plattform.x86_64.virtio.window) := by
    unfold Strecke.getrennt
    change 0x2000 ≤ 0x10000000 ∨ 0x10000200 ≤ 0x1000
    exact Or.inl (by omega)
  have hzul : E.ZulStart env start := by
    change Katalog.ZulStart k env image (lowStart env [extent])
    apply lowZulStart (k := k) (h := env) (regions := [extent])
    · exact hw
    · simpa [k, Plattform.katalog] using imageGueltigX86
    · exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
    · simpa [k, Plattform.katalog] using x86RegionsOk extent hbounds hsep
  have hparse : MemParse text tree := (memDruck .activateSpace tree).2
  have hopElab : elaborateMem scope tree = some op := by
    change Option.map MemInstruction.activateSpace ([spaceName.val].idxOf? spaceName.val) =
      some (MemInstruction.activateSpace 0)
    rw [spaceName_slot]
    rfl
  have hbezeichnet : BezeichnetMem k scope text (memUnit k op) .activateSpace := by
    refine ⟨tree, hparse, ?_⟩
    exact ⟨op, hopElab, rfl⟩
  have hnodupR : (scope.regionen.map Subtype.val).Nodup := by
    change [tablesName.val].Nodup
    exact List.nodup_singleton _
  have hnodupS : (scope.raeume.map Subtype.val).Nodup := by
    change [space.val].Nodup
    exact List.nodup_singleton _
  have hnodupM : (scope.marken.map Subtype.val).Nodup := by
    change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  have hs0status : s0.status entryContext = .laeuft := by
    simp only [s0, I.start, E, memProgram, lowStart, memBoot, Zustand.start, entryContext,
      ↓reduceIte]
  have hs0pc : (s0.lokal entryContext).pc = 0 := by
    rfl
  have hseiten : extent.seiten target := by
    unfold Strecke.seiten
    constructor
    · change 0x1000 < 0x2000
      omega
    constructor
    · change 0x2000 ≤ 2 ^ (52 : Nat)
      omega
    constructor
    · change 0x1000 % 4096 = 0
      rfl
    · change 0x2000 % 4096 = 0
      rfl
  have liveTable : (⟨extent, [⟨0, 0⟩]⟩ : MemRegion).live s0 = true := by
    simp only [MemRegion.live, s0, I.start, E, memProgram, lowStart, memBoot, Zustand.start,
      entryContext, ↓reduceIte, start, List.length_cons, List.length_nil, Nat.reduceLT,
      decide_true, List.isEmpty_cons, Bool.not_true, Bool.false_and,
      List.all_cons, List.all_nil, Bool.true_and, and_true]
  have heldTable : heldMemRegion target s0 entryContext 0 = some ⟨extent, [⟨0, 0⟩]⟩ := by
    unfold heldMemRegion
    change (if (⟨extent, [⟨0, 0⟩]⟩ : MemRegion).live s0 &&
        (s0.lokal entryContext).unreserved target.seitengranule extent then
      some (⟨extent, [⟨0, 0⟩]⟩ : MemRegion) else none) = some ⟨extent, [⟨0, 0⟩]⟩
    rw [if_pos]
    constructor
    · exact liveTable
    · unfold MemFrame.unreserved
      change ([] : List Adressraum).all (fun _ => true) = true
      rfl
  let frame0 : MemFrame :=
    { (s0.lokal entryContext) with
      result := some (.space (s0.lokal entryContext).spaces.length),
      spaces := (s0.lokal entryContext).spaces ++ [⟨extent, [], 0, []⟩] }
  have hframe0 : (MemInstruction.newSpace 0).evaluate target s0 entryContext = some frame0 := by
    change (do let region ← heldMemRegion target s0 entryContext 0
               if region.extent.seiten target then
                 (let space : Adressraum := ⟨region.extent, [], 0, []⟩
                  some { (s0.lokal entryContext) with
                    result := some (.space (s0.lokal entryContext).spaces.length),
                    spaces := (s0.lokal entryContext).spaces ++ [space] })
               else none) = some frame0
    rw [heldTable]
    dsimp
    rw [if_pos hseiten]
  have heval0 : ((MemInstruction.newSpace 0).evaluate target s0 entryContext).isSome := by
    rw [Option.isSome_iff_exists]
    exact ⟨frame0, hframe0⟩
  let s := frame0.advance entryContext s0
  have hhead0 : E.system.kopf s0 entryContext = some (.newSpace 0) := by
    change memHead target (pre ++ [op]) s0 entryContext = some (.newSpace 0)
    unfold memHead
    simp only [entryContext, ↓reduceIte, hs0status, hs0pc, List.getElem?_cons_zero]
    exact if_pos heval0
  have hstep0 : ((MemInstruction.rule target (.newSpace 0)).ideal entryContext s0 ()
      [plan] s) := by
    change ∃ frame, (MemInstruction.newSpace 0).evaluate target s0 entryContext = some frame ∧
      [plan] = [plan] ∧ s = frame.advance entryContext s0
    exact ⟨frame0, hframe0, rfl, rfl⟩
  have hreach : E.system.IErreichbar s0 s := by
    exact System.IErreichbar.schritt entryContext () [plan] System.IErreichbar.start
      ⟨.newSpace 0, hhead0, hstep0⟩
  have hsstatus : s.status entryContext = .laeuft := by
    simpa [s, MemFrame.advance] using hs0status
  have hspc : (s.lokal entryContext).pc = 1 := by
    simp only [s, MemFrame.advance, Function.update_self, hs0pc]
  have hsregions : (s.lokal entryContext).regions = [some ⟨extent, [⟨0, 0⟩]⟩] := by
    rfl
  have hsspaces : (s.lokal entryContext).spaces =
      [⟨extent, [], 0, []⟩] := by
    rfl
  have hAktiv : (⟨extent, [], 0, []⟩ : Adressraum).Aktivierbar target s entryContext := by
    unfold Adressraum.Aktivierbar Adressraum.Wohlgeformt
    refine ⟨⟨hseiten, List.nodup_nil, ?_⟩, ?_, ?_⟩
    · intro entry hmem
      cases hmem
    · simp only [MemFrame.covered, hsregions, List.any_cons, List.any_nil, Bool.or_false,
        Option.any_some]
      have hl : (⟨extent, [⟨0, 0⟩]⟩ : MemRegion).live s = true := by
        change (⟨extent, [⟨0, 0⟩]⟩ : MemRegion).live s0 = true
        exact liveTable
      rw [hl]
      change decide (extent.von ≤ extent.von ∧ extent.von < extent.bis ∧ extent.bis ≤ extent.bis) = true
      rfl
    · rfl
  have heval : (op.evaluate target s entryContext).isSome := by
    change ((MemInstruction.activateSpace 0).evaluate target s entryContext).isSome
    rw [Option.isSome_iff_exists]
    refine ⟨{ (s.lokal entryContext) with result := some .activated, active := some 0 }, ?_⟩
    change (do let space ← (s.lokal entryContext).spaces[0]?
               if space.Aktivierbar target s entryContext then
                 some { (s.lokal entryContext) with result := some .activated, active := some 0 }
               else none) =
      some { (s.lokal entryContext) with result := some .activated, active := some 0 }
    rw [hsspaces]
    change (if (⟨extent, [], 0, []⟩ : Adressraum).Aktivierbar target s entryContext then
      some { (s.lokal entryContext) with result := some .activated, active := some 0 }
      else none) =
      some { (s.lokal entryContext) with result := some .activated, active := some 0 }
    rw [if_pos hAktiv]
  obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp heval
  refine ⟨k, scope, tree, op, env, start, text, pre, s, next, ?_, hw, hzul, ?_,
    hnodupR, hnodupS, hnodupM, hbezeichnet, hparse, hopElab, hreach, ?_, hnext, ?_, ?_⟩
  · exact ⟨0, rfl, rfl⟩
  · exact memAkzeptiertX86 (pre ++ [op])
  · change memHead target (pre ++ [op]) s entryContext = some op
    unfold memHead
    simp only [entryContext, ↓reduceIte, hsstatus, hspc, List.getElem?_cons_succ,
      List.getElem?_cons_zero]
    exact if_pos heval
  · change ∃ i, memHead target (pre ++ [op]) s entryContext = some i ∧
      (MemInstruction.rule target i).ideal entryContext s () [plan] (next.advance entryContext s)
    refine ⟨op, ?_, ?_⟩
    · change memHead target (pre ++ [op]) s entryContext = some op
      unfold memHead
      simp only [entryContext, ↓reduceIte, hsstatus, hspc, List.getElem?_cons_succ,
        List.getElem?_cons_zero]
      exact if_pos heval
    · change ∃ frame, op.evaluate target s entryContext = some frame ∧
        [plan] = [plan] ∧ next.advance entryContext s = frame.advance entryContext s
      exact ⟨next, hnext, rfl, rfl⟩
  · change ∃ i, memHead target (pre ++ [op]) s entryContext = some i ∧
      (MemInstruction.rule target i).impl entryContext s () [plan] (next.advance entryContext s)
    refine ⟨op, ?_, ?_⟩
    · change memHead target (pre ++ [op]) s entryContext = some op
      unfold memHead
      simp only [entryContext, ↓reduceIte, hsstatus, hspc, List.getElem?_cons_succ,
        List.getElem?_cons_zero]
      exact if_pos heval
    · change ∃ frame, op.evaluate target s entryContext = some frame ∧
        [plan] = [plan] ∧ next.advance entryContext s = frame.advance entryContext s
      exact ⟨next, hnext, rfl, rfl⟩

theorem activate_aussage : ActivateAussage := by
  exact ⟨activateObligations, activate_meaning, activateJoint⟩

end Gabbro.Core.Ast.LowLevel
