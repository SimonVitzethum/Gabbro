module

public import Core.Ast.LowLevel.Mem.Proofs.NewSpace
public import Core.Ast.LowLevel.Mem.Proofs.Unmap.Unmap

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Waechter Katalog Maschine Text
open Gabbro.Core.Annahme

/-! Joint satisfiability of `unmap`: a real program first creates a space from
an aligned table grant, maps one frame grant into it, and only then unmaps. The
prefix is executed explicitly so the `unmap` occurrence has a reachable state. -/

private def satName (c : Char) (h : 'a' ≤ c ∧ c ≤ 'z') : Identifier :=
  keywordName c [] h (fun _ mem => (List.not_mem_nil mem).elim)

private def nameRegion0 : Identifier := satName 'a' (by decide)
private def nameRegion1 : Identifier := satName 'b' (by decide)
private def nameSpace : Identifier := satName 's' (by decide)

private def satScope : MemScope := ⟨[nameRegion0, nameRegion1], [nameSpace], []⟩

private def satK : Katalog := Plattform.x86_64.katalog

private theorem satKwf : KatalogWohlgeformt satK := by
  simpa [satK, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64

private def satSicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer

private def satEnv : Katalog.Umgebung := Katalog.Umgebung.referenz satK 1 satSicht

private theorem satHardware : Hardware satK satEnv :=
  Katalog.Umgebung.referenz_hardware satK 1 satSicht satKwf (by omega)

private def tableExtent : Strecke := ⟨0, 4096⟩
private def frameExtent : Strecke := ⟨4096, 8192⟩

private theorem tableBounds :
    tableExtent.von < tableExtent.bis ∧ tableExtent.bis ≤ 2 ^ satK.plattform.ziel.physicalBits := by
  change 0 < 4096 ∧ 4096 ≤ 2 ^ (52 : Nat)
  constructor <;> omega

private theorem frameBounds :
    frameExtent.von < frameExtent.bis ∧ frameExtent.bis ≤ 2 ^ satK.plattform.ziel.physicalBits := by
  change 4096 < 8192 ∧ 8192 ≤ 2 ^ (52 : Nat)
  constructor <;> omega

private def satStart : AussenStart :=
  ⟨0, fun i => if i = 0 then some 0 else none, [tableExtent, frameExtent],
    fun _ => none, satEnv.politik.sicht 0 []⟩

private theorem satImage : image.gueltig satK.plattform.ziel := by
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

private theorem satRegionOk (extent : Strecke)
    (hbounds : extent.von < extent.bis ∧ extent.bis ≤ 2 ^ satK.plattform.ziel.physicalBits)
    (hsep : extent.getrennt satK.plattform.virtio.window) :
    ∀ r ∈ [extent], r.von < r.bis ∧ r.bis ≤ 2 ^ satK.plattform.ziel.physicalBits ∧
      ∀ e d, satK.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window := by
  intro r hr
  have : r = extent := List.mem_singleton.mp hr
  subst r
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  intro e d hdev hmmio
  cases e with
  | uart =>
      change some satK.plattform.uart = some d at hdev
      cases hdev
      change GeratBus.ioPorts = GeratBus.mmio at hmmio
      cases hmmio
  | virtio =>
      change some satK.plattform.virtio = some d at hdev
      cases hdev
      exact hsep
  | bios | uefi | psci | sbi | hosted | cProcess =>
      change none = some d at hdev
      cases hdev

private theorem tableSep : tableExtent.getrennt satK.plattform.virtio.window := by
  unfold Strecke.getrennt
  change 4096 ≤ 0x10000000 ∨ 0x10000200 ≤ 0
  exact Or.inl (by omega)

private theorem frameSep : frameExtent.getrennt satK.plattform.virtio.window := by
  unfold Strecke.getrennt
  change 8192 ≤ 0x10000000 ∨ 0x10000200 ≤ 4096
  exact Or.inl (by omega)

private theorem satZul : Katalog.ZulStart satK satEnv image satStart := by
  refine ⟨satImage, satHardware.kerne, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro i hi
    refine ⟨0, ?_⟩
    change (if i = 0 then some 0 else none) = some 0
    have hi' : i < image.entries.length := hi
    have hi1 : i < 1 := by simpa [image] using hi'
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
      · simpa [image]
      · simpa using satHardware.kerne
    · cases hc
  · refine List.Pairwise.cons ?_ ?_
    · intro a ha
      obtain rfl := List.mem_singleton.mp ha
      unfold Strecke.getrennt
      change 4096 ≤ 4096 ∨ 8192 ≤ 0
      exact Or.inl (by omega)
    · exact List.Pairwise.cons (by
        intro a ha
        cases ha) List.Pairwise.nil
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact satRegionOk tableExtent tableBounds tableSep tableExtent (by
        simp only [List.mem_singleton, eq_self])
    · obtain rfl := List.mem_singleton.mp hr
      exact satRegionOk frameExtent frameBounds frameSep frameExtent (by
        simp only [List.mem_singleton, eq_self])
  · intro a byte hb
    cases hb

private def satRights : List Speicherdienst := [.read]

private def satCode : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 satRights, .unmapSpace 0 0 1]

private def satPrefix : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 satRights]

private def satOp : MemInstruction := .unmapSpace 0 0 1

private def satE : MemUnit := memProgram satK satCode

private def satS0 : MemState := (I.start satE satStart).2

private def tableRegion : MemRegion := ⟨tableExtent, [⟨0, 0⟩]⟩
private def frameRegion : MemRegion := ⟨frameExtent, [⟨1, 0⟩]⟩

private def space0 : Adressraum := ⟨tableExtent, [], 0, []⟩
private def space2 : Adressraum := ⟨tableExtent, [(0, ⟨1, satRights, 0⟩)], 0, []⟩

private theorem satHeld0 : heldMemRegion satK.plattform.ziel satS0 entryContext 0 = some tableRegion := by
  rfl

private theorem tableExtent_seiten : tableExtent.seiten satK.plattform.ziel := by
  change 0 < 4096 ∧ 4096 ≤ 2 ^ (52 : Nat) ∧ 0 % 4096 = 0 ∧ 4096 % 4096 = 0
  constructor
  · omega
  constructor
  · omega
  constructor <;> rfl

private theorem frameExtent_seiten : frameExtent.seiten satK.plattform.ziel := by
  change 4096 < 8192 ∧ 8192 ≤ 2 ^ (52 : Nat) ∧ 4096 % 4096 = 0 ∧ 8192 % 4096 = 0
  constructor
  · omega
  constructor
  · omega
  constructor <;> rfl

private theorem satValid : validVirtualRange satK.plattform.ziel 0 1 := by
  have hv : satK.plattform.ziel.virtuell 0 := by
    left
    change 0 < 2 ^ (48 - 1 : Nat)
    exact Nat.pow_pos (by omega)
  simp only [validVirtualRange, show satK.plattform.ziel.seitengranule = 4096 by rfl,
    Nat.zero_mod, Nat.zero_lt_one, true_and, decide_true, List.range_one, List.all_cons,
    List.all_nil, Bool.true_and, zero_add, zero_mul, decide_eq_true hv]

private def s1frame : MemFrame :=
  { (satS0.lokal entryContext) with result := some (.space 0), spaces := [space0] }

private def satS1 : MemState := s1frame.advance entryContext satS0

private theorem satEval1 :
    (MemInstruction.newSpace 0).evaluate satK.plattform.ziel satS0 entryContext = some s1frame := by
  simp only [MemInstruction.evaluate, satHeld0, tableExtent_seiten, Bind.bind, Option.bind,
    Option.bind_some, if_pos tableExtent_seiten, ↓reduceIte, List.nil_append]
  dsimp [s1frame, space0]
  rfl

private theorem satHeld1 : heldMemRegion satK.plattform.ziel satS1 entryContext 1 = some frameRegion := by
  rfl

private theorem satRights_ne : satRights ≠ [] := by
  intro h
  cases h

private theorem satEmpty0 :
    (List.range 1).all (fun i => (space0.abbildung (0 + i)).isNone) = true := by
  simp only [List.range_one, List.all_cons, List.all_nil, Bool.true_and, zero_add,
    space0, Adressraum.abbildung, List.find?_nil, Option.map_none, Option.isNone]

private theorem satPending0 :
    space0.ausstehend.all (fun token => (List.range 1).all (fun i => decide (¬ token.contains (0 + i)))) = true := by
  rfl

private def s2frame : MemFrame := { (satS1.lokal entryContext) with result := some .mapped, spaces := [space2], tlb := (satS1.lokal entryContext).tlb.invalidate 0 0 1 }

private def satS2 : MemState := s2frame.advance entryContext satS1

private theorem satEval2 :
    (MemInstruction.mapSpace 0 0 1 satRights).evaluate satK.plattform.ziel satS1 entryContext = some s2frame := by
  simp only [MemInstruction.evaluate, satHeld1, satRights_ne, frameExtent_seiten, satValid,
    satEmpty0, satPending0, Bind.bind, Option.bind, Option.bind_some, and_true,
    if_true, ↓reduceIte, List.range_one, List.map_cons, List.map_nil,
    List.nil_append, List.set_cons_zero]
  dsimp [s2frame, space2]
  rfl

private theorem satFirst : space2.abbildung 0 = some ⟨1, satRights, 0⟩ := by
  rfl

private theorem satFrames2 :
    (List.range 1).all (fun i => ((space2.abbildung (0 + i)).map Seiteneintrag.frame) ==
      some ((⟨1, satRights, 0⟩ : Seiteneintrag).frame + i)) = true := by
  simp only [List.range_one, List.all_cons, List.all_nil, Bool.true_and, zero_add,
    space2, Adressraum.abbildung, List.find?_cons, List.find?_nil, Option.map_none,
    beq_self_eq_true, if_true, Option.map_some]

private theorem satPage0 : pageRange 0 1 0 := ⟨by omega, by omega⟩

private def token2 : Zuruecknahme := ⟨0, 0, 1, 1, 1⟩
private def space3 : Adressraum := ⟨tableExtent, [], 1, [token2]⟩
private def s3frame : MemFrame :=
  { (satS2.lokal entryContext) with result := some (.pending token2), spaces := [space3] }

private theorem satEval3 :
    satOp.evaluate satK.plattform.ziel satS2 entryContext = some s3frame := by
  simp only [satOp, MemInstruction.evaluate, satFirst, satValid, satFrames2,
    Bind.bind, Option.bind, Option.bind_some, and_true, if_true, ↓reduceIte,
    List.range_one, List.filter_cons, satPage0, decide_true, Bool.not_true, if_false,
    List.filter_nil, List.set_cons_zero]
  dsimp [s3frame, space3, token2, satS2]
  rfl

theorem memProgramAkzeptiert (k : Katalog) (code : List MemInstruction)
    (hwf : KatalogWohlgeformt k) : Annahme.Akzeptiert (memProgram k code) := by
  let E := memProgram k code
  refine ⟨⟨hwf, ?_, ⟨⟨Aussen.zulassung_m2 k.plattform, ?_⟩, memProgramFlussLokal k code⟩⟩, ?_, ?_⟩
  · intro i c s u w P hideal
    simp only [E, memProgram, MemInstruction.rule, MemInstruction.step] at hideal
    have hP : P = plan := by
      rcases hideal with ⟨frame, _, hP, _⟩
      simpa using hP
    subst P
    rw [Annahme.Befugt]
    have hfuss : plan.fuss = [] := rfl
    have hlesen : plan.lesen = [] := rfl
    rw [hfuss, hlesen]
    constructor
    · intro x hx; cases hx
    · intro l hl; cases hl
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur s' step
    cases step with
    | kontext _ _ regel execute =>
        obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
        cases (List.cons.inj planEq).1
        obtain ⟨rfl, rfl⟩ := unmapMemGenauInternal execute
        exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
          (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · intro run conforms
    change (∀ pred ∈ (E.quelltabellen.klauseln).voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ (E.quelltabellen.klauseln).invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ (E.quelltabellen.klauseln).sicher, _
    simp only [E, memProgram]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro run conforms t o args need
      change E.quelltabellen.guard (run.zeit.zustand t.val) o args at need
      simp only [E, memProgram] at need
    · intro run conforms t waiting
      obtain ⟨C, ⟨c, hc⟩, blocked⟩ := waiting
      obtain ⟨b, hb, _, _, _⟩ := blocked c hc
      simp only [E, memProgram] at hb
    · intro run conforms t l h _ hne
      exact (hne rfl).elim

private theorem satScopeNodup :
    (satScope.regionen.map Subtype.val).Nodup ∧ (satScope.raeume.map Subtype.val).Nodup ∧
      (satScope.marken.map Subtype.val).Nodup := by
  change ([[ 'a' ], [ 'b' ]] : List (List Char)).Nodup ∧ [['s']].Nodup ∧
    ([] : List (List Char)).Nodup
  simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, and_true,
    List.nodup_nil, List.cons.injEq, Char.reduceEq, not_false_eq_true]

private theorem satElab : elaborateMem satScope (MemTree.unmapSpace nameSpace 0 1) = some satOp := by
  rfl

private theorem satS0status : satS0.status entryContext = .laeuft := by rfl
private theorem satS1status : satS1.status entryContext = .laeuft := by rfl
private theorem satS2status : satS2.status entryContext = .laeuft := by rfl
private theorem satS0pc : (satS0.lokal entryContext).pc = 0 := by rfl
private theorem satS1pc : (satS1.lokal entryContext).pc = 1 := by rfl
private theorem satS2pc : (satS2.lokal entryContext).pc = 2 := by rfl

private theorem satEval1Some : ((MemInstruction.newSpace 0).evaluate satK.plattform.ziel satS0 entryContext).isSome = true := by
  rw [satEval1]
  rfl

private theorem satHead1 : satE.system.kopf satS0 entryContext = some (.newSpace 0) := by
  change memHead satK.plattform.ziel satCode satS0 entryContext = some (.newSpace 0)
  simp only [memHead, satS0status, satS0pc, satCode, List.getElem?_cons_zero,
    Bind.bind, Option.bind, Option.bind_some, if_pos rfl, if_pos satEval1Some, ↓reduceIte]

private theorem satEval2Some :
    ((MemInstruction.mapSpace 0 0 1 satRights).evaluate satK.plattform.ziel satS1 entryContext).isSome = true := by
  rw [satEval2]
  rfl

private theorem satHead2 : satE.system.kopf satS1 entryContext = some (.mapSpace 0 0 1 satRights) := by
  change memHead satK.plattform.ziel satCode satS1 entryContext = some (.mapSpace 0 0 1 satRights)
  simp only [memHead, satS1status, satS1pc, satCode, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Bind.bind, Option.bind, Option.bind_some,
    if_pos rfl, if_pos satEval2Some, ↓reduceIte]

private theorem satEval3Some :
    ((MemInstruction.unmapSpace 0 0 1).evaluate satK.plattform.ziel satS2 entryContext).isSome = true := by
  change (satOp.evaluate satK.plattform.ziel satS2 entryContext).isSome = true
  rw [satEval3]
  rfl

private theorem satHead3 : satE.system.kopf satS2 entryContext = some satOp := by
  change memHead satK.plattform.ziel satCode satS2 entryContext = some satOp
  simp only [memHead, satS2status, satS2pc, satCode, List.getElem?_cons_succ,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Bind.bind, Option.bind,
    Option.bind_some, if_pos rfl, if_pos satEval3Some, ↓reduceIte]
  dsimp [satOp]

private theorem satReach1 : satE.system.IErreichbar satS0 satS1 := by
  apply System.IErreichbar.schritt entryContext () [plan]
  · exact .start
  · exact ⟨.newSpace 0, satHead1, ⟨s1frame, satEval1, rfl, rfl⟩⟩

private theorem satReach : satE.system.IErreichbar satS0 satS2 := by
  apply System.IErreichbar.schritt entryContext () [plan]
  · exact satReach1
  · exact ⟨.mapSpace 0 0 1 satRights, satHead2, ⟨s2frame, satEval2, rfl, rfl⟩⟩

theorem unmap_joint : UnmapJointAussage := by
  let tree : MemTree .unmapSpace := .unmapSpace nameSpace 0 1
  refine ⟨satK, satScope, tree, satOp, satEnv, satStart, tree.print, satPrefix, satS2, s3frame, ?_⟩
  refine ⟨?_, satHardware, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, satReach, ?_, satEval3, ?_, ?_⟩
  · exact ⟨0, 0, 1, satRights, 1, rfl, rfl⟩
  · change Katalog.ZulStart satK satEnv image satStart
    exact satZul
  · apply memProgramAkzeptiert
    exact satKwf
  · exact satScopeNodup.1
  · exact satScopeNodup.2.1
  · exact satScopeNodup.2.2
  · refine ⟨tree, unmapMemParseOfPrint tree (memUnmapPrints tree), ?_⟩
    exact ⟨satOp, satElab, rfl⟩
  · exact unmapMemParseOfPrint tree (memUnmapPrints tree)
  · exact satElab
  · exact satHead3
  · exact ⟨satOp, satHead3, ⟨s3frame, satEval3, rfl, rfl⟩⟩
  · exact ⟨satOp, satHead3, ⟨s3frame, satEval3, rfl, rfl⟩⟩

theorem unmapErhaltung : MemErhaltungAussage .unmapSpace := by
  intro k scope tree op _
  exact ⟨unmapMemAbgleich (k := k) op, unmapMemKomponierbar (k := k) op⟩

theorem unmapRegelSicher : MemRegelSicherAussage .unmapSpace := by
  intro k scope tree op _
  exact unmapMemRegelSicher (k := k) op

theorem unmapAussenLokal : MemAussenLokalAussage .unmapSpace := by
  intro k scope tree op _
  exact unmapMemAussenLokal (k := k) op

theorem unmapKosten : MemKostenAussage .unmapSpace := by
  intro k scope tree op _
  exact unmapMemKosten (k := k) op

theorem unmap_aussage : UnmapAussage := by
  refine ⟨?_, unmap_meaning, unmap_joint⟩
  exact ⟨unmapMemParse .unmapSpace, memInversionUnmap, memEindeutigUnmap, memDruckUnmap,
    memElaboriert .unmapSpace, unmapMemRealisiert .unmapSpace, unmapMemAnnahme .unmapSpace,
    unmapMemIdeal .unmapSpace, memEinheit .unmapSpace, memImpl .unmapSpace,
    unmapMemFortschritt .unmapSpace, unmapErhaltung, unmapRegelSicher,
    memRegelAntwortSicher .unmapSpace, unmapAussenLokal, unmapKosten,
    memSchranken, memEtiketten, memFluss⟩

end Gabbro.Core.Ast.LowLevel
