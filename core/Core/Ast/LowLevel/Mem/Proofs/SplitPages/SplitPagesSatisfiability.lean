module

public import Core.Ast.LowLevel.Mem.Proofs.SplitPages.SplitPages

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Annahme Waechter

private def spName : Identifier :=
  ⟨['r'], ⟨'r', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private theorem spNameSlot : (spName.val :: []).idxOf? spName.val = some 0 := by
  simp only [List.idxOf?_cons, beq_self_eq_true, if_true]

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

theorem splitPagesErfuellbar : MemErfuellbarAussage .splitPages := by
  let k : Katalog := Plattform.x86_64.katalog
  let target := k.plattform.ziel
  let granule := target.seitengranule
  let extent : Strecke := ⟨0x1000, 0x3000⟩
  let region : MemRegion := ⟨extent, [⟨0, 0⟩]⟩
  let name : Identifier := spName
  let scope : MemScope := ⟨[name], [], []⟩
  let pages := 1
  let tree : MemTree .splitPages := .splitPages name pages
  let op : MemInstruction := .splitPages 0 pages
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start : AussenStart :=
    ⟨0, (fun i => if i = 0 then some 0 else none), [extent], (fun _ => none), env.politik.sicht 0 []⟩
  let pre : List MemInstruction := []
  let E := memProgram k (pre ++ [op])
  let s : MemState := (I.start E start).2
  let cut := extent.von + pages * granule
  let next := (s.lokal entryContext).partition 0 region cut
  have hwf : KatalogWohlgeformt k := by
    dsimp [k]
    exact Plattform.katalog_wohlgeformt .x86_64
  have hardware : Hardware k env := by
    dsimp [env]
    exact Umgebung.referenz_hardware k 1 sicht hwf (by omega)
  have zulStart : E.ZulStart env start := by
    change Katalog.ZulStart k env image start
    refine ⟨by simpa only [k, Plattform.katalog] using imageGueltigX86, hardware.kerne, ?_, ?_, ?_, ?_, ?_, rfl⟩
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
        · simpa using hardware.kerne
      · cases hc
    · exact List.Pairwise.cons (by intro a ha; cases ha) List.Pairwise.nil
    · apply x86RegionsOk extent
      · constructor
        · dsimp [extent]; omega
        · dsimp [extent]
          change 0x3000 ≤ 2 ^ (52 : Nat)
          omega
      · unfold Strecke.getrennt
        change 0x3000 ≤ 0x10000000 ∨ 0x10000200 ≤ 0x1000
        exact Or.inl (by omega)
    · intro a byte hb
      change none = some byte at hb
      cases hb
  have hslot : scope.slotRegion name = some 0 := by
    change [spName.val].idxOf? spName.val = some 0
    exact spNameSlot
  have helab : elaborateMem scope tree = some op := by
    simp only [tree, op, elaborateMem, hslot, Option.map_some]
  have held : heldMemRegion target s entryContext 0 = some region := by
    dsimp [s, I.start, E, pre, memProgram, memBoot, Zustand.start, heldMemRegion,
      region, extent, target, k, start]
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, Option.join_some, Option.bind_some, MemRegion.live,
      MemFrame.unreserved, Bool.not_false, Bool.false_or, Bool.and_true, decide_true,
      List.all_nil, if_true]
    rfl
  have hEval : op.evaluate target s entryContext = some next := by
    simp only [op, MemInstruction.evaluate, held]
    change (if region.extent.von % granule = 0 ∧ 0 < pages ∧
        region.extent.von + pages * granule < region.extent.bis then
        some ((s.lokal entryContext).partition 0 region (region.extent.von + pages * granule)) else none) = some next
    have hcond : region.extent.von % granule = 0 ∧ 0 < pages ∧
        region.extent.von + pages * granule < region.extent.bis := by
      change 0x1000 % 4096 = 0 ∧ 0 < (1 : Nat) ∧ 0x1000 + 1 * 4096 < 0x3000
      constructor
      · rfl
      constructor <;> omega
    rw [if_pos hcond]
  refine ⟨k, scope, tree, op, env, start, tree.print, pre, s, next, ?_⟩
  refine ⟨True.intro, hardware, zulStart, splitPagesProgramAkzeptiert k [op] hwf, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · change ([name.val] : List (List Char)).Nodup
    refine List.nodup_cons.mpr ?_
    constructor
    · intro h; cases h
    · exact List.nodup_nil
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  · refine ⟨tree, splitPagesParseOfPrint tree (splitPagesPrints name pages), ?_⟩
    exact ⟨op, helab, rfl⟩
  · exact splitPagesParseOfPrint tree (splitPagesPrints name pages)
  · exact helab
  · change (memProgram k [op]).system.IErreichbar (I.start (memProgram k [op]) start).2 s
    exact System.IErreichbar.start
  · change memHead target [op] s entryContext = some op
    exact (splitPagesHeadSingleton target op s entryContext).2
      ⟨rfl, rfl, rfl, by rw [hEval]; rfl⟩
  · exact hEval
  · change ∃ i, memHead target [op] s entryContext = some i ∧
      ∃ frame, i.evaluate target s entryContext = some frame ∧ [plan] = [plan] ∧
        (next.advance entryContext s) = frame.advance entryContext s
    exact ⟨op, (splitPagesHeadSingleton target op s entryContext).2
      ⟨rfl, rfl, rfl, by rw [hEval]; rfl⟩, ⟨next, hEval, rfl, rfl⟩⟩
  · change ∃ i, memHead target [op] s entryContext = some i ∧
      ∃ frame, i.evaluate target s entryContext = some frame ∧ [plan] = [plan] ∧
        (next.advance entryContext s) = frame.advance entryContext s
    exact ⟨op, (splitPagesHeadSingleton target op s entryContext).2
      ⟨rfl, rfl, rfl, by rw [hEval]; rfl⟩, ⟨next, hEval, rfl, rfl⟩⟩

theorem splitPages_aussage : SplitPagesAussage := by
  exact ⟨splitPagesObligations, splitPagesMeaning, splitPagesErfuellbar⟩

end Gabbro.Core.Ast.LowLevel
