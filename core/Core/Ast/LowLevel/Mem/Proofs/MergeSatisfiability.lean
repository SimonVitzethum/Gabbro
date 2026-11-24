module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.MergeObligations
public import Core.Ast.LowLevel.Mem.Proofs.MergePreservation

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine Text
open Gabbro.Core.Annahme

private theorem memProgram_akzeptiert (k : Katalog) (code : List MemInstruction)
    (hwf : KatalogWohlgeformt k) : Annahme.Akzeptiert (memProgram k code) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hwf, ?_, ?_⟩
    · intro i c s u w pl hstep
      dsimp [memProgram, MemInstruction.rule, MemInstruction.step] at hstep
      rcases hstep with ⟨frame, heval, hpl, hu⟩
      have hpl' : pl = plan := (List.cons.inj hpl).1
      subst pl
      rw [Annahme.Befugt]
      constructor
      · intro x hx
        simp only [plan] at hx
        cases hx
      · intro l hl
        simp only [plan] at hl
        cases hl
    · refine ⟨zulassung_m2 k.plattform, ?_⟩
      apply aussen_gueltig_aus_kontext (memProgram k code)
      intro run t s c w spur s' step
      cases step with
      | kontext _ _ regel execute =>
        obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
        cases (List.cons.inj planEq).1
        dsimp [memProgram] at execute
        obtain ⟨rfl, rfl⟩ := MemInstruction.genauInternal (k := k) execute
        exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
          (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · intro ρ hρ
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      dsimp [kanonischeKlauseln] at hp
      cases hp
    · intro t p hp
      dsimp [kanonischeKlauseln] at hp
      cases hp
    · intro t hfertig p hp
      dsimp [kanonischeKlauseln] at hp
      cases hp
  · constructor
    · intro ρ hρ t op args bedarf
      dsimp [kanonischeVerwendung]
      exact False.elim bedarf
    · intro ρ hρ t hclosed
      rcases hclosed with ⟨C, hex, hall⟩
      obtain ⟨c, hc⟩ := hex
      obtain ⟨b, hblock, _⟩ := hall c hc
      dsimp [memProgram] at hblock
      cases hblock

private def memNameL : Identifier :=
  ⟨['l'], ⟨'l', [], rfl, by decide, by intro a h; cases h⟩⟩

private def memNameR : Identifier :=
  ⟨['r'], ⟨'r', [], rfl, by decide, by intro a h; cases h⟩⟩

private theorem memNameL_ne_R : memNameL.val ≠ memNameR.val := by
  decide

private theorem memZulStart {k : Katalog} {h : Katalog.Umgebung} {regions : List Strecke}
    (hw : Hardware k h) (img : image.gueltig k.plattform.ziel)
    (pairwise : regions.Pairwise Strecke.getrennt)
    (ok : ∀ r ∈ regions, r.von < r.bis ∧ r.bis ≤ 2 ^ k.plattform.ziel.physicalBits ∧
      ∀ e d, k.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window) :
    Katalog.ZulStart k h image
      ⟨0, (fun i => if i = 0 then some 0 else none), regions, (fun _ => none), h.politik.sicht 0 []⟩ := by
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

private theorem memRegionOk (extent : Strecke)
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

theorem merge_erfuellbar : MemErfuellbarAussage .merge := by
  let k : Katalog := Plattform.x86_64.katalog
  let scope : MemScope := ⟨[memNameL, memNameR], [], []⟩
  let tree : MemTree .merge := .merge memNameL memNameR
  let op : MemInstruction := .mergeRegions 0 1
  let extentL : Strecke := ⟨0x1000, 0x2000⟩
  let extentR : Strecke := ⟨0x2000, 0x3000⟩
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer
  let env : Katalog.Umgebung := Katalog.Umgebung.referenz k 1 sicht
  let start : AussenStart :=
    ⟨0, (fun i => if i = 0 then some 0 else none), [extentL, extentR], (fun _ => none),
      env.politik.sicht 0 []⟩
  let E : MemUnit := memProgram k [op]
  let s : MemState := (I.start E start).2
  let text : RawText := tree.print
  let frame : MemFrame := s.lokal entryContext
  let joined : MemRegion :=
    ⟨⟨min extentL.von extentR.von, max extentL.bis extentR.bis⟩,
      [⟨0, 0⟩] ++ [⟨1, 0⟩]⟩
  let next : MemFrame :=
    { frame with
      result := some (.merged joined)
      regions := (frame.regions.set 0 (some joined)).set 1 none }
  refine ⟨k, scope, tree, op, env, start, text, [], s, next, ?_⟩
  dsimp only
  constructor
  · trivial
  constructor
  · exact Katalog.Umgebung.referenz_hardware k 1 sicht
      (by simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
  constructor
  · apply memZulStart (k := k) (h := env) (regions := [extentL, extentR])
    · exact Katalog.Umgebung.referenz_hardware k 1 sicht
        (by simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64) (by omega)
    · simpa [k, Plattform.katalog] using (show image.gueltig (Plattform.x86_64).ziel by
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
          exact ⟨0, rfl⟩)
    · apply List.Pairwise.cons
      · intro r hr
        have : r = extentR := List.mem_singleton.mp hr
        subst r
        unfold Strecke.getrennt
        change 0x2000 ≤ 0x2000 ∨ 0x3000 ≤ 0x1000
        exact Or.inl (by omega)
      · exact List.Pairwise.nil
    · intro r hr
      simp only [List.mem_cons, List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · apply memRegionOk
        · change 0x1000 < 0x2000 ∧ 0x2000 ≤ 2 ^ (52 : Nat)
          constructor <;> omega
        · unfold Strecke.getrennt
          change 0x2000 ≤ 0x10000000 ∨ 0x10000200 ≤ 0x1000
          exact Or.inl (by omega)
      · apply memRegionOk
        · change 0x2000 < 0x3000 ∧ 0x3000 ≤ 2 ^ (52 : Nat)
          constructor <;> omega
        · unfold Strecke.getrennt
          change 0x3000 ≤ 0x10000000 ∨ 0x10000200 ≤ 0x2000
          exact Or.inl (by omega)
  constructor
  · apply memProgram_akzeptiert
    simpa [k, Plattform.katalog] using Plattform.katalog_wohlgeformt .x86_64
  constructor
  · change (memNameL.val :: memNameR.val :: []).Nodup
    apply List.nodup_cons.mpr
    constructor
    · exact memNameL_ne_R
    · exact List.nodup_singleton _
  constructor
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  constructor
  · change ([] : List (List Char)).Nodup
    exact List.nodup_nil
  constructor
  · refine ⟨tree, ?_, ?_⟩
    · exact (memDruckAussage_merge tree).2
    · refine ⟨op, ?_, rfl⟩
      change (scope.slotRegion memNameL).bind (fun left =>
        (scope.slotRegion memNameR).map (fun right => MemInstruction.mergeRegions left right)) = some op
      dsimp [scope, MemScope.slotRegion]
      simp only [List.map_cons, List.map_nil, List.idxOf?_cons, beq_self_eq_true, if_true,
        memNameL_ne_R, beq_iff_eq, if_false]
  constructor
  · exact (memDruckAussage_merge tree).2
  constructor
  · change (scope.slotRegion memNameL).bind (fun left =>
      (scope.slotRegion memNameR).map (fun right => MemInstruction.mergeRegions left right)) = some op
    dsimp [scope, MemScope.slotRegion]
    simp only [List.map_cons, List.map_nil, List.idxOf?_cons, beq_self_eq_true, if_true,
      memNameL_ne_R, beq_iff_eq, if_false]
  constructor
  · exact System.IErreichbar.start
  constructor
  · -- head at start
    dsimp [E, memUnit, memProgram, memHead, s, I.start]
    rw [if_pos rfl]
    -- status laeuft, pc 0, eval some next
    have hleft : heldMemRegion k.plattform.ziel ((I.start (memProgram k [op]) start).2)
        entryContext 0 = some ⟨extentL, [⟨0, 0⟩]⟩ := by
      dsimp [heldMemRegion, memBoot, MemRegion.live, MemFrame.unreserved]
      simp only [List.getElem?_cons_zero, decide_true, Bool.not_false, List.isEmpty_cons,
        Bool.not_true, List.all_cons, List.all_nil, and_true]
    have hright : heldMemRegion k.plattform.ziel ((I.start (memProgram k [op]) start).2)
        entryContext 1 = some ⟨extentR, [⟨1, 0⟩]⟩ := by
      dsimp [heldMemRegion, memBoot, MemRegion.live, MemFrame.unreserved]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, decide_true, Bool.not_false,
        List.isEmpty_cons, Bool.not_true, List.all_cons, List.all_nil, and_true]
    rw [hleft, hright]
    simp only [Option.bind_some]
    rw [if_pos ⟨by decide, by change 0x1000 < 0x2000; omega, by change 0x2000 < 0x3000; omega,
      Or.inl (by change 0x2000 = 0x2000; rfl)⟩]
    rfl
  constructor
  · -- evaluate
    dsimp [E, s]
    have hleft : heldMemRegion k.plattform.ziel ((I.start (memProgram k [op]) start).2)
        entryContext 0 = some ⟨extentL, [⟨0, 0⟩]⟩ := by
      dsimp [heldMemRegion, memBoot, MemRegion.live, MemFrame.unreserved]
      simp only [List.getElem?_cons_zero, decide_true, Bool.not_false, List.isEmpty_cons,
        Bool.not_true, List.all_cons, List.all_nil, and_true]
    have hright : heldMemRegion k.plattform.ziel ((I.start (memProgram k [op]) start).2)
        entryContext 1 = some ⟨extentR, [⟨1, 0⟩]⟩ := by
      dsimp [heldMemRegion, memBoot, MemRegion.live, MemFrame.unreserved]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, decide_true, Bool.not_false,
        List.isEmpty_cons, Bool.not_true, List.all_cons, List.all_nil, and_true]
    dsimp [MemInstruction.evaluate]
    rw [hleft, hright]
    simp only [Option.bind_some]
    rw [if_pos ⟨by decide, by change 0x1000 < 0x2000; omega, by change 0x2000 < 0x3000; omega,
      Or.inl (by change 0x2000 = 0x2000; rfl)⟩]
    rfl
  constructor
  · exact ⟨op, rfl, ⟨next, rfl, rfl⟩⟩
  · exact ⟨op, rfl, ⟨next, rfl, rfl⟩⟩

end Gabbro.Core.Ast.LowLevel
