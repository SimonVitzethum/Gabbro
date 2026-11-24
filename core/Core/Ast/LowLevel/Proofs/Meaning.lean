module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level form-specific proofs

Invert name and layout resolution and the checked local transfer. The view
must make a second borrow of the same grant unavailable. For an environment
selection, both the row membership and exact ABI matter.

- `AddressTypeMeaningAussage`
- `RegionAddressMeaningAussage`
- `ViewMeaningAussage`
- `EnvironmentMeaningAussage`
-/

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

private lemma layout_endian (target : ZielDaten) (t : WrittenType) (shape : Layout)
    (h : layout target t = some shape) : shape.endian = ByteOrder.ofTarget target := by
  cases t with
  | integer signed width range =>
      simp only [layout] at h
      split at h
      · injection h with hs
        subst shape
        rfl
      · cases h
  | _ =>
    simp only [layout] at h
    cases h

private lemma heldRegion_borrowed_none {k : Katalog} (s : State k) (c : Kontext) (slot : Nat)
    (h : (⟨slot, 0⟩ : Griff) ∈ (s.lokal c).borrowed) :
    heldRegion s c slot = none := by
  unfold heldRegion
  dsimp
  rw [List.contains_eq_mem]
  rw [decide_eq_true h]
  rw [Bool.not_true]
  rw [Bool.and_false]
  cases (s.lokal c).regions[slot]? with
  | none => rfl
  | some extent =>
      dsimp

theorem addressTypeMeaning : AddressTypeMeaningAussage := by
  intro k scope space op hop
  simp only [elaborate] at hop
  split at hop
  · injection hop with hop'
    subst op
    exact ⟨_, _, rfl⟩
  · cases hop

theorem regionAddressMeaning : RegionAddressMeaningAussage := by
  intro k scope region op s c transfer hop heval
  simp only [elaborate, Option.map] at hop
  cases hslot : scope.slot region with
  | none =>
      simp only [hslot, Option.map] at hop
      cases hop
  | some slot =>
      simp only [hslot, Option.map] at hop
      injection hop with hop'
      subst op
      cases hhr : heldRegion s c slot with
      | none =>
          simp only [Instruction.evaluate] at heval
          rw [hhr] at heval
          dsimp at heval
          cases heval
      | some pair =>
          rcases pair with ⟨handleV, extent⟩
          by_cases hlt : extent.von < 2 ^ k.plattform.ziel.physicalBits
          · simp only [Instruction.evaluate] at heval
            rw [hhr] at heval
            dsimp at heval
            rw [dif_pos hlt] at heval
            injection heval with hval
            subst transfer
            exact ⟨slot, handleV, extent, ⟨k.plattform.ziel.physicalBits, extent.von, rfl, hlt⟩,
              (by first | exact hslot | rfl), hhr, rfl, rfl, rfl⟩
          · simp only [Instruction.evaluate] at heval
            rw [hhr] at heval
            dsimp at heval
            rw [dif_neg hlt] at heval
            cases heval

theorem viewMeaning : ViewMeaningAussage := by
  intro k scope region type op s c transfer hop heval
  simp only [elaborate, Option.bind, Option.bind_some] at hop
  cases hslot : scope.slot region with
  | none =>
      simp only [hslot, Option.bind, Option.bind_some] at hop
      cases hop
  | some slot =>
      cases hlayout : layout k.plattform.ziel type with
      | none =>
          simp only [hslot, hlayout, Option.bind, Option.bind_some] at hop
          cases hop
      | some shape =>
          simp only [hslot, hlayout, Option.bind, Option.bind_some] at hop
          injection hop with hop'
          subst op
          cases hhr : heldRegion s c slot with
          | none =>
              simp only [Instruction.evaluate] at heval
              rw [hhr] at heval
              dsimp at heval
              cases heval
          | some pair =>
              rcases pair with ⟨handleV, extent⟩
              by_cases hcond : shape.fits extent
              · simp only [Instruction.evaluate] at heval
                rw [hhr] at heval
                dsimp at heval
                rw [if_pos hcond] at heval
                injection heval with hval
                subst transfer
                have hendian : shape.endian = ByteOrder.ofTarget k.plattform.ziel :=
                  layout_endian k.plattform.ziel type shape hlayout
                have hhandle : handleV = ⟨slot, 0⟩ := by
                  have hhr' := hhr
                  unfold heldRegion at hhr'
                  dsimp at hhr'
                  cases hreg : (s.lokal c).regions[slot]? with
                  | none =>
                      rw [hreg] at hhr'
                      dsimp at hhr'
                      cases hhr'
                  | some extent0 =>
                      rw [hreg] at hhr'
                      dsimp at hhr'
                      split at hhr'
                      · cases hleihe : s.leihen slot with
                        | eigen =>
                            simp only [hleihe] at hhr'
                            have hpair : ((⟨slot, 0⟩ : Griff), extent0) = (handleV, extent) :=
                              Option.some.inj hhr'
                            exact (congrArg Prod.fst hpair).symm
                        | verliehen x =>
                            simp only [hleihe] at hhr'
                            cases hhr'
                      · cases hhr'
                have hb :
                    (⟨slot, 0⟩ : Griff) ∈
                      (((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                          some handleV⟩ : Transfer k).apply c s).lokal c).borrowed := by
                  simp only [Transfer.apply, Function.update_self, hhandle, Option.toList,
                    List.mem_append, List.mem_singleton, true_or]
                have hlast :
                    heldRegion
                      ((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                          some handleV⟩ : Transfer k).apply c s) c slot = none :=
                  heldRegion_borrowed_none ((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                    some handleV⟩ : Transfer k).apply c s) c slot hb
                exact ⟨slot, handleV, extent, shape, (by first | exact hslot | rfl), hhr,
                  (by first | exact hlayout | rfl), hendian, hcond.1, hcond.2, rfl, rfl, hlast⟩
              · simp only [Instruction.evaluate] at heval
                rw [hhr] at heval
                dsimp at heval
                rw [if_neg hcond] at heval
                cases heval

theorem environmentMeaning : EnvironmentMeaningAussage := by
  intro k scope name abi row
  constructor
  · rintro ⟨op, hop⟩
    simp only [elaborate] at hop
    by_cases h : row.zugelassen k abi
    · exact h
    · rw [dif_neg h] at hop
      cases hop
  · intro h
    have hz : row.zugelassen k abi := by
      unfold FirmwareZeile.zugelassen
      exact h
    refine ⟨.selectEnvironment name abi row hz, ?_⟩
    simp only [elaborate]
    rw [dif_pos hz]

end Gabbro.Core.Ast.LowLevel
