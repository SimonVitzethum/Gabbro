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
  | bool => simp [layout] at h
  | array element count => simp [layout] at h
  | tuple first second rest => simp [layout] at h
  | integer signed width range =>
      simp only [layout] at h
      split at h
      · injection h with hs
        subst shape
        rfl
      · cases h

private lemma heldRegion_borrowed_none {k : Katalog} (s : State k) (c : Kontext) (slot : Nat)
    (h : (⟨slot, 0⟩ : Griff) ∈ (s.lokal c).borrowed) :
    heldRegion s c slot = none := by
  unfold heldRegion
  dsimp
  simp [h]

theorem addressTypeMeaning : AddressTypeMeaningAussage := by
  intro k scope space op hop
  simp [elaborate] at hop
  rcases hop with ⟨h, hop'⟩
  subst op
  exact ⟨_, _, rfl⟩

theorem regionAddressMeaning : RegionAddressMeaningAussage := by
  intro k scope region op s c transfer hop heval
  simp [elaborate] at hop
  cases hslot : scope.slot region with
  | none =>
      simp [hslot] at hop
  | some slot =>
      simp [hslot] at hop
      subst op
      cases hhr : heldRegion s c slot with
      | none =>
          simp [Instruction.evaluate, hhr] at heval
      | some pair =>
          rcases pair with ⟨handleV, extent⟩
          by_cases hlt : extent.von < 2 ^ k.plattform.ziel.physicalBits
          · simp [Instruction.evaluate, hhr, hlt] at heval
            subst transfer
            exact ⟨slot, handleV, extent, ⟨k.plattform.ziel.physicalBits, extent.von, rfl, hlt⟩,
              (by first | exact hslot | rfl), hhr, rfl, rfl, rfl⟩
          · simp [Instruction.evaluate, hhr, hlt] at heval

theorem viewMeaning : ViewMeaningAussage := by
  intro k scope region type op s c transfer hop heval
  simp [elaborate] at hop
  cases hslot : scope.slot region with
  | none => simp [hslot] at hop
  | some slot =>
      cases hlayout : layout k.plattform.ziel type with
      | none => simp [hslot, hlayout] at hop
      | some shape =>
          simp [hslot, hlayout] at hop
          subst op
          cases hhr : heldRegion s c slot with
          | none => simp [Instruction.evaluate, hhr] at heval
          | some pair =>
              rcases pair with ⟨handleV, extent⟩
              by_cases hcond : extent.von % shape.alignment = 0 ∧ extent.von + shape.bytes ≤ extent.bis
              · simp [Instruction.evaluate, hhr, hcond] at heval
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
                  simp [Transfer.apply, hhandle]
                have hlast :
                    heldRegion
                      ((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                          some handleV⟩ : Transfer k).apply c s) c slot = none :=
                  heldRegion_borrowed_none ((⟨.view slot handleV ⟨extent.von, extent.von + shape.bytes⟩ shape,
                    some handleV⟩ : Transfer k).apply c s) c slot hb
                exact ⟨slot, handleV, extent, shape, (by first | exact hslot | rfl), hhr,
                  (by first | exact hlayout | rfl), hendian, hcond.1, hcond.2, rfl, rfl, hlast⟩
              · simp [Instruction.evaluate, hhr, hcond] at heval

theorem environmentMeaning : EnvironmentMeaningAussage := by
  intro k scope name abi row
  constructor
  · rintro ⟨op, hop⟩
    simp [elaborate] at hop
    by_cases h : row.zugelassen k abi
    · exact h
    · simp [h] at hop
  · intro h
    have hz : row.zugelassen k abi := by
      unfold FirmwareZeile.zugelassen
      exact h
    refine ⟨.selectEnvironment name abi row hz, ?_⟩
    simp [elaborate, hz]

end Gabbro.Core.Ast.LowLevel
