/- A satisfiable result-area provider writes every canonical word and no other byte. -/
module
public import Stage0.Senke.Tore.AreaProbes
public import Stage0.Senke.Welt.Schreib
@[expose] public section

namespace Gabbro.Stage0.Senke.ForeignAreaContractWitness
open Gabbro.Grammatik Runner.IR Runner.Mem ForeignAreaProbe
abbrev D := ForeignAreaProbe.D 96 false
def layout : Lay D := layU (u 96 false) (fun _ => some (binding false)) 0
def provider : Orakel D := oracle 96 false false
def value : Wert D (answerTy 96) := ⟨2 ^ 80, by decide, by decide⟩

/-- This is an explicit software service witness on the abstract runner
    relation, not a claim that a host system call implements this provider. -/
theorem area_contract_zeuge :
    @AreaContract ⟨fun _ _ _ _ => True⟩ D layout provider := by
  letI : Kern := ⟨fun _ _ _ _ => True⟩
  intro a b τ he j bound accepted σ ρ request m fp base K frame capacity separated below
    number arguments hidden unused world
  obtain ⟨a, ha⟩ := a
  have zero : a = 0 := by change a < 1 at ha; omega
  subst a
  have resultType : answerTy 96 = τ := by
    have same : some (answerTy 96) = some τ := he
    exact Option.some.inj same
  subst τ
  have bindingType : binding false = b := by
    have same : some (binding false) = some b := bound
    exact Option.some.inj same
  subst b
  let address := fp.toNat + 8 * base
  let words := encodeWords layout (answerTy 96) value
  let output := writeSpan m address words
  have width : words.length = valueWords (answerTy 96) := encodeWords_length _ _ _
  have fits : address + 8 * words.length ≤ 2 ^ 64 := by
    have room := frame.room
    dsimp only [address]
    omega
  have stored : StorageAt layout output address (answerTy 96) value := by
    apply writeValue_same (by simpa only [width] using fits)
    · intro i hi
      exact frame_rd_at frame (by dsimp only [address]; omega)
        (by dsimp only [address]; omega)
    · trivial
  have baseAddress : slot fp (BitVec.ofNat 64 base) = BitVec.ofNat 64 address := by
    apply BitVec.eq_of_toNat_eq
    rw [slot_toNat frame.room (by have := valueWords_pos (answerTy 96); omega)]
    simp only [BitVec.toNat_ofNat]
    have room := frame.room
    dsimp only [address]
    omega
  have payload : ValueAt layout output fp base (answerTy 96) value := by
    refine ⟨stored.1, ?_⟩
    intro i hi
    rw [← slot_plus fp base i, baseAddress, ← BitVec.ofNat_add]
    simpa only [Nat.zero_add, absolute_slot] using stored.2 i hi
  refine ⟨0, 0, output, trivial, ?_, ?_, ?_⟩
  · refine ⟨writeSpan_rd _ _ _, writeSpan_wr _ _ _, ?_⟩
    intro x outside outsideWorld
    apply writeSpan_out _ _ _ fits
    unfold inSlots at outside
    dsimp only [address]
    omega
  · exact ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g),
      world.2.2.keep (writeSpan_wr _ _ _)⟩
  · refine .inl ⟨value, ?_, rfl, payload⟩
    decide +kernel

/-- The exact layout/oracle pair jointly satisfies all inherited gate
    premises. Register-only obligations are impossible for an area profile. -/
theorem gate_contract_zeuge : @TorOK ⟨fun _ _ _ _ => True⟩ D layout provider := by
  letI : Kern := ⟨fun _ _ _ _ => True⟩
  refine ⟨?_, ?_, ?_, area_contract_zeuge⟩
  · intro a b bound accepted
    have same : some (binding false) = some b := bound
    cases same
    simp only [torGut, binding, Option.isNone_some, Bool.and_false] at accepted
    cases accepted
  · intro a b bound accepted
    have same : some (binding false) = some b := bound
    cases same
    simp only [torGut, binding, Option.isNone_some, Bool.and_false] at accepted
    cases accepted
  · intro a n he
    obtain ⟨a, ha⟩ := a
    have zero : a = 0 := by change a < 1 at ha; omega
    subst a
    have impossible : some (answerTy 96) = some (.ref n) := he
    cases impossible

end Gabbro.Stage0.Senke.ForeignAreaContractWitness
