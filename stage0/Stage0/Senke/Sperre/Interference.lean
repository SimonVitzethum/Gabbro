/- The first rely/guarantee frame component for concurrent IR refinement.
   A foreign lock operation may change its entire scratch area and lock;
   disjoint observer frames retain complete values, including every ABI word.
   The guarantee is an explicit footprint premise, not a scheduler assumption. -/
module
public import Stage0.Senke.Sperre.Lauf
public import Stage0.Senke.Ausdruck.Aggregat.Werte.ValueProbe
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem

variable {D : Deklaration} {L : Lay D}

/-- Foreign lock bookkeeping cannot change a disjoint observer frame word.
    Either interval order is allowed; the frames need not share a stack. -/
theorem AgreeK.foreign_word {m m' : Mem} {writer fp : W} {s a K i : Nat}
    (interference : AgreeK writer s a m m')
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (index : i < K)
    (scratch : fp.toNat + 8 * K ≤ writer.toNat + 8 * s ∨
      writer.toNat + 8 * (s + 18) ≤ fp.toNat)
    (lock : fp.toNat + 8 * K ≤ a ∨ a + 24 ≤ fp.toNat) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have address := slot_toNat room index
  apply rd64_keep interference.rd
  intro j hj
  have position : (slot fp (BitVec.ofNat 64 i) + BitVec.ofNat 64 j).toNat =
      fp.toNat + 8 * i + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, address]
    omega
  apply interference.b
  · unfold inSlots
    rw [position]
    rcases scratch with before | after <;> omega
  · unfold InLk
    rw [position]
    rcases lock with before | after <;> omega

/-- A foreign operation respecting its lock/scratch footprint preserves the
    observer's permissions and complete local environment. No world or shared
    atomic value is frozen: those belong to the subsequent GX rely proof. -/
theorem AgreeK.foreign_frame {m m' : Mem} {writer fp : W} {s a K reserved : Nat}
    {Γ : Ctx} {ρ : Env D Γ} (interference : AgreeK writer s a m m')
    (frame : FrameOK m fp K) (environment : EnvAt L m fp ρ reserved)
    (fits : frei Γ reserved ≤ K)
    (scratch : fp.toNat + 8 * K ≤ writer.toNat + 8 * s ∨
      writer.toNat + 8 * (s + 18) ≤ fp.toNat)
    (lock : fp.toNat + 8 * K ≤ a ∨ a + 24 ≤ fp.toNat) :
    FrameOK m' fp K ∧ EnvAt L m' fp ρ reserved := by
  refine ⟨⟨frame.lt, ?_, ?_⟩, ?_⟩
  · intro i hi; rw [interference.rd]; exact frame.rd i hi
  · intro i hi; rw [interference.wr]; exact frame.wr i hi
  · intro τ x
    obtain ⟨valid, words⟩ := environment τ x
    refine ⟨valid, fun i hi => ?_⟩
    have width := encodeWords_length L τ (ρ.get x)
    have offset := variableOffset_bound x
    have index : vslot x reserved + i < K := by
      unfold vslot frei at *
      omega
    rw [interference.foreign_word frame.room index scratch lock]
    exact words i hi

end Gabbro.Stage0.Senke
