/- The first rely/guarantee frame component for concurrent IR refinement.
   A foreign lock operation may change its entire scratch area and lock;
   disjoint observer frames retain complete values, including every ABI word.
   The guarantee is an explicit footprint premise, not a scheduler assumption. -/
import Stage0.Senke.Sperre.Lauf
import Stage0.Senke.Ausdruck.Aggregat.ValueProbe

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

/-- A three-word local array survives writes to another thread's scratch and
    a shared lock word. Both writes really change memory; all frame and ABI
    premises are supplied jointly. -/
theorem foreign_frame_zeuge {D : Deklaration} (L : Lay D) :
    let m := ValueProbe.memory
    let m' := write (write m (slot 6144 4) 8 99) 8192 8 2
    AgreeK 6144 4 8192 m m' ∧
    m.rd64 (slot 6144 4) = some 0 ∧ m.rd64 8192 = some 0 ∧
    m'.rd64 (slot 6144 4) = some 99 ∧ m'.rd64 8192 = some 2 ∧
    FrameOK m' 4096 7 ∧ EnvAt L m' 4096 ValueProbe.env ∧
    encodeWords L ValueProbe.shape (ValueProbe.value (D := D)) = [1, 2, 3] := by
  intro m m'
  letI : Kern := futexKernel
  have interference : AgreeK 6144 4 8192 m m' :=
    (agreeK_slot (fp := 6144) (s := 4) (a := 8192) (d := 0)
      (by decide) (by decide) 99).trans
      (agreeK_lk (y := 8192) (Nat.le_refl _) (by decide) (by decide) 2)
  have observer : FrameOK m 4096 7 :=
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have kept := interference.foreign_frame observer (ValueProbe.env_at L)
    (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  exact ⟨interference, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, kept.1, kept.2, rfl⟩

end Gabbro.Stage0.Senke
