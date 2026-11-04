/- A computed native result is retained while its guard reads only that slot. -/
module
public import Stage0.Senke.Gleit.Native.Range
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotBasics
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Repeated guard operands are loads, never repeated floating computations. -/
def floatRetainedRangeL (input d : Nat) (lo hi : Int × Int) : Option (List II × Nat) :=
  floatRangeL d lo hi (fun j => some ([ci 2 j input 0], j + 1))

/-- The proof-only word binder is reconstructed from the actual result read.
    It carries every raw bit pattern, without inventing a finite source value. -/
theorem floatRetainedRangeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K top : Nat} {code : List II}
    {lo hi : Int × Int} {x : Float} {word : Runner.W}
    (emitted : floatRetainedRangeL (frei Γ reserved) (frei Γ reserved + 1) lo hi = some (code, top))
    (fits : top ≤ K)
    (pre : Pre L m pc fp K (frei Γ reserved) code ρ W reserved)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some word)
    (decoded : Runner.readFloat word = x) :
    Ok m pc fp K (frei Γ reserved + 1) code (· = Runner.IR.bool (floatRangeReject lo hi x)) := by
  let raw : Zahl (-2 ^ 63) (2 ^ 63 - 1) :=
    ⟨word.toInt, by simpa using BitVec.le_toInt word,
      by simpa using BitVec.toInt_le (x := word)⟩
  have value : ValueAt L m fp (frei Γ reserved) frameWordTy raw := by
    apply ValueAt.of_enc frameWordTy_width read
    exact BitVec.ofInt_toInt.symm
  have auxiliary : Pre L m pc fp K (frei Γ reserved + 1) code
      (Env.cons (τ := frameWordTy) raw ρ) W reserved :=
    ⟨by simp only [frei, contextWords_cons, frameWordTy_width]; omega,
      pre.small, pre.frame, pre.code, pre.far, envAt_cons pre.env value, pre.welt, pre.wstab⟩
  exact nativeFloatRangeL_at_ok lo hi x (fun j child ceiling hc ht m' pc' hp => by
    cases hc
    obtain ⟨w, hr, hw⟩ := ValueAt.word frameWordTy raw (by trivial) (hp.env _ Var.here)
    have location : vslot (Var.here : Var (frameWordTy :: Γ) frameWordTy) reserved = frei Γ reserved := by
      simp only [vslot_here]
    rw [location] at hr
    change w = BitVec.ofInt 64 raw.n at hw
    have actual : w = word := hw.trans BitVec.ofInt_toInt
    rw [actual] at hr
    have room : frei Γ reserved + 1 ≤ j := by
      simpa only [frei_cons, frameWordTy_width] using hp.ctx
    exact (mov_ok hp (by omega) (by omega) hr).mono (fun v hv => by rw [hv]; exact decoded))
    emitted fits auxiliary

end Gabbro.Stage0.Senke
