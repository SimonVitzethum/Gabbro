/- The existing checked branch template for native conversion outcomes. -/
module
public import Stage0.Senke.Gleit.Native.Values
public import Stage0.Senke.Ausdruck.Wenn
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Reserve the destination even when a selected child has no instructions. -/
def routineChooseL (d : Nat) (condition yes no : Nat → Option (List II × Nat)) :
    Option (List II × Nat) := do
  let code ← wennL d (condition d) (yes d) (no d)
  pure (code.1, max code.2 (d + 1))

theorem nativeFloatChooseL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {condition yes no : Nat → Option (List II × Nat)} {flag : Bool} {yv nv : Float}
    (hc : WordCode (L := L) (reserved := reserved) ρ W condition (Runner.IR.bool flag))
    (hy : flag = true → NativeFloatCode (L := L) (reserved := reserved) ρ W yes yv)
    (hn : flag = false → NativeFloatCode (L := L) (reserved := reserved) ρ W no nv) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => routineChooseL d condition yes no) (if flag then yv else nv) := by
  intro fp K d code top h hK m pc hp
  simp only [routineChooseL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨body, ceiling⟩, hb, he, ht⟩ := h
  dsimp only at he ht
  subst body
  subst top
  apply wennL_ok hb (by omega) (by omega) (bc := flag)
    (P := fun m' => ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧
      Runner.readFloat w = if flag then yv else nv)
  · intro c t he ht m pc pre
    exact hc he ht m pc pre
  · intro ht c t he htop m pc pre
    simpa only [Ok, Executes, ht, ite_true] using hy ht he htop m pc pre
  · intro hf c t he htop m pc pre
    simpa only [Ok, Executes, hf, Bool.false_eq_true, ite_false] using hn hf he htop m pc pre
  · exact hp

end Gabbro.Stage0.Senke
