/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Zeuge.lean
  Subject:   Witness of the memory part of the single-step lift (package MT1). Two threads with disjoint, nonempty
             footprints (the eight bytes from 0 and the eight bytes from 16), each its own write set, over one
             memory; thread 0 writes a word at 0. The premises of `verschmolzen_ask` hold jointly
             (`zeuge_verschmolzen`, `zeuge_imFuss`, `zeuge_memAns`), and its conclusion holds there.
-/
module
public import Stage0.Senke.Bild.Mehr.Fuss
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr.Zeuge

open Runner Runner.IR Gabbro.Stage0.Senke.BildMehr

def a0 : W := BitVec.ofNat 64 0
def a16 : W := BitVec.ofNat 64 16

/-- Every byte zero, readable and writable. -/
def zm : Mem := ⟨fun _ => 0, fun _ => true, fun _ => true⟩

def zk : Ans → Res T := fun _ => .fault

def z0 : Solo := ⟨.ask (.wr a0 (BitVec.ofNat 64 5)) zk, zm, fenster a0, fenster a0⟩
def z1 : Solo := ⟨.fault, zm, fenster a16, fenster a16⟩

def zS : Nat → Option Solo
  | 0 => some z0
  | 1 => some z1
  | _ + 2 => none

theorem zeuge_getrennt {y : W} (h0 : fenster a0 y) (h1 : fenster a16 y) : False := by
  have := y.isLt
  simp only [fenster, a0, a16, BitVec.toNat_sub, BitVec.toNat_ofNat] at h0 h1
  omega

theorem zeuge_verschmolzen : Verschmolzen zm zS where
  gleich := by
    intro i s hi y _
    rcases i with _ | _ | i
    · cases hi
      exact GleichAt.refl _ _
    · cases hi
      exact GleichAt.refl _ _
    · cases hi
  wrF := by
    intro i s hi y hy
    rcases i with _ | _ | i
    · cases hi
      exact hy
    · cases hi
      exact hy
    · cases hi
  getrennt := by
    intro i j s u hij hi hj y hy hu
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> cases hi <;> cases hj
    · exact hij rfl
    · exact zeuge_getrennt hy hu
    · exact zeuge_getrennt hu hy
    · exact hij rfl

theorem zeuge_imFuss : ImFuss z0 := by
  intro o k e
  cases e
  exact ⟨fun _ hy => hy, fun _ _ hy => hy⟩

theorem zeuge_memAns :
    memAns zm (.wr a0 (BitVec.ofNat 64 5)) = some (some (0, 0), Mem.write zm a0 8 (BitVec.ofNat 64 5).toNat) := by
  simp only [memAns_wr, Mem.wr64_some (m := zm) (a := a0) (v := BitVec.ofNat 64 5) (Mem.all_of fun _ _ => rfl)]

/-- **The witness**: thread 0's write is answered in its solo memory as in the shared memory, both threads stay
    related to the new shared memory, and the shared memory changed inside thread 0's write set only. -/
theorem verschmolzen_ask_zeuge :
    ∃ m2', memAns zm (.wr a0 (BitVec.ofNat 64 5)) = some (some (0, 0), m2') ∧
      Verschmolzen (Mem.write zm a0 8 (BitVec.ofNat 64 5).toNat)
        (setzeS zS 0 { z0 with r := zk (some (0, 0)), m := m2' }) ∧
      ∀ y, ¬ fenster a0 y → GleichAt (Mem.write zm a0 8 (BitVec.ofNat 64 5).toNat) zm y :=
  verschmolzen_ask zeuge_verschmolzen (i := 0) rfl rfl zeuge_imFuss zeuge_memAns

end Gabbro.Stage0.Senke.BildMehr.Zeuge
