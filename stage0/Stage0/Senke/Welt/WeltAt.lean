/-
  File:      stage0/Stage0/Senke/Welt/WeltAt.lean
  Subject:   The world in memory (`WeltAt`): every element of every column and every global at its address (`Lay`), as
             the word of its value; an element of a byte column is the low byte of the word read there.

  The world lies above everything a frame uses (`fp + 8K ≤ lo`), so code that writes only its frame keeps it
  (`weltAt_stab`). It describes the slots and globals only, so asking or reading (`lese`, `fragt`, which only
  record events) keeps it by definition.
-/
import Stage0.Senke.AusdruckSim

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

/-- Every element and every global, one word each, inside `[lo, hi)`, below `2^31`. -/
def LayIn (L : Lay D) : Prop :=
  (∀ t f (k : Nat), (k : Int) < D.count t → L.lo ≤ L.elem t f k ∧ L.elem t f k + 8 ≤ L.hi) ∧
  (∀ g, L.lo ≤ L.ga g ∧ L.ga g + 8 ≤ L.hi) ∧ L.hi < 2 ^ 31

/-- The value word of an element: the low byte for a byte column. -/
def cellW {t : D.Tab} (f : D.Feld t) (w : Runner.W) : Runner.W := if byteCol t f then w &&& 255 else w

def WeltAt (m : Runner.Mem) (L : Lay D) (σ : World D) : Prop :=
  (∀ t f (k : Nat), (k : Int) < D.count t → ∃ w, m.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some w ∧
    Enc (D.typ t f) (σ.slots t k f) (cellW f w)) ∧
  (∀ g, ∃ w, m.rd64 (BitVec.ofNat 64 (L.ga g)) = some w ∧ Enc (D.gtyp g) (σ.globs g) w)

/-- A word outside the changed slots reads the same. -/
theorem rd64_agree_out {m m' : Runner.Mem} {fp : Runner.W} {lo K a : Nat} (ha : Agree fp lo K m m')
    (h1 : a + 8 ≤ 2 ^ 64) (h2 : a + 8 ≤ fp.toNat + 8 * lo ∨ fp.toNat + 8 * K ≤ a) :
    m'.rd64 (BitVec.ofNat 64 a) = m.rd64 (BitVec.ofNat 64 a) := by
  simp only [Runner.Mem.rd64, ha.rd]
  rw [le_congr (m := m') (m' := m) (fun j hj => ha.b _ fun ⟨g1, g2⟩ => by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at g1 g2
    omega)]

theorem weltAt_stab {L : Lay D} {σ : World D} {fp : Runner.W} {K : Nat} (hl : LayIn L)
    (hwl : fp.toNat + 8 * K ≤ L.lo) : WStab (fun m => WeltAt m L σ) fp K := by
  intro m m' hm ha
  obtain ⟨hs, hg⟩ := hm
  obtain ⟨hl1, hl2, hl3⟩ := hl
  refine ⟨fun t f k hk => ?_, fun g => ?_⟩
  · obtain ⟨w, hw, he⟩ := hs t f k hk
    have := hl1 t f k hk
    exact ⟨w, by rw [rd64_agree_out ha (by omega) (Or.inr (by omega))]; exact hw, he⟩
  · obtain ⟨w, hw, he⟩ := hg g
    have := hl2 g
    exact ⟨w, by rw [rd64_agree_out ha (by omega) (Or.inr (by omega))]; exact hw, he⟩

theorem frameOK_sub {m : Runner.Mem} {fp : Runner.W} {K Ks : Nat} (h : FrameOK m fp K) (hs : Ks ≤ K) :
    FrameOK m fp Ks :=
  ⟨by have := h.lt; omega, fun i hi => h.rd i (by omega), fun i hi => h.wr i (by omega)⟩

theorem codeFar_sub2 {pc fp : Runner.W} {n K Ks : Nat} (h : CodeFar pc n fp K) (hs : Ks ≤ K) : CodeFar pc n fp Ks := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by omega, by omega⟩

theorem Agree.widen {m m' : Runner.Mem} {fp : Runner.W} {lo Ks K : Nat} (h : Agree fp lo Ks m m') (hs : Ks ≤ K) :
    Agree fp lo K m m' :=
  ⟨h.rd, h.wr, fun x hx => h.b x fun ⟨h1, h2⟩ => hx ⟨h1, by omega⟩⟩

/-- An expression of a statement runs in the frame below `Ks`, with the world above it. -/
theorem PreS.welt {m : Runner.Mem} {pc fp : Runner.W} {K Ks d : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    {L : Lay D} {σ : World D} (hp : PreS m pc fp K d c ρ) (hs : Ks ≤ K) (hw : WeltAt m L σ) (hl : LayIn L)
    (hwl : fp.toNat + 8 * Ks ≤ L.lo) : Pre m pc fp Ks d c ρ (fun m => WeltAt m L σ) :=
  ⟨hp.ctx, by have := hp.small; omega, frameOK_sub hp.frame hs, hp.code, codeFar_sub2 hp.far hs, hp.env, hw, weltAt_stab hl hwl⟩

end Gabbro.Stage0.Senke
