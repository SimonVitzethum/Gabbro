/- Compositional semantics for pure word-code generators used by software floats. -/
import Stage0.Senke.Ausdruck.Gleit.Wort
import Stage0.Senke.Ausdruck.Aggregat.Wort

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- A pure generator may be evaluated at any free slot and reread without effects. -/
abbrev WordCode (ρ : Env D Γ) (W : Runner.Mem → Prop)
    (a : Nat → Option (List II × Nat)) (v : Runner.W) : Prop :=
  ∀ {fp K d c top}, a d = some (c, top) → top ≤ K → ∀ m pc,
    Pre L m pc fp K d c ρ W → Ok m pc fp K d c (· = v)

/-- An input retained below the temporary interval survives composition. -/
theorem slotRead_agree {m m' : Runner.Mem} {fp : Runner.W}
    {K d input : Nat} {v : Runner.W}
    (frame : FrameOK m fp K) (ha : Agree fp d K m m')
    (hi : input < d) (hd : d ≤ K)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some v) :
    m'.rd64 (slot fp (BitVec.ofNat 64 input)) = some v := by
  rw [agree_rd_low ha frame.room hi hd]
  exact read

theorem WordCode.bin {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {va vb v : Runner.W} {o : Nat}
    {g : Runner.W → Runner.W → Option Runner.W}
    (ha : WordCode (L := L) ρ W a va) (hb : WordCode (L := L) ρ W b vb)
    (hg : g va vb = some v) (hop : op o = bin g) (ho : o < 256) :
    WordCode (L := L) ρ W (fun d => wordL o d (a d) (b (d + 1))) v := by
  intro fp K d c top h hK m pc hp
  exact wordL_ok h hK (fun _ _ he ht => ha he ht) (fun _ _ he ht => hb he ht)
    (fun x y hx hy => ⟨v, by simpa only [hx, hy] using hg, rfl⟩) hop ho hp

theorem WordCode.const {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (n : Int) (hn : lit32 n = true) :
    WordCode (L := L) ρ W (fun d => some ([ci 1 d n 0], d + 1))
      (BitVec.ofInt 64 n) := by
  intro fp K d c top h hK m pc hp
  cases h
  exact const_ok hp hn (by omega)

/-- All unsigned words, including those above the signed range. -/
theorem WordCode.konst {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (n : Nat) (hn : n < 2^64) :
    WordCode (L := L) ρ W (fun d => some (konstWL 4 n d)) (BitVec.ofNat 64 n) := by
  intro fp K d c top h hK m pc hp
  cases h
  exact konstWL_ok 4 n (by simpa using hn)
    (by simp only [konstWL, bin2] at hK; omega) hp

end Gabbro.Stage0.Senke
