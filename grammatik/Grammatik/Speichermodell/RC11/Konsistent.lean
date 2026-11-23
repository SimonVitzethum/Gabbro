/-
  File:      Grammatik/Speichermodell/RC11/Konsistent.lean
  Subject:   THE AXIOMATIC MEMORY MODEL W, part 3: RC11 consistency with `po ∪ rf` acyclic (the
             memory model of PERFECT-MODEL §3.4/§3.5), sequential consistency in Shasha–Snir form,
             and the two side conditions of the DRF-SC theorem (only `seq_cst` atomics, no race).
-/
module

public import Grammatik.Speichermodell.RC11.Relationen

@[expose] public section

namespace Gabbro.Grammatik.Speichermodell.RC11

namespace Graph

variable {E Ort Wert : Type} (G : Graph E Ort Wert)

/-- **RC11 consistency without load buffering** (Lahav et al., PLDI 2017, Def. 1, fence-free, with
    NO-THIN-AIR strengthened to `po ∪ rf` acyclic as RC11 itself does):
    * `hb_irrefl`, `kohaerent` -- COHERENCE: `hb ; eco?` is irreflexive;
    * `atomar` -- ATOMICITY: no write sits in `mo` between an update and the write it reads;
    * `psc` -- SC: `psc` is acyclic;
    * `ohneLB` -- NO-THIN-AIR: `po ∪ rf` is acyclic (no load buffering). -/
structure Konsistent : Prop where
  wf : G.Wohlgeformt
  hb_irrefl : ∀ a, ¬ G.hb a a
  kohaerent : ∀ a b, G.hb a b → ¬ G.eco b a
  atomar : ∀ w u w', G.rf w u → G.istRmw u → G.mo w w' → ¬ G.mo w' u
  psc : Azyklisch G.psc
  ohneLB : Azyklisch G.porf

/-- One step of the sequentially consistent order `po ∪ rf ∪ mo ∪ rb`. -/
def scSchritt (a b : E) : Prop := G.po a b ∨ G.rf a b ∨ G.mo a b ∨ G.rb a b

/-- **Sequential consistency** (Shasha–Snir): `po ∪ rf ∪ mo ∪ rb` is acyclic. Its reading as an
    interleaving on one memory is `sc_verschraenkung` (SCOrdnung.lean). -/
def SCKonsistent : Prop := Azyklisch G.scSchritt

/-- Every atomic access is `seq_cst`. -/
def NurSC : Prop := ∀ a, G.na a ∨ G.sc a

/-- Two distinct accesses to one location of which one writes. -/
def Konflikt (a b : E) : Prop := a ≠ b ∧ G.ort a = G.ort b ∧ (G.schreibt a ∨ G.schreibt b)

/-- **Race freedom**: two conflicting accesses one of which is plain are ordered by `hb`. -/
def Rennfrei : Prop := ∀ a b, G.Konflikt a b → (G.na a ∨ G.na b) → G.hb a b ∨ G.hb b a

variable {G}

/-- `rf` is irreflexive on a consistent graph (an update never reads itself). -/
theorem Konsistent.rf_irrefl (hk : G.Konsistent) (a : E) : ¬ G.rf a a :=
  fun h => hk.ohneLB a (.single (Or.inr h))

/-- On a consistent graph an `hb`-ordered pair is not `eco`-ordered backwards: the direction of
    any conflicting pair that `hb` orders is the direction of `eco`. -/
theorem Konsistent.hb_richtung (hk : G.Konsistent) {a b : E} (he : G.eco a b)
    (h : G.hb a b ∨ G.hb b a) : G.hb a b := by
  cases h with
  | inl h => exact h
  | inr h => exact absurd he (hk.kohaerent b a h)

end Graph

end Gabbro.Grammatik.Speichermodell.RC11
