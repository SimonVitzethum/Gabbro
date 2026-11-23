/-
  File:      core/Core/Speicher/Relationen.lean
  Subject:   THE AXIOMATIC MEMORY MODEL W, part 2: the shape of a graph (`Wohlgeformt`) and the
             derived relations of RC11 without fences: reads-before `rb`, extended coherence order
             `eco`, release sequences `Rs`, synchronises-with `sw`, happens-before `hb`, the SC base
             `scb` and the partial SC relation `psc` (Lahav et al., PLDI 2017, §3, fence-free part).
-/
module

public import Core.Speicher.Basis

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E Ort Wert : Type} (G : Graph E Ort Wert)

/-- The location of an event. -/
def ort (a : E) : Ort := (G.lab a).ort

/-- The mode of an event (the mode of its location's declaration). -/
def modus (a : E) : Modus := (G.lab a).modus

/-- The event reads (a read or an update). -/
def liest (a : E) : Prop := (G.lab a).art.liest

/-- The event writes (a write or an update). -/
def schreibt (a : E) : Prop := (G.lab a).art.schreibt

/-- The event is an update (read-modify-write). -/
def istRmw (a : E) : Prop := (G.lab a).art = .rmw

/-- **The shape of an execution graph.** `po` a strict order; `rf` from a write to a read of the
    same location carrying the written value, at most one source per read; `mo` a strict total
    order on the writes of each location. -/
structure Wohlgeformt : Prop where
  po_trans : ∀ a b c, G.po a b → G.po b c → G.po a c
  po_irrefl : ∀ a, ¬ G.po a a
  rf_schreibt : ∀ w r, G.rf w r → G.schreibt w
  rf_liest : ∀ w r, G.rf w r → G.liest r
  rf_ort : ∀ w r, G.rf w r → G.ort w = G.ort r
  rf_wert : ∀ w r, G.rf w r → (G.lab w).geschrieben = (G.lab r).gelesen
  rf_eindeutig : ∀ w w' r, G.rf w r → G.rf w' r → w = w'
  mo_schreibt : ∀ a b, G.mo a b → G.schreibt a ∧ G.schreibt b
  mo_ort : ∀ a b, G.mo a b → G.ort a = G.ort b
  mo_trans : ∀ a b c, G.mo a b → G.mo b c → G.mo a c
  mo_irrefl : ∀ a, ¬ G.mo a a
  mo_total : ∀ a b, G.schreibt a → G.schreibt b → G.ort a = G.ort b → a ≠ b → G.mo a b ∨ G.mo b a

/-- **Reads-before** (RC11's `rb = rf⁻¹ ; mo \ id`): `r` reads a write that `w` follows in `mo`. -/
def rb (r w : E) : Prop := ∃ w', G.rf w' r ∧ G.mo w' w ∧ r ≠ w

/-- One step of the extended coherence order. -/
def ecoSchritt (a b : E) : Prop := G.rf a b ∨ G.mo a b ∨ G.rb a b

/-- **Extended coherence order** `eco = (rf ∪ mo ∪ rb)⁺`. -/
def eco (a b : E) : Prop := Relation.TransGen G.ecoSchritt a b

/-- **Release sequence** (RC11's `rs = [W] ; po|loc? ; [W ⊒ rlx] ; (rf ; rmw)*`): the writes that
    carry the release of `w`. -/
inductive Rs : E → E → Prop
  | selbst {w : E} : G.schreibt w → Rs w w
  | po {w x : E} : G.schreibt w → G.po w x → G.schreibt x → G.ort x = G.ort w →
      (G.modus x).atomar → Rs w x
  | rmw {w x u : E} : Rs w x → G.rf x u → G.istRmw u → Rs w u

/-- **Synchronises-with** (fence-free RC11: `[W ⊒ rel] ; rs ; rf ; [R ⊒ acq]`). -/
def sw (a b : E) : Prop :=
  G.schreibt a ∧ (G.modus a).stark ∧ G.liest b ∧ (G.modus b).stark ∧ ∃ x, G.Rs a x ∧ G.rf x b

/-- One step of happens-before. -/
def hbSchritt (a b : E) : Prop := G.po a b ∨ G.sw a b

/-- **Happens-before** `hb = (po ∪ sw)⁺`. -/
def hb (a b : E) : Prop := Relation.TransGen G.hbSchritt a b

/-- **The SC base** (fence-free RC11):
    `scb = po ∪ po|≠loc ; hb ; po|≠loc ∪ hb|loc ∪ mo ∪ rb`. -/
def scb (a b : E) : Prop :=
  G.po a b
    ∨ (∃ c d, G.po a c ∧ G.ort a ≠ G.ort c ∧ G.hb c d ∧ G.po d b ∧ G.ort d ≠ G.ort b)
    ∨ (G.hb a b ∧ G.ort a = G.ort b)
    ∨ G.mo a b
    ∨ G.rb a b

/-- The event is a `seq_cst` access. -/
def sc (a : E) : Prop := G.modus a = .sc

/-- The event is a plain (non-atomic) access. -/
def na (a : E) : Prop := G.modus a = .na

/-- **Partial SC relation** (fence-free RC11: `psc = [E_sc] ; scb ; [E_sc]`). -/
def psc (a b : E) : Prop := G.sc a ∧ G.sc b ∧ G.scb a b

/-- One step of `po ∪ rf`, the relation whose acyclicity excludes load buffering. -/
def porf (a b : E) : Prop := G.po a b ∨ G.rf a b

/-! ## Elementary facts -/

theorem hb_trans {a b c : E} (h1 : G.hb a b) (h2 : G.hb b c) : G.hb a c :=
  Relation.TransGen.trans h1 h2

theorem hb_von_po {a b : E} (h : G.po a b) : G.hb a b := .single (Or.inl h)

theorem hb_von_sw {a b : E} (h : G.sw a b) : G.hb a b := .single (Or.inr h)

theorem eco_von_rf {a b : E} (h : G.rf a b) : G.eco a b := .single (Or.inl h)

theorem eco_von_mo {a b : E} (h : G.mo a b) : G.eco a b := .single (Or.inr (Or.inl h))

theorem eco_von_rb {a b : E} (h : G.rb a b) : G.eco a b := .single (Or.inr (Or.inr h))

variable {G}

/-- A release sequence stays at its head's location. -/
theorem Rs.ort_gleich (hw : G.Wohlgeformt) {w x : E} (h : G.Rs w x) : G.ort x = G.ort w := by
  induction h with
  | selbst _ => rfl
  | po _ _ _ ho _ => exact ho
  | rmw _ hrf _ ih => exact (hw.rf_ort _ _ hrf).symm.trans ih

/-- `sw` stays at one location. -/
theorem sw_ort (hw : G.Wohlgeformt) {a b : E} (h : G.sw a b) : G.ort a = G.ort b := by
  obtain ⟨_, _, _, _, x, hrs, hrf⟩ := h
  exact (Rs.ort_gleich hw hrs).symm.trans (hw.rf_ort _ _ hrf)

/-- Reads-before stays at one location. -/
theorem rb_ort (hw : G.Wohlgeformt) {r w : E} (h : G.rb r w) : G.ort r = G.ort w := by
  obtain ⟨w', hrf, hmo, _⟩ := h
  exact (hw.rf_ort _ _ hrf).symm.trans (hw.mo_ort _ _ hmo)

/-- The target of reads-before writes. -/
theorem rb_schreibt (hw : G.Wohlgeformt) {r w : E} (h : G.rb r w) : G.schreibt w := by
  obtain ⟨w', _, hmo, _⟩ := h
  exact (hw.mo_schreibt _ _ hmo).2

/-- The endpoints of `psc` are `seq_cst`. -/
theorem psc_sc_links {a b : E} (h : G.psc a b) : G.sc a := h.1

theorem psc_sc_rechts {a b : E} (h : G.psc a b) : G.sc b := h.2.1

/-- The endpoints of a `psc` path are `seq_cst`. -/
theorem psc_pfad_sc {a b : E} (h : Relation.TransGen G.psc a b) : G.sc a ∧ G.sc b := by
  obtain ⟨_, h1⟩ := transGen_kopf h
  obtain ⟨_, h2⟩ := transGen_ende h
  exact ⟨h1.1, h2.2.1⟩

end Graph

end Gabbro.Core.Speicher
