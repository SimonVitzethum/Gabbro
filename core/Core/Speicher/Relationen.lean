/-
  File:      core/Core/Speicher/Relationen.lean
  Subject:   THE AXIOMATIC MEMORY MODEL W, part 2: the shape of a graph (`Wohlgeformt`) and the
              derived relations of RC11 with fences: reads-before `rb`, extended coherence order
              `eco`, release sequences `Rs`, synchronises-with `sw` (with release/acquire fences),
              happens-before `hb`, the SC base `scb` and the partial SC relation `psc` (with
              `seq_cst` fences, `pscBasis` and `pscZaun`; Lahav et al., PLDI 2017, §3).
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

/-- The event is a fence (no access, only order). -/
def istZaun (a : E) : Prop := (G.lab a).art = .zaun

/-- The graph has no fence events. -/
def OhneZaun : Prop := ∀ a, (G.lab a).art ≠ .zaun

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

/-- **Release sequence** (RC11's `rs = [W] ; po|loc? ; [W ⊒ rlx] ; (rf ; rmw)*`, with
    single-event updates: the `rmw` step stays at the update, which is itself atomic): the writes
    that carry the release of `w`. -/
inductive Rs : E → E → Prop
  | selbst {w : E} : G.schreibt w → (G.modus w).atomar → Rs w w
  | po {w x : E} : G.schreibt w → G.po w x → G.schreibt x → G.ort x = G.ort w →
      (G.modus x).atomar → Rs w x
  | rmw {w x u : E} : Rs w x → G.rf x u → G.istRmw u → Rs w u

/-- **A synchronising fence** (RC11's `F ⊒ rel` on the release side and `F ⊒ acq` on the
    acquire side): with the collapsed modes a fence of at least release/acquire strength plays
    both roles, like `acqrel`. -/
def istSyncZaun (a : E) : Prop := G.istZaun a ∧ (G.modus a).stark

/-- **The head of a synchronisation** (RC11's `[E ⊒ rel] ; ([F] ; po)?`): a release write, or
    a synchronising fence before a write. -/
def FreigabeKopf (a w : E) : Prop :=
  (a = w ∧ G.schreibt a ∧ (G.modus a).stark) ∨
    (G.istSyncZaun a ∧ G.po a w ∧ G.schreibt w)

/-- **The tail of a synchronisation** (RC11's `[R ⊒ acq]`-side `[R] ; (po ; [F])?`): an acquire
    read, or an atomic read before a synchronising fence. -/
def ErwerbSchwanz (r b : E) : Prop :=
  (r = b ∧ G.liest b ∧ (G.modus b).stark) ∨
    (G.liest r ∧ (G.modus r).atomar ∧ G.po r b ∧ G.istSyncZaun b)

/-- **Synchronises-with** (RC11's `[E ⊒ rel] ; ([F] ; po)? ; rs ; rf ; [R] ; (po ; [F])? ;
    [E ⊒ acq]`, Lahav et al., PLDI 2017, §3.2, with single-event updates). -/
def sw (a b : E) : Prop :=
  ∃ w x r : E, G.FreigabeKopf a w ∧ G.Rs w x ∧ G.rf x r ∧ (G.modus r).atomar ∧ G.liest r ∧
    G.ErwerbSchwanz r b

/-- One step of happens-before. -/
def hbSchritt (a b : E) : Prop := G.po a b ∨ G.sw a b

/-- **Happens-before** `hb = (po ∪ sw)⁺`. -/
def hb (a b : E) : Prop := Relation.TransGen G.hbSchritt a b

/-- **The SC base** (RC11's `scb = po ∪ po|≠loc ; hb ; po|≠loc ∪ hb|loc ∪ mo ∪ rb`;
    `hb` already carries the fence synchronisations). -/
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

/-- An `seq_cst` fence (RC11's `F sc`). -/
def istSCZaun (a : E) : Prop := G.istZaun a ∧ G.modus a = .sc

/-- **The SC base with SC fences** (RC11's `psc_base = ([E sc] ∪ [F sc] ; hb?) ; scb ;
    ([E sc] ∪ hb? ; [F sc])`). -/
def pscBasis (a b : E) : Prop :=
  ∃ c d : E, G.scb c d ∧ (G.sc a ∧ a = c ∨ G.istSCZaun a ∧ (a = c ∨ G.hb a c)) ∧
    (G.sc b ∧ d = b ∨ G.istSCZaun b ∧ (d = b ∨ G.hb d b))

/-- **SC fences order through coherence** (RC11's `psc_F = [F sc] ; (hb ∪ hb ; eco ; hb) ;
    [F sc]`). -/
def pscZaun (a b : E) : Prop :=
  G.istSCZaun a ∧ G.istSCZaun b ∧ (G.hb a b ∨ ∃ c d : E, G.hb a c ∧ G.eco c d ∧ G.hb d b)

/-- **Partial SC relation** (RC11's `psc = psc_base ∪ psc_F`). -/
def psc (a b : E) : Prop := G.pscBasis a b ∨ G.pscZaun a b

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
  | selbst _ _ => rfl
  | po _ _ _ ho _ => exact ho
  | rmw _ hrf _ ih => exact (hw.rf_ort _ _ hrf).symm.trans ih

/-- **Without fences a synchronisation is the classic shape**: with no fence at either end the
    release head is a release write and the acquire tail an acquire read. -/
theorem sw_klassisch {a b : E} (ha : ¬ G.istZaun a) (hb : ¬ G.istZaun b) (h : G.sw a b) :
    G.schreibt a ∧ (G.modus a).stark ∧ G.liest b ∧ (G.modus b).stark ∧
      ∃ x, G.Rs a x ∧ G.rf x b := by
  obtain ⟨w, x, r, hkopf, hrs, hrf, _, _, hschwanz⟩ := h
  rcases hkopf with ⟨rfl, hsa, hma⟩ | ⟨hza, _, _⟩
  · rcases hschwanz with ⟨rfl, hlb, hmb⟩ | ⟨_, _, _, hz⟩
    · exact ⟨hsa, hma, hlb, hmb, x, hrs, hrf⟩
    · exact absurd hz.1 hb
  · exact absurd hza.1 ha

/-- The classic shape synchronises. -/
theorem sw_von_klassisch {a b : E}
    (h : G.schreibt a ∧ (G.modus a).stark ∧ G.liest b ∧ (G.modus b).stark ∧
      ∃ x, G.Rs a x ∧ G.rf x b) : G.sw a b := by
  obtain ⟨hsa, hma, hlb, hmb, x, hrs, hrf⟩ := h
  exact ⟨a, x, b, Or.inl ⟨rfl, hsa, hma⟩, hrs, hrf, Modus.stark_atomar hmb, hlb,
    Or.inl ⟨rfl, hlb, hmb⟩⟩

/-- The classic shape stays at one location. -/
theorem sw_klassisch_ort (hw : G.Wohlgeformt) {a b : E}
    (h : G.schreibt a ∧ (G.modus a).stark ∧ G.liest b ∧ (G.modus b).stark ∧
      ∃ x, G.Rs a x ∧ G.rf x b) : G.ort a = G.ort b := by
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

/-- The endpoints of `psc` are `seq_cst` (an `seq_cst` fence has `seq_cst` mode). -/
theorem psc_sc_links {a b : E} (h : G.psc a b) : G.sc a := by
  rcases h with ⟨_, _, _, hl, _⟩ | ⟨hza, _, _⟩
  · rcases hl with ⟨hsc, _⟩ | ⟨hza, _⟩
    · exact hsc
    · exact hza.2
  · exact hza.2

theorem psc_sc_rechts {a b : E} (h : G.psc a b) : G.sc b := by
  rcases h with ⟨_, _, _, _, hr⟩ | ⟨_, hzb, _⟩
  · rcases hr with ⟨hsc, _⟩ | ⟨hzb, _⟩
    · exact hsc
    · exact hzb.2
  · exact hzb.2

/-- **Without fences `psc` is the classic shape**: with no fence at either end both ends are
    `seq_cst` accesses related by the SC base. -/
theorem psc_klassisch {a b : E} (ha : ¬ G.istZaun a) (hb : ¬ G.istZaun b) (h : G.psc a b) :
    G.sc a ∧ G.sc b ∧ G.scb a b := by
  rcases h with ⟨c, d, hscb, hl, hr⟩ | ⟨hza, _, _⟩
  · rcases hl with ⟨hsa, rfl⟩ | ⟨hza, _⟩
    · rcases hr with ⟨hsb, rfl⟩ | ⟨hzb, _⟩
      · exact ⟨hsa, hsb, hscb⟩
      · exact absurd hzb.1 hb
    · exact absurd hza.1 ha
  · exact absurd hza.1 ha

/-- The classic shape is a `psc` step. -/
theorem psc_von_klassisch {a b : E} (h : G.sc a ∧ G.sc b ∧ G.scb a b) : G.psc a b := by
  obtain ⟨hsa, hsb, hscb⟩ := h
  exact Or.inl ⟨a, b, hscb, Or.inl ⟨hsa, rfl⟩, Or.inl ⟨hsb, rfl⟩⟩

/-- The endpoints of a `psc` path are `seq_cst`. -/
theorem psc_pfad_sc {a b : E} (h : Relation.TransGen G.psc a b) : G.sc a ∧ G.sc b := by
  obtain ⟨_, h1⟩ := transGen_kopf h
  obtain ⟨_, h2⟩ := transGen_ende h
  exact ⟨psc_sc_links h1, psc_sc_rechts h2⟩

end Graph

end Gabbro.Core.Speicher
