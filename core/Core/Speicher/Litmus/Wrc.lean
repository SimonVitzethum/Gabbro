/-
  File:      core/Core/Speicher/Litmus/Wrc.lean
  Subject:   WRITE-READ CAUSALITY (WRC) catalogue entry: the three-thread shape
             `x := 1 ‖ r1 := x; y := 1 ‖ r2 := y; r3 := x` with `r1 = 1`, `r2 = 1` and `r3 = 0`
             (the last read misses the first thread's write of `x`).

  Source: Lahav et al., "Repairing Sequential Consistency in C/C++11" (PLDI 2017), the WRC
  ("causality") test; the same shape appears in Batty et al. and in the herd C11 catalogue. The
  Gabbro fragment has no fence form and no dependencies: the order of an access is the mode of its
  location, so the forwarding flag carries the synchronisation by being release/acquire.
  Modes: forbidden when every access is at least release/acquire (`.ra` or `.sc`, i.e. `stark`);
  allowed with relaxed (`.rlx`, likewise `.na` off a data race), where no `sw` edge exists.
  Expected: FORBIDDEN for `stark`, ALLOWED for `.rlx`. The forbidden half holds over every
  consistent graph; the allowed half exhibits one complete graph. The result agrees with the
  literature; no model deviation was found.
-/
module

public import Core.Speicher.Trennung
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E Ort Wert : Type} {G : Graph E Ort Wert}

/-- **Write-read causality is forbidden with release/acquire or stronger.** A write `wx` of one
    location is read by `r1`, whose program-order successor `wy` writes a forwarding location;
    `r2` reads that write and its program-order successor `r3` reads before `wx` in `rb`. With
    `stark` modes the two `rf` edges are `sw` edges, so `hb` chains `wx` to `r3`, and coherence
    rejects the backward `eco` edge. -/
theorem wrc_stark_verboten (hk : G.Konsistent) {wx r1 wy r2 r3 : E}
    (hs : ∀ a, (G.modus a).stark)
    (f1 : G.rf wx r1) (p1 : G.po r1 wy) (f2 : G.rf wy r2) (p2 : G.po r2 r3)
    (rb : G.rb r3 wx) : False := by
  have hs1 : G.sw wx r1 := by
    refine ⟨hk.wf.rf_schreibt _ _ f1, hs wx, hk.wf.rf_liest _ _ f1, hs r1, wx, ?_, f1⟩
    exact Rs.selbst (hk.wf.rf_schreibt _ _ f1)
  have hs2 : G.sw wy r2 := by
    refine ⟨hk.wf.rf_schreibt _ _ f2, hs wy, hk.wf.rf_liest _ _ f2, hs r2, wy, ?_, f2⟩
    exact Rs.selbst (hk.wf.rf_schreibt _ _ f2)
  have hb : G.hb wx r3 :=
    G.hb_trans (G.hb_trans (G.hb_trans (G.hb_von_sw hs1) (G.hb_von_po p1))
      (G.hb_von_sw hs2)) (G.hb_von_po p2)
  exact hk.kohaerent wx r3 hb (G.eco_von_rb rb)

end Graph

/-- The seven events: initial writes `ix`, `iy`, the first write `wx`, the forwarding thread
    `r1; wy` and the receiving thread `r2; r3`. -/
inductive WrcEv where
  | ix | iy | wx | r1 | wy | r2 | r3
  deriving DecidableEq, Repr

open WrcEv

/-- Location `false` is `x`, `true` is `y`. `wx` writes `x := 1`, `r1` reads it; `wy` writes
    `y := 1`, `r2` reads it; `r3` reads the initial `x := 0`. All accesses carry the mode `m`. -/
def wrcLab (m : Modus) : WrcEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, m, 0, 0⟩
  | iy => ⟨.schreiben, true, m, 0, 0⟩
  | wx => ⟨.schreiben, false, m, 0, 1⟩
  | r1 => ⟨.lesen, false, m, 1, 0⟩
  | wy => ⟨.schreiben, true, m, 0, 1⟩
  | r2 => ⟨.lesen, true, m, 1, 0⟩
  | r3 => ⟨.lesen, false, m, 0, 0⟩

abbrev wrcPo (a b : WrcEv) : Prop :=
  (a = ix ∧ b ≠ ix) ∨ (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨
    (a = r1 ∧ b = wy) ∨ (a = r2 ∧ b = r3)

abbrev wrcRf (a b : WrcEv) : Prop :=
  (a = wx ∧ b = r1) ∨ (a = wy ∧ b = r2) ∨ (a = ix ∧ b = r3)

abbrev wrcMo (a b : WrcEv) : Prop := (a = ix ∧ b = wx) ∨ (a = iy ∧ b = wy)

/-- The transitive closure of `rf ∪ mo ∪ rb` in this graph. -/
abbrev wrcEco (a b : WrcEv) : Prop :=
  (a = ix ∧ (b = wx ∨ b = r3 ∨ b = r1)) ∨ (a = wx ∧ b = r1) ∨
    (a = r3 ∧ (b = wx ∨ b = r1)) ∨ (a = iy ∧ (b = wy ∨ b = r2)) ∨ (a = wy ∧ b = r2)

/-- A rank that every `po` and `rf` step raises. -/
def wrcRang : WrcEv → Nat
  | ix => 0
  | iy => 1
  | wx => 2
  | r1 => 3
  | wy => 4
  | r2 => 5
  | r3 => 6

def wrcGraph (m : Modus) : Graph WrcEv Bool Nat := ⟨wrcLab m, wrcPo, wrcRf, wrcMo⟩

abbrev wrcSchreibt (m : Modus) (a : WrcEv) : Prop := (wrcLab m a).art.schreibt
abbrev wrcLiest (m : Modus) (a : WrcEv) : Prop := (wrcLab m a).art.liest
abbrev wrcOrt (m : Modus) (a : WrcEv) : Bool := (wrcLab m a).ort

theorem wrcPo_trans (a b c : WrcEv) : (wrcPo a b ∧ wrcPo b c) → wrcPo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem wrcMo_trans (a b c : WrcEv) : (wrcMo a b ∧ wrcMo b c) → wrcMo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem wrcEco_trans (a b c : WrcEv) : (wrcEco a b ∧ wrcEco b c) → wrcEco a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem wrcRf_schreibt (m : Modus) (w r : WrcEv) (h : wrcRf w r) : wrcSchreibt m w := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem wrcRf_liest (m : Modus) (w r : WrcEv) (h : wrcRf w r) : wrcLiest m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem wrcRf_ort (m : Modus) (w r : WrcEv) (h : wrcRf w r) : wrcOrt m w = wrcOrt m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem wrcRf_wert (m : Modus) (w r : WrcEv) (h : wrcRf w r) :
    (wrcLab m w).geschrieben = (wrcLab m r).gelesen := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem wrcRf_eindeutig (w w' r : WrcEv) : (wrcRf w r ∧ wrcRf w' r) → w = w' := by
  cases w <;> cases w' <;> cases r <;> decide

theorem wrcMo_schreibt (m : Modus) (a b : WrcEv) (h : wrcMo a b) :
    wrcSchreibt m a ∧ wrcSchreibt m b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨trivial, trivial⟩

theorem wrcMo_ort (m : Modus) (a b : WrcEv) (h : wrcMo a b) : wrcOrt m a = wrcOrt m b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem wrcMo_total (m : Modus) (a b : WrcEv) (ha : wrcSchreibt m a) (hb : wrcSchreibt m b)
    (ho : wrcOrt m a = wrcOrt m b) (hne : a ≠ b) : wrcMo a b ∨ wrcMo b a := by
  cases a <;> cases b <;>
    first
      | exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      | exact False.elim ha
      | exact False.elim hb
      | exact False.elim (hne rfl)
      | (simp only [wrcOrt, wrcLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)

theorem wrc_wf (m : Modus) : (wrcGraph m).Wohlgeformt where
  po_trans := by
    intro a b c hab hbc
    exact wrcPo_trans a b c ⟨hab, hbc⟩
  po_irrefl := by
    intro a
    show ¬ wrcPo a a
    cases a <;> decide
  rf_schreibt := by intro w r h; exact wrcRf_schreibt m w r h
  rf_liest := by intro w r h; exact wrcRf_liest m w r h
  rf_ort := by intro w r h; exact wrcRf_ort m w r h
  rf_wert := by intro w r h; exact wrcRf_wert m w r h
  rf_eindeutig := by
    intro w w' r h1 h2
    exact wrcRf_eindeutig w w' r ⟨h1, h2⟩
  mo_schreibt := by intro a b h; exact wrcMo_schreibt m a b h
  mo_ort := by intro a b h; exact wrcMo_ort m a b h
  mo_trans := by
    intro a b c hab hbc
    exact wrcMo_trans a b c ⟨hab, hbc⟩
  mo_irrefl := by
    intro a
    show ¬ wrcMo a a
    cases a <;> decide
  mo_total := by intro a b ha hb ho hne; exact wrcMo_total m a b ha hb ho hne

theorem wrc_kein_rmw (m : Modus) (u : WrcEv) : ¬ (wrcGraph m).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, wrcGraph, wrcLab, reduceCtorEq] at hu

theorem wrc_rb {m : Modus} {r w : WrcEv} (h : (wrcGraph m).rb r w) : r = r3 ∧ w = wx := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show wrcRf w' r → wrcMo w' w → _
  cases w' <;> cases r <;> cases w <;> decide

theorem wrc_eco_schritt {m : Modus} {a b : WrcEv} (h : (wrcGraph m).ecoSchritt a b) : wrcEco a b := by
  rcases h with h | h | h
  · revert h
    show wrcRf a b → wrcEco a b
    cases a <;> cases b <;> decide
  · revert h
    show wrcMo a b → wrcEco a b
    cases a <;> cases b <;> decide
  · rcases wrc_rb h with ⟨rfl, rfl⟩ <;> decide

theorem wrc_eco {m : Modus} {a b : WrcEv} (h : (wrcGraph m).eco a b) : wrcEco a b :=
  transGen_von_trans (fun x y z hxy hyz => wrcEco_trans x y z ⟨hxy, hyz⟩)
    (transGen_mono (fun _ _ h => wrc_eco_schritt h) h)

theorem wrc_modus (m : Modus) (a : WrcEv) : (wrcGraph m).modus a = m := by
  cases a <;> rfl

/-- With a non-synchronising mode no `sw` edge exists, so `hb` is contained in `po`. -/
theorem wrc_hb (m : Modus) (hm : ¬ m.stark) {a b : WrcEv} (h : (wrcGraph m).hb a b) : wrcPo a b := by
  have hs : ∀ x y, (wrcGraph m).hbSchritt x y → wrcPo x y := by
    intro x y hxy
    rcases hxy with hpo | hsw
    · exact hpo
    · have hst : ((wrcGraph m).modus x).stark := Graph.sw_stark_links hsw
      rw [wrc_modus m x] at hst
      exact False.elim (hm hst)
  exact transGen_von_trans (fun x y z hxy hyz => wrcPo_trans x y z ⟨hxy, hyz⟩)
    (transGen_mono hs h)

theorem wrc_kein_sc (m : Modus) (hm : ¬ m.stark) (a : WrcEv) : ¬ (wrcGraph m).sc a := by
  have hmsc : m ≠ .sc := by
    intro h
    subst h
    exact hm trivial
  cases a <;> simp only [Graph.sc, Graph.modus, wrcGraph, wrcLab, reduceCtorEq] <;> exact hmsc

/-- The outcome's shape in the small graph, independent of the mode. -/
theorem wrc_shape (m : Modus) :
    (wrcGraph m).rf wx r1 ∧ (wrcGraph m).po r1 wy ∧ (wrcGraph m).rf wy r2 ∧
      (wrcGraph m).po r2 r3 ∧ (wrcGraph m).rb r3 wx := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact ⟨ix, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩, by decide⟩

/-- **The WRC outcome is consistent in every non-synchronising mode.** Feeds: closed-form
    well-formedness, coherence, empty `psc`, empty atomicity obligations, rank for `ohneLB`. -/
theorem wrc_ohne_stark_erlaubt (m : Modus) (hm : ¬ m.stark) :
    (wrcGraph m).Konsistent ∧ (wrcGraph m).rf wx r1 ∧ (wrcGraph m).po r1 wy ∧
      (wrcGraph m).rf wy r2 ∧ (wrcGraph m).po r2 r3 ∧ (wrcGraph m).rb r3 wx := by
  refine ⟨⟨wrc_wf m, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro a h
    have hp := wrc_hb m hm h
    revert hp
    cases a <;> decide
  · intro a b hab he
    have hp := wrc_hb m hm hab
    have he' := wrc_eco he
    revert hp he'
    cases a <;> cases b <;> decide
  · intro w u _ _ hu
    exact absurd hu (wrc_kein_rmw m u)
  · intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    exact wrc_kein_sc m hm a hc.1
  · refine azyklisch_von_rang wrcRang ?_
    intro a b
    show wrcPo a b ∨ wrcRf a b → wrcRang a < wrcRang b
    cases a <;> cases b <;> decide
  · intro w u _ hu
    exact absurd hu (wrc_kein_rmw m u)
  · exact (wrc_shape m).1
  · exact (wrc_shape m).2.1
  · exact (wrc_shape m).2.2.1
  · exact (wrc_shape m).2.2.2.1
  · exact (wrc_shape m).2.2.2.2

theorem wrc_vollstaendig (m : Modus) : (wrcGraph m).Vollstaendig := by
  intro r hr
  cases r with
  | ix => exact (hr : False).elim
  | iy => exact (hr : False).elim
  | wx => exact (hr : False).elim
  | r1 => exact ⟨wx, Or.inl ⟨rfl, rfl⟩⟩
  | wy => exact (hr : False).elim
  | r2 => exact ⟨wy, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | r3 => exact ⟨ix, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- **Forbidden WRC.** No consistent graph with every access `stark` has the shape. -/
def WrcStarkVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ (∀ a, (G.modus a).stark) ∧
      ∃ wx r1 wy r2 r3 : E,
        G.rf wx r1 ∧ G.po r1 wy ∧ G.rf wy r2 ∧ G.po r2 r3 ∧ G.rb r3 wx

/-- **Allowed WRC.** Some consistent and complete graph (all `.rlx`) has the shape. -/
def WrcRlxErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wx r1 wy r2 r3 : E,
        G.rf wx r1 ∧ G.po r1 wy ∧ G.rf wy r2 ∧ G.po r2 r3 ∧ G.rb r3 wx

/-- **The pinned WRC group root.** -/
def WrcLitmusAussage : Prop := WrcStarkVerbotenAussage ∧ WrcRlxErlaubtAussage

theorem wrc_stark_verboten_kat : WrcStarkVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, hs, wx, r1, wy, r2, r3, f1, p1, f2, p2, rb⟩
  exact Graph.wrc_stark_verboten hk hs f1 p1 f2 p2 rb

theorem wrc_rlx_erlaubt_kat : WrcRlxErlaubtAussage := by
  obtain ⟨hk, f1, p1, f2, p2, rb⟩ := wrc_ohne_stark_erlaubt .rlx (by intro h; cases h)
  exact ⟨WrcEv, Bool, Nat, wrcGraph .rlx, hk, wrc_vollstaendig .rlx,
    wx, r1, wy, r2, r3, f1, p1, f2, p2, rb⟩

theorem wrc_litmus : WrcLitmusAussage := ⟨wrc_stark_verboten_kat, wrc_rlx_erlaubt_kat⟩

/-- Non-vacuity of the forbidden half: the same shape with `.ra` is not consistent. -/
theorem wrc_stark_inkonsistent : ¬ (wrcGraph .ra).Konsistent := by
  intro hk
  obtain ⟨f1, p1, f2, p2, rb⟩ := wrc_shape .ra
  exact Graph.wrc_stark_verboten hk (by intro a; cases a <;> trivial) f1 p1 f2 p2 rb

end Gabbro.Core.Speicher
