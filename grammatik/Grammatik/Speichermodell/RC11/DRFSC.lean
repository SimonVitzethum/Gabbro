/-
  File:      Grammatik/Speichermodell/RC11/DRFSC.lean
  Subject:   THE DRF-SC THEOREM of the memory model W (PERFECT-MODEL §8, step S5): an RC11-consistent
             execution whose atomics are all `seq_cst` and which has no data race is sequentially
             consistent (`drf_sc`).

  THE ARGUMENT. Two orders cover every edge of `po ∪ rf ∪ mo ∪ rb`:
  * `hb` -- every `po` edge; every edge between two `seq_cst` events that `sw` carries (`rf`); and
    every edge touching a plain access, because race freedom orders such a conflicting pair by `hb`
    and coherence (`hb ; eco?` irreflexive) fixes the direction to the one of `eco`;
  * `psc⁺` -- every `mo`/`rb` edge between two `seq_cst` events (they are in `scb`).
  Between `seq_cst` events `hb` is inside `psc⁺` (`hb_sc_psc`: an `hb` path is `po` stretches and
  `sw` steps; each `sw` step is `hb|loc`, each `po` stretch between `seq_cst` events is `po`). So a
  cycle of `po ∪ rf ∪ mo ∪ rb` folds into a cycle of `hb` or of `psc⁺` (`Kette`), and both are
  excluded by consistency.
-/
module

public import Grammatik.Speichermodell.RC11.Konsistent

@[expose] public section

namespace Gabbro.Grammatik.Speichermodell.RC11

namespace Graph

variable {E Ort Wert : Type} {G : Graph E Ort Wert}

theorem sc_stark {a : E} (h : G.sc a) : (G.modus a).stark := by
  unfold sc at h
  rw [h]
  exact trivial

/-- With only `seq_cst` atomics, an access of at least release/acquire strength is `seq_cst`. -/
theorem NurSC.sc_von_stark (hn : G.NurSC) {a : E} (h : (G.modus a).stark) : G.sc a := by
  cases hn a with
  | inl hna =>
    unfold na at hna
    rw [hna] at h
    exact False.elim h
  | inr hsc => exact hsc

/-- With only `seq_cst` atomics, an `sw` step is a `psc` step (`hb|loc` between `seq_cst`
    events). -/
theorem sw_psc (hk : G.Konsistent) (hn : G.NurSC) {a b : E} (h : G.sw a b) : G.psc a b :=
  ⟨hn.sc_von_stark h.2.1, hn.sc_von_stark h.2.2.2.1,
    Or.inr (Or.inr (Or.inl ⟨G.hb_von_sw h, sw_ort hk.wf h⟩))⟩

/-- A `po` edge between two `seq_cst` events is a `psc` step. -/
theorem po_psc {a b : E} (ha : G.sc a) (hb : G.sc b) (h : G.po a b) : G.psc a b :=
  ⟨ha, hb, Or.inl h⟩

theorem pfad_verlaengern {r : E → E → Prop} {a c e f : E} (h1 : c = a ∨ Relation.TransGen r a c)
    (h2 : c = e ∨ r c e) (h3 : r e f) : Relation.TransGen r a f := by
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact .single h3
  · exact .tail (.single h2) h3
  · exact .tail h1 h3
  · exact .tail (.tail h1 h2) h3

/-- **The shape of an `hb` path from a `seq_cst` event**: a `psc` path to a last `seq_cst`
    event `c`, then a `po` stretch (or nothing). -/
theorem hb_zerlegung (hk : G.Konsistent) (hn : G.NurSC) {a e : E} (ha : G.sc a) (h : G.hb a e) :
    ∃ c, G.sc c ∧ (c = a ∨ Relation.TransGen G.psc a c) ∧ (c = e ∨ G.po c e) := by
  unfold Graph.hb at h
  induction h with
  | single h1 =>
    cases h1 with
    | inl hpo => exact ⟨a, ha, Or.inl rfl, Or.inr hpo⟩
    | inr hsw =>
      have hp := sw_psc hk hn hsw
      exact ⟨_, hp.2.1, Or.inr (.single hp), Or.inl rfl⟩
  | @tail e f _ h2 ih =>
    obtain ⟨c, hc, hac, hce⟩ := ih
    cases h2 with
    | inl hpo =>
      refine ⟨c, hc, hac, Or.inr ?_⟩
      rcases hce with rfl | hce
      · exact hpo
      · exact hk.wf.po_trans _ _ _ hce hpo
    | inr hsw =>
      have hp := sw_psc hk hn hsw
      have hce' : c = e ∨ G.psc c e := by
        rcases hce with rfl | hce
        · exact Or.inl rfl
        · exact Or.inr (po_psc hc hp.1 hce)
      exact ⟨f, hp.2.1, Or.inr (pfad_verlaengern hac hce' hp), Or.inl rfl⟩

/-- **Between `seq_cst` events `hb` is inside `psc⁺`** (only `seq_cst` atomics). -/
theorem hb_sc_psc (hk : G.Konsistent) (hn : G.NurSC) {a b : E} (ha : G.sc a) (hb : G.sc b)
    (h : G.hb a b) : Relation.TransGen G.psc a b := by
  obtain ⟨c, hc, hac, hcb⟩ := hb_zerlegung hk hn ha h
  rcases hcb with rfl | hcb
  · rcases hac with rfl | hac
    · exact absurd h (hk.hb_irrefl _)
    · exact hac
  · have hp := po_psc hc hb hcb
    rcases hac with rfl | hac
    · exact .single hp
    · exact .tail hac hp

/-- **Every edge of `po ∪ rf ∪ mo ∪ rb` is in `hb` or in `psc⁺`** (consistent, only `seq_cst`
    atomics, race-free). -/
theorem scSchritt_einbetten (hk : G.Konsistent) (hn : G.NurSC) (hr : G.Rennfrei) {a b : E}
    (h : G.scSchritt a b) : G.hb a b ∨ Relation.TransGen G.psc a b := by
  have wf := hk.wf
  rcases h with hpo | hrf | hmo | hrb
  · exact Or.inl (G.hb_von_po hpo)
  · have hne : a ≠ b := by
      intro e
      subst e
      exact hk.rf_irrefl a hrf
    have hkf : G.Konflikt a b := ⟨hne, wf.rf_ort _ _ hrf, Or.inl (wf.rf_schreibt _ _ hrf)⟩
    rcases hn a with ha | ha <;> rcases hn b with hb | hb
    · exact Or.inl (hk.hb_richtung (G.eco_von_rf hrf) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rf hrf) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rf hrf) (hr a b hkf (Or.inr hb)))
    · exact Or.inl (G.hb_von_sw ⟨wf.rf_schreibt _ _ hrf, sc_stark ha, wf.rf_liest _ _ hrf,
        sc_stark hb, a, .selbst (wf.rf_schreibt _ _ hrf), hrf⟩)
  · have hne : a ≠ b := by
      intro e
      subst e
      exact wf.mo_irrefl a hmo
    have hkf : G.Konflikt a b := ⟨hne, wf.mo_ort _ _ hmo, Or.inl (wf.mo_schreibt _ _ hmo).1⟩
    rcases hn a with ha | ha <;> rcases hn b with hb | hb
    · exact Or.inl (hk.hb_richtung (G.eco_von_mo hmo) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_mo hmo) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_mo hmo) (hr a b hkf (Or.inr hb)))
    · exact Or.inr (.single ⟨ha, hb, Or.inr (Or.inr (Or.inr (Or.inl hmo)))⟩)
  · have hne : a ≠ b := by
      obtain ⟨_, _, _, h⟩ := hrb
      exact h
    have hkf : G.Konflikt a b := ⟨hne, rb_ort wf hrb, Or.inr (rb_schreibt wf hrb)⟩
    rcases hn a with ha | ha <;> rcases hn b with hb | hb
    · exact Or.inl (hk.hb_richtung (G.eco_von_rb hrb) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rb hrb) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rb hrb) (hr a b hkf (Or.inr hb)))
    · exact Or.inr (.single ⟨ha, hb, Or.inr (Or.inr (Or.inr (Or.inr hrb)))⟩)

variable (G) in
/-- The folded order: `hb`, or `hb? ; psc⁺ ; hb?`. -/
def Kette (a b : E) : Prop :=
  G.hb a b ∨ ∃ c d, (c = a ∨ G.hb a c) ∧ Relation.TransGen G.psc c d ∧ (d = b ∨ G.hb d b)

theorem verbinde {x y b : E} (hx : x = b ∨ G.hb x b) (hy : y = b ∨ G.hb b y) :
    x = y ∨ G.hb x y := by
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact Or.inl rfl
  · exact Or.inr hy
  · exact Or.inr hx
  · exact Or.inr (G.hb_trans hx hy)

/-- Two `psc⁺` stretches joined by `hb?` form one (only `seq_cst` atomics). -/
theorem psc_kleben (hk : G.Konsistent) (hn : G.NurSC) {c d c' d' : E}
    (h1 : Relation.TransGen G.psc c d) (hm : d = c' ∨ G.hb d c')
    (h2 : Relation.TransGen G.psc c' d') : Relation.TransGen G.psc c d' := by
  rcases hm with rfl | hm
  · exact h1.trans h2
  · exact h1.trans ((hb_sc_psc hk hn (psc_pfad_sc h1).2 (psc_pfad_sc h2).1 hm).trans h2)

theorem Kette_trans (hk : G.Konsistent) (hn : G.NurSC) {a b e : E} (h1 : G.Kette a b)
    (h2 : G.Kette b e) : G.Kette a e := by
  rcases h1 with h1 | ⟨c, d, hc, hcd, hd⟩ <;> rcases h2 with h2 | ⟨c', d', hc', hcd', hd'⟩
  · exact Or.inl (G.hb_trans h1 h2)
  · refine Or.inr ⟨c', d', Or.inr ?_, hcd', hd'⟩
    rcases hc' with rfl | hc'
    · exact h1
    · exact G.hb_trans h1 hc'
  · refine Or.inr ⟨c, d, hc, hcd, Or.inr ?_⟩
    rcases hd with rfl | hd
    · exact h2
    · exact G.hb_trans hd h2
  · exact Or.inr ⟨c, d', hc, psc_kleben hk hn hcd (verbinde hd hc') hcd', hd'⟩

theorem Kette_irrefl (hk : G.Konsistent) (hn : G.NurSC) (a : E) : ¬ G.Kette a a := by
  rintro (h | ⟨c, d, hc, hcd, hd⟩)
  · exact hk.hb_irrefl a h
  · rcases verbinde hd hc with rfl | hdc
    · exact hk.psc _ hcd
    · exact hk.psc c (hcd.trans (hb_sc_psc hk hn (psc_pfad_sc hcd).2 (psc_pfad_sc hcd).1 hdc))

/-- **DRF-SC.** An RC11-consistent execution (with `po ∪ rf` acyclic) whose atomic accesses are
    all `seq_cst` and in which every conflicting pair with a plain access is ordered by
    happens-before is sequentially consistent: `po ∪ rf ∪ mo ∪ rb` is acyclic. Its reading as one
    interleaving on one memory is `sc_verschraenkung`. -/
theorem drf_sc (hk : G.Konsistent) (hn : G.NurSC) (hr : G.Rennfrei) : G.SCKonsistent := by
  intro a ha
  have hketten : Relation.TransGen G.Kette a a := by
    refine transGen_mono (fun x y hxy => ?_) ha
    rcases scSchritt_einbetten hk hn hr hxy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨x, y, Or.inl rfl, h, Or.inl rfl⟩
  exact Kette_irrefl hk hn a
    (transGen_von_trans (r := G.Kette) (fun _ _ _ h1 h2 => Kette_trans hk hn h1 h2) hketten)

end Graph

end Gabbro.Grammatik.Speichermodell.RC11
