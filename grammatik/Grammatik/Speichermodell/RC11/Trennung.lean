/-
  File:      Grammatik/Speichermodell/RC11/Trennung.lean
  Subject:   `seq_cst` IS NO LONGER RELEASE/ACQUIRE: the store-buffering graph (both reads read the
             initial value) is consistent in every mode except `seq_cst` (`sb_ohne_sc_erlaubt`) and
             inconsistent with `seq_cst` (`sb_sc_inkonsistent`, from `sb_sc_verboten`). The first
             statement is also the satisfiability lemma of `Konsistent` with a non-SC outcome
             (`konsistent_erfuellbar`).
-/
module

public import Grammatik.Speichermodell.RC11.Litmus

@[expose] public section

namespace Gabbro.Grammatik.Speichermodell.RC11

namespace Graph

variable {E Ort Wert : Type} {G : Graph E Ort Wert}

/-- Without updates a release sequence is its head or a `po` successor. -/
theorem Rs.ohne_rmw (hr : ∀ u, ¬ G.istRmw u) {a x : E} (h : G.Rs a x) : a = x ∨ G.po a x := by
  induction h with
  | selbst _ => exact Or.inl rfl
  | po _ hpo _ _ _ => exact Or.inr hpo
  | rmw _ _ hu _ => exact absurd hu (hr _)

/-- Without updates, `sw` ends at an `rf` edge from the head or a `po` successor of it. -/
theorem sw_ohne_rmw (hr : ∀ u, ¬ G.istRmw u) {a b : E} (h : G.sw a b) :
    ∃ x, (a = x ∨ G.po a x) ∧ G.rf x b := by
  obtain ⟨_, _, _, _, x, hrs, hrf⟩ := h
  exact ⟨x, Rs.ohne_rmw hr hrs, hrf⟩

/-- Without updates and with every `rf` edge inside `po`, happens-before is program order. -/
theorem hb_in_po (hw : G.Wohlgeformt) (hr : ∀ u, ¬ G.istRmw u)
    (hrf : ∀ x b, G.rf x b → G.po x b) {a b : E} (h : G.hb a b) : G.po a b := by
  have schritt : ∀ x y, G.hbSchritt x y → G.po x y := by
    intro x y hxy
    rcases hxy with hpo | hsw
    · exact hpo
    · obtain ⟨z, hz, hzy⟩ := sw_ohne_rmw hr hsw
      rcases hz with rfl | hz
      · exact hrf _ _ hzy
      · exact hw.po_trans _ _ _ hz (hrf _ _ hzy)
  exact transGen_von_trans hw.po_trans (transGen_mono schritt h)

end Graph

/-! ## The store-buffering graph -/

/-- The events: the two initial writes and the two threads `a₁; b₁` and `a₂; b₂`. -/
inductive SbEv where
  | ix
  | iy
  | a1
  | b1
  | a2
  | b2
  deriving DecidableEq, Repr

open SbEv

/-- Location `false` is `x`, `true` is `y`. Thread 1 writes `x := 1` and reads `y`; thread 2
    writes `y := 1` and reads `x`; both reads return `0`. Every access has mode `m`. -/
def sbLab (m : Modus) : SbEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, m, 0, 0⟩
  | iy => ⟨.schreiben, true, m, 0, 0⟩
  | a1 => ⟨.schreiben, false, m, 0, 1⟩
  | b1 => ⟨.lesen, true, m, 0, 0⟩
  | a2 => ⟨.schreiben, true, m, 0, 1⟩
  | b2 => ⟨.lesen, false, m, 0, 0⟩

@[reducible] def sbPo (a b : SbEv) : Prop :=
  (a = ix ∧ b ≠ ix) ∨ (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨ (a = a1 ∧ b = b1) ∨ (a = a2 ∧ b = b2)

@[reducible] def sbRf (a b : SbEv) : Prop := (a = iy ∧ b = b1) ∨ (a = ix ∧ b = b2)

@[reducible] def sbMo (a b : SbEv) : Prop := (a = ix ∧ b = a1) ∨ (a = iy ∧ b = a2)

/-- The closure of `rf ∪ mo ∪ rb` in this graph. -/
@[reducible] def sbEco (a b : SbEv) : Prop :=
  (a = ix ∧ (b = a1 ∨ b = b2)) ∨ (a = iy ∧ (b = a2 ∨ b = b1)) ∨ (a = b1 ∧ b = a2) ∨
    (a = b2 ∧ b = a1)

def sbRang : SbEv → Nat
  | ix => 0
  | iy => 1
  | a1 => 2
  | a2 => 2
  | b1 => 3
  | b2 => 3

def sbGraph (m : Modus) : Graph SbEv Bool Nat := ⟨sbLab m, sbPo, sbRf, sbMo⟩

theorem sb_wf (m : Modus) : (sbGraph m).Wohlgeformt where
  po_trans := by
    intro a b c
    show sbPo a b → sbPo b c → sbPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ sbPo a a
    cases a <;> decide
  rf_schreibt := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_liest := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_ort := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_wert := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_eindeutig := by
    rintro w w' r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first | exact h1.symm | exact absurd h2 (by decide)
  mo_schreibt := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨trivial, trivial⟩
  mo_ort := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  mo_trans := by
    intro a b c
    show sbMo a b → sbMo b c → sbMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ sbMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    show sbMo a b ∨ sbMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha
        | exact False.elim hb
        | exact absurd rfl hne
        | (simp [Graph.ort, sbGraph, sbLab] at ho)

theorem sb_rb {m : Modus} {r w : SbEv} (h : (sbGraph m).rb r w) :
    (r = b1 ∧ w = a2) ∨ (r = b2 ∧ w = a1) := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show sbRf w' r → sbMo w' w → _
  cases w' <;> cases r <;> cases w <;> decide

theorem sb_eco_schritt {m : Modus} {a b : SbEv} (h : (sbGraph m).ecoSchritt a b) : sbEco a b := by
  rcases h with h | h | h
  · revert h
    show sbRf a b → sbEco a b
    cases a <;> cases b <;> decide
  · revert h
    show sbMo a b → sbEco a b
    cases a <;> cases b <;> decide
  · rcases sb_rb h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem sb_eco {m : Modus} {a b : SbEv} (h : (sbGraph m).eco a b) : sbEco a b := by
  have htr : ∀ x y z, sbEco x y → sbEco y z → sbEco x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  exact transGen_von_trans htr (transGen_mono (fun _ _ h => sb_eco_schritt h) h)

theorem sb_kein_rmw (m : Modus) (u : SbEv) : ¬ (sbGraph m).istRmw u := by
  intro hu
  cases u <;> simp [Graph.istRmw, sbGraph, sbLab] at hu

theorem sb_hb {m : Modus} {a b : SbEv} (h : (sbGraph m).hb a b) : sbPo a b :=
  Graph.hb_in_po (sb_wf m) (sb_kein_rmw m)
    (by
      intro x y
      show sbRf x y → sbPo x y
      cases x <;> cases y <;> decide) h

/-- **The store-buffering outcome is consistent in every mode except `seq_cst`.** -/
theorem sb_ohne_sc_erlaubt (m : Modus) (hm : m ≠ .sc) :
    (sbGraph m).Konsistent ∧ (sbGraph m).po a1 b1 ∧ (sbGraph m).po a2 b2 ∧
      (sbGraph m).rb b1 a2 ∧ (sbGraph m).rb b2 a1 := by
  refine ⟨⟨sb_wf m, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a h
    have := sb_hb h
    revert this
    cases a <;> decide
  · intro a b h1 h2
    have hp := sb_hb h1
    have he := sb_eco h2
    revert hp he
    cases a <;> cases b <;> decide
  · intro w u _ _ hu
    exact absurd hu (sb_kein_rmw m u)
  · intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    have hs := hc.1
    cases a <;> exact hm hs
  · refine azyklisch_von_rang sbRang ?_
    intro a b
    show sbPo a b ∨ sbRf a b → sbRang a < sbRang b
    cases a <;> cases b <;> decide
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact ⟨iy, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, by decide⟩
  · exact ⟨ix, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, by decide⟩

/-- **The same graph with `seq_cst` is inconsistent** (`sb_sc_verboten`): `seq_cst` is truly
    sequentially consistent and strictly stronger than release/acquire. -/
theorem sb_sc_inkonsistent : ¬ (sbGraph .sc).Konsistent := by
  intro hk
  obtain ⟨_, p₁, p₂, r₁, r₂⟩ := sb_ohne_sc_erlaubt .ra (by decide)
  exact Graph.sb_sc_verboten (a₁ := a1) (b₁ := b1) (a₂ := a2) (b₂ := b2) hk rfl rfl rfl rfl
    p₁ p₂ r₁ r₂

/-- **Satisfiability of `Konsistent`** with a non-sequentially-consistent outcome. -/
theorem konsistent_erfuellbar :
    ∃ G : Graph SbEv Bool Nat, G.Konsistent ∧ ¬ G.SCKonsistent := by
  obtain ⟨hk, p₁, p₂, r₁, r₂⟩ := sb_ohne_sc_erlaubt .ra (by decide)
  refine ⟨sbGraph .ra, hk, fun hsc => hsc a1 ?_⟩
  exact .tail (.tail (.tail (.single (Or.inl p₁)) (Or.inr (Or.inr (Or.inr r₁))))
    (Or.inl p₂)) (Or.inr (Or.inr (Or.inr r₂)))

end Gabbro.Grammatik.Speichermodell.RC11
