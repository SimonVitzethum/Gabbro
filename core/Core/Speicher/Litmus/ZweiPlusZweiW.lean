/-
  File:      core/Core/Speicher/Litmus/ZweiPlusZweiW.lean
  Subject:   THE 2+2W catalogue entry: two threads write two locations in opposite order.

  Source: Lahav et al., "Repairing sequential consistency in C/C++11" (PLDI 2017), §3, Fig. 2 and
  the 2+2W variant of [32] quoted there: `x := sc 1; y := sc 2; a := y rlx // 1` in thread 0 and
  `y := sc 1; x := sc 2; b := x rlx // 1` in thread 1; outcome `a = b = 1`. Batty et al. and the
  herd C11 catalogue give the same test; the weak outcome is a store-store reordering.
  Modes: forbidden with `seq_cst` writes (coherence forces `mo wy₂ wy₁` and `mo wx₂ wx₁`, which
  are two SC steps closing an `S` cycle with the two program-order steps); the reads may be
  relaxed, as in the paper. Allowed with relaxed accesses (no `seq_cst` step, hence no SC cycle).
  Expected: FORBIDDEN (both reads see 1) at `seq_cst`; ALLOWED below `seq_cst`. The allowed half
  is non-vacuous: the same shape is exhibited by a consistent, complete relaxed graph.
-/
module

public import Core.Speicher.Trennung
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **2+2W is forbidden with `seq_cst` writes.** Thread 0 writes `wx₁` then `wy₂` and reads `ry`;
    thread 1 writes `wy₁` then `wx₂` and reads `rx`. Both reads see the value 1 (`ry` reads `wy₁`,
    `rx` reads `wx₁`); coherence forces `wy₂` before `wy₁` and `wx₂` before `wx₁` in `mo`. Under
    `seq_cst` the four steps `po wx₁ wy₂`, `mo wy₂ wy₁`, `po wy₁ wx₂`, `mo wx₂ wx₁` close a
    `psc` cycle. Feeds: `Graph.sb_sc_verboten` style, `G.mo ⊆ scb`. -/
def ZweiPlusZweiWScVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧
      ∃ wx₁ wy₂ ry wy₁ wx₂ rx : E,
        G.sc wx₁ ∧ G.sc wy₂ ∧ G.sc wy₁ ∧ G.sc wx₂ ∧
        G.po wx₁ wy₂ ∧ G.po wy₂ ry ∧ G.po wy₁ wx₂ ∧ G.po wx₂ rx ∧
        G.rf wy₁ ry ∧ G.rf wx₁ rx ∧ G.mo wy₂ wy₁ ∧ G.mo wx₂ wx₁

theorem zwei_plus_zwei_w_sc_verboten : ZweiPlusZweiWScVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, wx₁, wy₂, ry, wy₁, wx₂, rx,
    s₁, s₂, s₃, s₄, p₁, p₂, p₃, p₄, f₁, f₂, m₁, m₂⟩
  exact hk.psc wx₁
    ( (.tail (.tail (.tail (.single ⟨s₁, s₂, Or.inl p₁⟩)
        ⟨s₂, s₃, Or.inr (Or.inr (Or.inr (Or.inl m₁)))⟩)
        ⟨s₃, s₄, Or.inl p₃⟩)
        ⟨s₄, s₁, Or.inr (Or.inr (Or.inr (Or.inl m₂)))⟩))

/-- The eight events: the initial writes and, in thread 0, `wx₁; wy₂; ry`, in thread 1,
    `wy₁; wx₂; rx`. -/
inductive Zp2wEv where
  | ix
  | iy
  | wx1
  | wy2
  | ry
  | wy1
  | wx2
  | rx
  deriving DecidableEq, Repr

open Zp2wEv

/-- Location `false` is `x`, `true` is `y`. Thread 0 writes `x := 1`, `y := 2` and reads `y = 1`
    from thread 1's `wy₁`; thread 1 writes `y := 1`, `x := 2` and reads `x = 1` from `wx₁`.
    Every access carries mode `m`. -/
def zp2wLab (m : Modus) : Zp2wEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, m, 0, 0⟩
  | iy => ⟨.schreiben, true, m, 0, 0⟩
  | wx1 => ⟨.schreiben, false, m, 0, 1⟩
  | wy2 => ⟨.schreiben, true, m, 0, 2⟩
  | ry => ⟨.lesen, true, m, 1, 0⟩
  | wy1 => ⟨.schreiben, true, m, 0, 1⟩
  | wx2 => ⟨.schreiben, false, m, 0, 2⟩
  | rx => ⟨.lesen, false, m, 1, 0⟩

abbrev zp2wPo (a b : Zp2wEv) : Prop :=
  (a = ix ∧ b ≠ ix) ∨
  (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨
  (a = wx1 ∧ (b = wy2 ∨ b = ry)) ∨
  (a = wy2 ∧ b = ry) ∨
  (a = wy1 ∧ (b = wx2 ∨ b = rx)) ∨
  (a = wx2 ∧ b = rx)

abbrev zp2wRf (a b : Zp2wEv) : Prop := (a = wy1 ∧ b = ry) ∨ (a = wx1 ∧ b = rx)

abbrev zp2wMo (a b : Zp2wEv) : Prop :=
  (a = ix ∧ (b = wx2 ∨ b = wx1)) ∨ (a = wx2 ∧ b = wx1) ∨
  (a = iy ∧ (b = wy2 ∨ b = wy1)) ∨ (a = wy2 ∧ b = wy1)

/-- The closure of `rf ∪ mo ∪ rb` in this graph. Both reads take a modification-order maximum,
    so there are no `rb` edges. -/
abbrev zp2wEco (a b : Zp2wEv) : Prop :=
  (a = ix ∧ (b = wx2 ∨ b = wx1 ∨ b = rx)) ∨
  (a = wx2 ∧ (b = wx1 ∨ b = rx)) ∨
  (a = wx1 ∧ b = rx) ∨
  (a = iy ∧ (b = wy2 ∨ b = wy1 ∨ b = ry)) ∨
  (a = wy2 ∧ (b = wy1 ∨ b = ry)) ∨
  (a = wy1 ∧ b = ry)

def zp2wRang : Zp2wEv → Nat
  | ix => 0
  | iy => 1
  | wx1 => 2
  | wy1 => 3
  | wy2 => 4
  | wx2 => 5
  | ry => 6
  | rx => 7

def zp2wGraph (m : Modus) : Graph Zp2wEv Bool Nat := ⟨zp2wLab m, zp2wPo, zp2wRf, zp2wMo⟩

abbrev zp2wSchreibt (m : Modus) (a : Zp2wEv) : Prop := (zp2wLab m a).art.schreibt
abbrev zp2wLiest (m : Modus) (a : Zp2wEv) : Prop := (zp2wLab m a).art.liest
abbrev zp2wOrt (m : Modus) (a : Zp2wEv) : Bool := (zp2wLab m a).ort

theorem zp2wPo_trans_und (a b c : Zp2wEv) : (zp2wPo a b ∧ zp2wPo b c) → zp2wPo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem zp2wMo_trans_und (a b c : Zp2wEv) : (zp2wMo a b ∧ zp2wMo b c) → zp2wMo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem zp2wPo_trans (a b c : Zp2wEv) : zp2wPo a b → zp2wPo b c → zp2wPo a c := by
  intro hab hbc
  exact zp2wPo_trans_und a b c ⟨hab, hbc⟩

theorem zp2wMo_trans (a b c : Zp2wEv) : zp2wMo a b → zp2wMo b c → zp2wMo a c := by
  intro hab hbc
  exact zp2wMo_trans_und a b c ⟨hab, hbc⟩

theorem zp2wPo_irrefl (a : Zp2wEv) : ¬ zp2wPo a a := by
  cases a <;> decide

theorem zp2wMo_irrefl (a : Zp2wEv) : ¬ zp2wMo a a := by
  cases a <;> decide

theorem zp2wRf_eindeutig (w w' r : Zp2wEv) : (zp2wRf w r ∧ zp2wRf w' r) → w = w' := by
  cases w <;> cases w' <;> cases r <;> decide

theorem zp2wEco_trans_und (a b c : Zp2wEv) : (zp2wEco a b ∧ zp2wEco b c) → zp2wEco a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem zp2wEco_trans (a b c : Zp2wEv) : zp2wEco a b → zp2wEco b c → zp2wEco a c := by
  intro hab hbc
  exact zp2wEco_trans_und a b c ⟨hab, hbc⟩

theorem zp2wRf_schreibt (m : Modus) (w r : Zp2wEv) (h : zp2wRf w r) : zp2wSchreibt m w := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem zp2wRf_liest (m : Modus) (w r : Zp2wEv) (h : zp2wRf w r) : zp2wLiest m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem zp2wMo_schreibt (m : Modus) (a b : Zp2wEv) (h : zp2wMo a b) :
    zp2wSchreibt m a ∧ zp2wSchreibt m b := by
  rcases h with (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) <;>
    exact ⟨trivial, trivial⟩

theorem zp2wMo_ort (m : Modus) (a b : Zp2wEv) (h : zp2wMo a b) : zp2wOrt m a = zp2wOrt m b := by
  rcases h with (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

theorem zp2wEco_von_rf (a b : Zp2wEv) : zp2wRf a b → zp2wEco a b := by
  cases a <;> cases b <;> decide

theorem zp2wEco_von_mo (a b : Zp2wEv) : zp2wMo a b → zp2wEco a b := by
  cases a <;> cases b <;> decide

theorem zp2wRb_closed (w' r w : Zp2wEv) : (zp2wRf w' r ∧ zp2wMo w' w) → False := by
  cases w' <;> cases r <;> cases w <;> decide

theorem zp2wMo_total (m : Modus) (a b : Zp2wEv)
    (ha : (zp2wGraph m).schreibt a) (hb : (zp2wGraph m).schreibt b)
    (ho : (zp2wGraph m).ort a = (zp2wGraph m).ort b) (hne : a ≠ b) :
    zp2wMo a b ∨ zp2wMo b a := by
  cases a <;> cases b <;>
    first
      | decide
      | exact False.elim ha
      | exact False.elim hb
      | exact False.elim (hne rfl)
      | (simp only [Graph.ort, zp2wGraph, zp2wLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)

theorem zp2w_wf (m : Modus) : (zp2wGraph m).Wohlgeformt where
  po_trans := by
    intro a b c hab hbc
    exact zp2wPo_trans a b c hab hbc
  po_irrefl := zp2wPo_irrefl
  rf_schreibt := by
    intro w r h
    exact zp2wRf_schreibt m w r h
  rf_liest := by
    intro w r h
    exact zp2wRf_liest m w r h
  rf_ort := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_wert := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_eindeutig := by
    intro w w' r h1 h2
    exact zp2wRf_eindeutig w w' r ⟨h1, h2⟩
  mo_schreibt := by
    intro a b h
    exact zp2wMo_schreibt m a b h
  mo_ort := by
    intro a b h
    exact zp2wMo_ort m a b h
  mo_trans := by
    intro a b c hab hbc
    exact zp2wMo_trans a b c hab hbc
  mo_irrefl := zp2wMo_irrefl
  mo_total := by
    intro a b ha hb ho hne
    exact zp2wMo_total m a b ha hb ho hne
  rmw_nicht_na := by
    intro a h
    cases a <;> simp only [Graph.istRmw, zp2wGraph, zp2wLab, reduceCtorEq] at h

theorem zp2w_rb {m : Modus} {r w : Zp2wEv} (h : (zp2wGraph m).rb r w) : False := by
  obtain ⟨w', h1, h2, -⟩ := h
  exact zp2wRb_closed w' r w ⟨h1, h2⟩

theorem zp2w_eco_schritt {m : Modus} {a b : Zp2wEv} (h : (zp2wGraph m).ecoSchritt a b) :
    zp2wEco a b := by
  rcases h with h | h | h
  · exact zp2wEco_von_rf a b h
  · exact zp2wEco_von_mo a b h
  · exact False.elim (zp2w_rb h)

theorem zp2w_eco {m : Modus} {a b : Zp2wEv} (h : (zp2wGraph m).eco a b) : zp2wEco a b :=
  transGen_von_trans zp2wEco_trans (transGen_mono (fun _ _ h => zp2w_eco_schritt h) h)

theorem zp2w_kein_rmw (m : Modus) (u : Zp2wEv) : ¬ (zp2wGraph m).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, zp2wGraph, zp2wLab, reduceCtorEq] at hu

/-- With relaxed accesses there is no synchronises-with edge, so happens-before is program order. -/
theorem zp2w_hb_rlx {a b : Zp2wEv} (h : (zp2wGraph .rlx).hb a b) : zp2wPo a b := by
  have schritt : ∀ x y, (zp2wGraph .rlx).hbSchritt x y → zp2wPo x y := by
    intro x y hxy
    rcases hxy with hpo | hsw
    · exact hpo
    · obtain ⟨_, hmw, _, _, _, _, _⟩ := hsw
      cases x <;> cases hmw
  exact transGen_von_trans zp2wPo_trans (transGen_mono schritt h)

theorem zp2wRang_porf (a b : Zp2wEv) : zp2wPo a b ∨ zp2wRf a b → zp2wRang a < zp2wRang b := by
  cases a <;> cases b <;> decide

theorem zp2w_kein_sc (e : Zp2wEv) : ¬ (zp2wGraph .rlx).sc e := by
  cases e <;> simp only [Graph.sc, Graph.modus, zp2wGraph, zp2wLab, reduceCtorEq] <;> trivial

theorem zp2w_konsistent : (zp2wGraph .rlx).Konsistent where
  wf := zp2w_wf .rlx
  hb_irrefl := by
    intro a h
    have hp := zp2w_hb_rlx h
    revert hp
    cases a <;> decide
  kohaerent := by
    intro a b hab he
    have hp := zp2w_hb_rlx hab
    have he' := zp2w_eco he
    revert hp he'
    cases a <;> cases b <;> decide
  atomar := by
    intro w u _ _ hu
    exact absurd hu (zp2w_kein_rmw .rlx u)
  psc := by
    intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    exact (zp2w_kein_sc a) hc.1
  ohneLB := azyklisch_von_rang zp2wRang (zp2wRang_porf)
  liest_vorher := by
    intro w u _ hu
    exact absurd hu (zp2w_kein_rmw .rlx u)

theorem zp2w_vollstaendig : (zp2wGraph .rlx).Vollstaendig := by
  intro r hr
  cases r with
  | ix => exact (hr : False).elim
  | iy => exact (hr : False).elim
  | wx1 => exact (hr : False).elim
  | wy2 => exact (hr : False).elim
  | wx2 => exact (hr : False).elim
  | wy1 => exact (hr : False).elim
  | ry => exact ⟨wy1, Or.inl ⟨rfl, rfl⟩⟩
  | rx => exact ⟨wx1, Or.inr ⟨rfl, rfl⟩⟩

/-- **The weak 2+2W outcome is allowed below `seq_cst`.** Some consistent and complete relaxed
    graph has the same program-order, reads-from and modification-order shape. Feeds:
    `zp2w_konsistent`, `zp2w_vollstaendig`. -/
def ZweiPlusZweiWRlxErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wx₁ wy₂ ry wy₁ wx₂ rx : E,
        G.po wx₁ wy₂ ∧ G.po wy₂ ry ∧ G.po wy₁ wx₂ ∧ G.po wx₂ rx ∧
        G.rf wy₁ ry ∧ G.rf wx₁ rx ∧ G.mo wy₂ wy₁ ∧ G.mo wx₂ wx₁

theorem zwei_plus_zwei_w_rlx_erlaubt : ZweiPlusZweiWRlxErlaubtAussage := by
  have p1 : (zp2wGraph .rlx).po wx1 wy2 := by show zp2wPo wx1 wy2; decide
  have p2 : (zp2wGraph .rlx).po wy2 ry := by show zp2wPo wy2 ry; decide
  have p3 : (zp2wGraph .rlx).po wy1 wx2 := by show zp2wPo wy1 wx2; decide
  have p4 : (zp2wGraph .rlx).po wx2 rx := by show zp2wPo wx2 rx; decide
  have f1 : (zp2wGraph .rlx).rf wy1 ry := by show zp2wRf wy1 ry; decide
  have f2 : (zp2wGraph .rlx).rf wx1 rx := by show zp2wRf wx1 rx; decide
  have m1 : (zp2wGraph .rlx).mo wy2 wy1 := by show zp2wMo wy2 wy1; decide
  have m2 : (zp2wGraph .rlx).mo wx2 wx1 := by show zp2wMo wx2 wx1; decide
  exact ⟨Zp2wEv, Bool, Nat, zp2wGraph .rlx, zp2w_konsistent, zp2w_vollstaendig,
    wx1, wy2, ry, wy1, wx2, rx, p1, p2, p3, p4, f1, f2, m1, m2⟩

/-- **The 2+2W group:** the weak outcome is forbidden with `seq_cst` writes and allowed with
    relaxed accesses. This is the single pin root of the group. -/
def ZweiPlusZweiWLitmusAussage : Prop :=
  ZweiPlusZweiWScVerbotenAussage ∧ ZweiPlusZweiWRlxErlaubtAussage

theorem zwei_plus_zwei_w_litmus : ZweiPlusZweiWLitmusAussage :=
  ⟨zwei_plus_zwei_w_sc_verboten, zwei_plus_zwei_w_rlx_erlaubt⟩

end Gabbro.Core.Speicher
