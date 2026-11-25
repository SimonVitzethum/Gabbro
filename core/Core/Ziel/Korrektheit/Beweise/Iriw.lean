/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Iriw.lean
  Subject:   PROOFS of the two pinned independent-reads statements of the memory layer (M3):
             independent reads of independent writes are forbidden with `seq_cst` and allowed with
             release/acquire. Both proofs stay generic over every consistent graph (forbidden half)
             or exhibit one concrete RC11-consistent graph (allowed half); no fixture is evaluated
             on the compiler path.

   Feeding facts: `Graph.sw_direkt`, `Graph.sc_stark`, `Graph.psc_von_klassisch`, `Graph.rb`,
   `Graph.hb_in_po`, `Graph.hb_irrefl`, `Graph.atomar`, `Konsistent.psc`, `Konsistent.ohneLB`,
   `transGen_von_trans`, `transGen_mono`, `transGen_kopf`, `azyklisch_von_rang`,
   and the closed-form case-split style of `Core/Speicher/Trennung.lean`.
-/
module

public import Core.Ziel.Korrektheit.Speicher
public import Core.Speicher.Kohaerenz

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Speicher

/-- INDEPENDENT READS OF INDEPENDENT WRITES ARE FORBIDDEN UNDER `seq_cst`. Feeds: the
    classic `psc` steps (`Graph.psc_von_klassisch`: the two `rf` edges synchronise through `sw_direkt`
    into `hb|loc`, the `po` and `rb` edges are in `scb`). Proof sketch: the six assumptions are
    six `psc` steps closing `wx → r1x → r1y → wy → r2y → r2x → wx`; a transitive path around
    that loop is a `psc` cycle, which `Konsistent.psc` excludes. -/
theorem iriw_sc_verboten : IriwScVerbotenAussage := by
  intro E Ort Wert G hk hsc wx wy r1x r1y r2y r2x hf1 hp1 hrb1 hf2 hp2 hrb2
  have s1 : G.psc wx r1x := Graph.psc_von_klassisch ⟨hsc wx, hsc r1x, Or.inr (Or.inr (Or.inl
    ⟨G.hb_von_sw (Graph.sw_direkt hk.wf hf1 (Graph.sc_stark (hsc wx)) (Graph.sc_stark (hsc r1x))),
      hk.wf.rf_ort _ _ hf1⟩))⟩
  have s2 : G.psc r1x r1y := Graph.psc_von_klassisch ⟨hsc r1x, hsc r1y, Or.inl hp1⟩
  have s3 : G.psc r1y wy :=
    Graph.psc_von_klassisch ⟨hsc r1y, hsc wy, Or.inr (Or.inr (Or.inr (Or.inr hrb1)))⟩
  have s4 : G.psc wy r2y := Graph.psc_von_klassisch ⟨hsc wy, hsc r2y, Or.inr (Or.inr (Or.inl
    ⟨G.hb_von_sw (Graph.sw_direkt hk.wf hf2 (Graph.sc_stark (hsc wy)) (Graph.sc_stark (hsc r2y))),
      hk.wf.rf_ort _ _ hf2⟩))⟩
  have s5 : G.psc r2y r2x := Graph.psc_von_klassisch ⟨hsc r2y, hsc r2x, Or.inl hp2⟩
  have s6 : G.psc r2x wx :=
    Graph.psc_von_klassisch ⟨hsc r2x, hsc wx, Or.inr (Or.inr (Or.inr (Or.inr hrb2)))⟩
  exact hk.psc wx (((((Relation.TransGen.single s1).tail s2).tail s3).tail s4).tail s5).tail s6

/-- The eight events of the release/acquire IRIW outcome: the initial writes `ix`, `iy`, the two
    release writes `wx`, `wy`, and the acquire readers `r1x; r1y` and `r2y; r2x`. -/
inductive IriwEv where
  | irIX | irIY | irWX | irWY | irR1X | irR1Y | irR2Y | irR2X
  deriving DecidableEq, Repr

open IriwEv

/-- `r1x` reads `x := 1` from `wx` and `r1y` reads the initial `y := 0`; `r2y` reads `y := 1` from
    `wy` and `r2x` reads the initial `x := 0`. Every access carries the mode `m`. -/
def irLab (m : Modus) : IriwEv → Etikett Bool Nat
  | irIX => ⟨.schreiben, false, m, 0, 0⟩
  | irIY => ⟨.schreiben, true, m, 0, 0⟩
  | irWX => ⟨.schreiben, false, m, 0, 1⟩
  | irWY => ⟨.schreiben, true, m, 0, 1⟩
  | irR1X => ⟨.lesen, false, m, 1, 0⟩
  | irR1Y => ⟨.lesen, true, m, 0, 0⟩
  | irR2Y => ⟨.lesen, true, m, 1, 0⟩
  | irR2X => ⟨.lesen, false, m, 0, 0⟩

/-- Program order: the initial writes precede every other event, `wx; r1x; r1y` and `wy; r2y; r2x`
    are the two reader threads (the write of a location is in the same thread as its reader here;
    that only adds order and leaves the IRIW shape intact). -/
abbrev irPo (a b : IriwEv) : Prop :=
  (a = irIX ∧ b ≠ irIX) ∨
  (a = irIY ∧ b ≠ irIX ∧ b ≠ irIY) ∨
  (a = irWX ∧ (b = irR1X ∨ b = irR1Y)) ∨
  (a = irWY ∧ (b = irR2Y ∨ b = irR2X)) ∨
  (a = irR1X ∧ b = irR1Y) ∨
  (a = irR2Y ∧ b = irR2X)

abbrev irRf (a b : IriwEv) : Prop :=
  (a = irWX ∧ b = irR1X) ∨ (a = irIY ∧ b = irR1Y) ∨
  (a = irWY ∧ b = irR2Y) ∨ (a = irIX ∧ b = irR2X)

abbrev irMo (a b : IriwEv) : Prop :=
  (a = irIX ∧ b = irWX) ∨ (a = irIY ∧ b = irWY)

/-- The transitive closure of `rf ∪ mo ∪ rb` in this graph, in closed form. -/
abbrev irEco (a b : IriwEv) : Prop :=
  (a = irIX ∧ (b = irWX ∨ b = irR2X ∨ b = irR1X)) ∨
  (a = irR2X ∧ (b = irWX ∨ b = irR1X)) ∨
  (a = irWX ∧ b = irR1X) ∨
  (a = irIY ∧ (b = irWY ∨ b = irR1Y ∨ b = irR2Y)) ∨
  (a = irR1Y ∧ (b = irWY ∨ b = irR2Y)) ∨
  (a = irWY ∧ b = irR2Y)

/-- A rank that every `po` and `rf` step raises, for `ohneLB`. -/
def irRang : IriwEv → Nat
  | irIX => 0
  | irIY => 1
  | irWX => 2
  | irWY => 3
  | irR1X => 4
  | irR1Y => 5
  | irR2Y => 6
  | irR2X => 7

def irGraph (m : Modus) : Graph IriwEv Bool Nat := ⟨irLab m, irPo, irRf, irMo⟩

theorem irPo_trans (a b c : IriwEv) : (irPo a b ∧ irPo b c) → irPo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem irMo_trans (a b c : IriwEv) : (irMo a b ∧ irMo b c) → irMo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem irEco_trans (a b c : IriwEv) : (irEco a b ∧ irEco b c) → irEco a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem irEco_von_rf (a b : IriwEv) : irRf a b → irEco a b := by
  cases a <;> cases b <;> decide

theorem irEco_von_mo (a b : IriwEv) : irMo a b → irEco a b := by
  cases a <;> cases b <;> decide

theorem irRf_po (a b : IriwEv) : irRf a b → irPo a b := by
  cases a <;> cases b <;> decide

theorem irRf_eindeutig (w w' r : IriwEv) : (irRf w r ∧ irRf w' r) → w = w' := by
  cases w <;> cases w' <;> cases r <;> decide

abbrev irSchreibt (m : Modus) (a : IriwEv) : Prop := (irLab m a).art.schreibt
abbrev irLiest (m : Modus) (a : IriwEv) : Prop := (irLab m a).art.liest
abbrev irOrt (m : Modus) (a : IriwEv) : Bool := (irLab m a).ort
abbrev irGelesen (m : Modus) (a : IriwEv) : Nat := (irLab m a).gelesen
abbrev irGeschrieben (m : Modus) (a : IriwEv) : Nat := (irLab m a).geschrieben

theorem irRf_schreibt (m : Modus) (w r : IriwEv) (h : irRf w r) : irSchreibt m w := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial
theorem irRf_liest (m : Modus) (w r : IriwEv) (h : irRf w r) : irLiest m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial
theorem irRf_ort (m : Modus) (w r : IriwEv) (h : irRf w r) : irOrt m w = irOrt m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
theorem irRf_wert (m : Modus) (w r : IriwEv) (h : irRf w r) : irGeschrieben m w = irGelesen m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
theorem irMo_schreibt (m : Modus) (a b : IriwEv) (h : irMo a b) : irSchreibt m a ∧ irSchreibt m b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨trivial, trivial⟩
theorem irMo_ort (m : Modus) (a b : IriwEv) (h : irMo a b) : irOrt m a = irOrt m b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem irMo_total (m : Modus) (a b : IriwEv) (ha : irSchreibt m a) (hb : irSchreibt m b)
    (ho : irOrt m a = irOrt m b) (hne : a ≠ b) : irMo a b ∨ irMo b a := by
  cases a <;> cases b <;>
    first
      | exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      | exact False.elim ha
      | exact False.elim hb
      | exact False.elim (hne rfl)
      | (simp only [irOrt, irLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)

theorem irRb_closed (w' r w : IriwEv) :
    (irRf w' r ∧ irMo w' w) → (r = irR1Y ∧ w = irWY) ∨ (r = irR2X ∧ w = irWX) := by
  cases w' <;> cases r <;> cases w <;> decide

theorem irKoh (a b : IriwEv) : (irPo a b ∧ irEco b a) → False := by
  cases a <;> cases b <;> decide

theorem ir_wf (m : Modus) : (irGraph m).Wohlgeformt where
  po_trans := by
    intro a b c hab hbc
    exact irPo_trans a b c ⟨hab, hbc⟩
  po_irrefl := by
    intro a
    show ¬ irPo a a
    cases a <;> decide
  rf_schreibt := by
    intro w r h
    exact irRf_schreibt m w r h
  rf_liest := by
    intro w r h
    exact irRf_liest m w r h
  rf_ort := by
    intro w r h
    exact irRf_ort m w r h
  rf_wert := by
    intro w r h
    exact irRf_wert m w r h
  rf_eindeutig := by
    intro w w' r h1 h2
    exact irRf_eindeutig w w' r ⟨h1, h2⟩
  mo_schreibt := by
    intro a b h
    exact irMo_schreibt m a b h
  mo_ort := by
    intro a b h
    exact irMo_ort m a b h
  mo_trans := by
    intro a b c hab hbc
    exact irMo_trans a b c ⟨hab, hbc⟩
  mo_irrefl := by
    intro a
    show ¬ irMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    exact irMo_total m a b ha hb ho hne

theorem ir_kein_rmw (m : Modus) (u : IriwEv) : ¬ (irGraph m).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, irGraph, irLab, reduceCtorEq] at hu

theorem ir_rb {m : Modus} {r w : IriwEv} (h : (irGraph m).rb r w) :
    (r = irR1Y ∧ w = irWY) ∨ (r = irR2X ∧ w = irWX) := by
  obtain ⟨w', h1, h2, _⟩ := h
  exact irRb_closed w' r w ⟨h1, h2⟩

theorem ir_eco_schritt {m : Modus} {a b : IriwEv} (h : (irGraph m).ecoSchritt a b) : irEco a b := by
  rcases h with h | h | h
  · exact irEco_von_rf a b h
  · exact irEco_von_mo a b h
  · rcases ir_rb h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem ir_eco {m : Modus} {a b : IriwEv} (h : (irGraph m).eco a b) : irEco a b := by
  exact transGen_von_trans (fun x y z hxy hyz => irEco_trans x y z ⟨hxy, hyz⟩)
    (transGen_mono (fun _ _ h => ir_eco_schritt h) h)

theorem ir_kein_zaun (m : Modus) (a : IriwEv) : ¬ (irGraph m).istZaun a := by
  intro hu
  cases a <;> simp only [Graph.istZaun, irGraph, irLab, reduceCtorEq] at hu

/-- Every `rf` edge lies inside program order here, so `hb_in_po` describes `hb` by `irPo`. -/
theorem ir_hb {m : Modus} {a b : IriwEv} (h : (irGraph m).hb a b) : irPo a b :=
  Graph.hb_in_po (ir_wf m) (ir_kein_zaun m) (ir_kein_rmw m) irRf_po h

theorem ir_kein_sc (e : IriwEv) : ¬ (irGraph .ra).sc e := by
  cases e <;> simp only [Graph.sc, Graph.modus, irGraph, irLab, reduceCtorEq] <;> trivial

theorem ir_konsistent : (irGraph .ra).Konsistent where
  wf := ir_wf .ra
  hb_irrefl := by
    intro a h
    have hp := ir_hb h
    revert hp
    cases a <;> decide
  kohaerent := by
    intro a b hab he
    exact irKoh a b ⟨ir_hb hab, ir_eco he⟩
  atomar := by
    intro w u _ _ hu
    exact absurd hu (ir_kein_rmw .ra u)
  psc := by
    intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    rcases hc with ⟨_, _, _, hl, _⟩ | ⟨hza, _, _⟩
    · rcases hl with ⟨hsc, _⟩ | ⟨hza, _⟩
      · exact absurd hsc (ir_kein_sc a)
      · exact absurd hza.1 (ir_kein_zaun .ra a)
    · exact absurd hza.1 (ir_kein_zaun .ra a)
  ohneLB := by
    refine azyklisch_von_rang irRang ?_
    intro a b
    show (irPo a b ∨ irRf a b) → irRang a < irRang b
    cases a <;> cases b <;> decide
  liest_vorher := by
    intro w u _ hu
    exact absurd hu (ir_kein_rmw .ra u)

/-- THE SAME SHAPE IS ALLOWED BELOW `seq_cst`. Feeds: `ir_konsistent` (well-formedness, coherence,
    atomicity, empty `psc` and `ohneLB` for the small graph), `hb_in_po`, `transGen_von_trans`,
    `transGen_mono`, `azyklisch_von_rang` (the consistency fields), `Graph.rb` (the two `rb` edges).
    Proof sketch: `irGraph .ra` is RC11-consistent by closed-form case analysis over its eight events;
    its two readers disagree on `x` and `y` exactly as the forbidden `seq_cst` shape requires. -/
theorem iriw_ra_erlaubt : IriwRaErlaubtAussage := by
  have hf1 : (irGraph .ra).rf irWX irR1X := by
    show irRf irWX irR1X
    decide
  have hp1 : (irGraph .ra).po irR1X irR1Y := by
    show irPo irR1X irR1Y
    decide
  have hrb1 : (irGraph .ra).rb irR1Y irWY := by
    exact ⟨irIY, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr ⟨rfl, rfl⟩, by decide⟩
  have hf2 : (irGraph .ra).rf irWY irR2Y := by
    show irRf irWY irR2Y
    decide
  have hp2 : (irGraph .ra).po irR2Y irR2X := by
    show irPo irR2Y irR2X
    decide
  have hrb2 : (irGraph .ra).rb irR2X irWX := by
    exact ⟨irIX, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), Or.inl ⟨rfl, rfl⟩, by decide⟩
  exact ⟨IriwEv, Bool, Nat, irGraph .ra, ir_konsistent,
    irWX, irWY, irR1X, irR1Y, irR2Y, irR2X, hf1, hp1, hrb1, hf2, hp2, hrb2⟩

end Gabbro.Core.Ziel.Korrektheit
