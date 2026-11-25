/-
  File:      core/Core/Speicher/Litmus/Isa2.lean
  Subject:   ISA2 catalogue entry: the three-thread forwarding chain
             `x := 1; y := 1 ‖ r1 := y; z := 1 ‖ r2 := z; r3 := x` with `r1 = 1`, `r2 = 1` and
             `r3 = 0` -- the message at `x` fails to arrive at the third thread.

  Source: Batty et al. (herd/OpenCL catalogue, `ISA2.litmus`, Example 6), the cumulativity /
  two-hop message-passing test, and the RC11 model of Lahav et al. (PLDI 2017). The hardware form
  uses `lwsync` plus dependencies; the Gabbro fragment has no fence form and no dependencies, so
  the two forwarding flags `y` and `z` are release/acquire accesses and carry the ordering instead.
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

/-- **The two-hop forwarding outcome is forbidden with release/acquire or stronger.** A first
    thread writes `wx` then `wy`; the second reads `wy` and writes `wz`; the third reads `wz` and
    then reads before `wx` in `rb`. With `stark` modes both forwarding `rf` edges are `sw` edges,
    so `hb` chains `wx` to the stale reader and coherence rejects the backward `eco` edge. -/
theorem isa2_stark_verboten (hk : G.Konsistent) {wx wy r1 wz r2 r3 : E}
    (hs : ∀ a, (G.modus a).stark)
    (p0 : G.po wx wy) (f1 : G.rf wy r1) (p1 : G.po r1 wz)
    (f2 : G.rf wz r2) (p2 : G.po r2 r3) (rb : G.rb r3 wx) : False := by
  have hs1 : G.sw wy r1 := by
    refine ⟨hk.wf.rf_schreibt _ _ f1, hs wy, hk.wf.rf_liest _ _ f1, hs r1, wy, ?_, f1⟩
    exact Rs.selbst (hk.wf.rf_schreibt _ _ f1)
  have hs2 : G.sw wz r2 := by
    refine ⟨hk.wf.rf_schreibt _ _ f2, hs wz, hk.wf.rf_liest _ _ f2, hs r2, wz, ?_, f2⟩
    exact Rs.selbst (hk.wf.rf_schreibt _ _ f2)
  have hb : G.hb wx r3 :=
    G.hb_trans (G.hb_trans (G.hb_trans (G.hb_trans (G.hb_von_po p0) (G.hb_von_sw hs1))
      (G.hb_von_po p1)) (G.hb_von_sw hs2)) (G.hb_von_po p2)
  exact hk.kohaerent wx r3 hb (G.eco_von_rb rb)

end Graph

/-- The nine events: three initial writes, the first thread `wx; wy`, the forwarding thread
    `r1; wz` and the receiving thread `r2; r3`. -/
inductive Isa2Ev where
  | ix | iy | iz | wx | wy | r1 | wz | r2 | r3
  deriving DecidableEq, Repr

open Isa2Ev

/-- Locations `0 = x`, `1 = y`, `2 = z`. `wx` writes `x := 1`, `wy` writes `y := 1`, `r1` reads
    it; `wz` writes `z := 1`, `r2` reads it; `r3` reads the initial `x := 0`. -/
def isa2Lab (m : Modus) : Isa2Ev → Etikett Nat Nat
  | ix => ⟨.schreiben, 0, m, 0, 0⟩
  | iy => ⟨.schreiben, 1, m, 0, 0⟩
  | iz => ⟨.schreiben, 2, m, 0, 0⟩
  | wx => ⟨.schreiben, 0, m, 0, 1⟩
  | wy => ⟨.schreiben, 1, m, 0, 1⟩
  | r1 => ⟨.lesen, 1, m, 1, 0⟩
  | wz => ⟨.schreiben, 2, m, 0, 1⟩
  | r2 => ⟨.lesen, 2, m, 1, 0⟩
  | r3 => ⟨.lesen, 0, m, 0, 0⟩

abbrev isa2Po (a b : Isa2Ev) : Prop :=
  (a = ix ∧ b ≠ ix) ∨ (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨
    (a = iz ∧ b ≠ ix ∧ b ≠ iy ∧ b ≠ iz) ∨
    (a = wx ∧ b = wy) ∨ (a = r1 ∧ b = wz) ∨ (a = r2 ∧ b = r3)

abbrev isa2Rf (a b : Isa2Ev) : Prop :=
  (a = wy ∧ b = r1) ∨ (a = wz ∧ b = r2) ∨ (a = ix ∧ b = r3)

abbrev isa2Mo (a b : Isa2Ev) : Prop :=
  (a = ix ∧ b = wx) ∨ (a = iy ∧ b = wy) ∨ (a = iz ∧ b = wz)

/-- The transitive closure of `rf ∪ mo ∪ rb` in this graph. -/
abbrev isa2Eco (a b : Isa2Ev) : Prop :=
  (a = ix ∧ (b = wx ∨ b = r3)) ∨ (a = iy ∧ (b = wy ∨ b = r1)) ∨
    (a = iz ∧ (b = wz ∨ b = r2)) ∨ (a = wy ∧ b = r1) ∨
    (a = wz ∧ b = r2) ∨ (a = r3 ∧ b = wx)

/-- A rank that every `po` and `rf` step raises. -/
def isa2Rang : Isa2Ev → Nat
  | ix => 0
  | iy => 1
  | iz => 2
  | wx => 3
  | wy => 4
  | r1 => 5
  | wz => 6
  | r2 => 7
  | r3 => 8

def isa2Graph (m : Modus) : Graph Isa2Ev Nat Nat := ⟨isa2Lab m, isa2Po, isa2Rf, isa2Mo⟩

abbrev isa2Schreibt (m : Modus) (a : Isa2Ev) : Prop := (isa2Lab m a).art.schreibt
abbrev isa2Liest (m : Modus) (a : Isa2Ev) : Prop := (isa2Lab m a).art.liest
abbrev isa2Ort (m : Modus) (a : Isa2Ev) : Nat := (isa2Lab m a).ort

theorem isa2Po_trans (a b c : Isa2Ev) : (isa2Po a b ∧ isa2Po b c) → isa2Po a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem isa2Mo_trans (a b c : Isa2Ev) : (isa2Mo a b ∧ isa2Mo b c) → isa2Mo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem isa2Eco_trans (a b c : Isa2Ev) : (isa2Eco a b ∧ isa2Eco b c) → isa2Eco a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem isa2Rf_schreibt (m : Modus) (w r : Isa2Ev) (h : isa2Rf w r) : isa2Schreibt m w := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem isa2Rf_liest (m : Modus) (w r : Isa2Ev) (h : isa2Rf w r) : isa2Liest m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial

theorem isa2Rf_ort (m : Modus) (w r : Isa2Ev) (h : isa2Rf w r) : isa2Ort m w = isa2Ort m r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem isa2Rf_wert (m : Modus) (w r : Isa2Ev) (h : isa2Rf w r) :
    (isa2Lab m w).geschrieben = (isa2Lab m r).gelesen := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem isa2Rf_eindeutig (w w' r : Isa2Ev) : (isa2Rf w r ∧ isa2Rf w' r) → w = w' := by
  cases w <;> cases w' <;> cases r <;> decide

theorem isa2Mo_schreibt (m : Modus) (a b : Isa2Ev) (h : isa2Mo a b) :
    isa2Schreibt m a ∧ isa2Schreibt m b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨trivial, trivial⟩

theorem isa2Mo_ort (m : Modus) (a b : Isa2Ev) (h : isa2Mo a b) : isa2Ort m a = isa2Ort m b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem isa2Mo_total (m : Modus) (a b : Isa2Ev) (ha : isa2Schreibt m a) (hb : isa2Schreibt m b)
    (ho : isa2Ort m a = isa2Ort m b) (hne : a ≠ b) : isa2Mo a b ∨ isa2Mo b a := by
  cases a <;> cases b <;>
    first
      | exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      | exact False.elim ha
      | exact False.elim hb
      | exact False.elim (hne rfl)
      | (simp only [isa2Ort, isa2Lab, Nat.succ.injEq, reduceCtorEq] at ho; done)

theorem isa2_wf (m : Modus) : (isa2Graph m).Wohlgeformt where
  po_trans := by
    intro a b c hab hbc
    exact isa2Po_trans a b c ⟨hab, hbc⟩
  po_irrefl := by
    intro a
    show ¬ isa2Po a a
    cases a <;> decide
  rf_schreibt := by intro w r h; exact isa2Rf_schreibt m w r h
  rf_liest := by intro w r h; exact isa2Rf_liest m w r h
  rf_ort := by intro w r h; exact isa2Rf_ort m w r h
  rf_wert := by intro w r h; exact isa2Rf_wert m w r h
  rf_eindeutig := by
    intro w w' r h1 h2
    exact isa2Rf_eindeutig w w' r ⟨h1, h2⟩
  mo_schreibt := by intro a b h; exact isa2Mo_schreibt m a b h
  mo_ort := by intro a b h; exact isa2Mo_ort m a b h
  mo_trans := by
    intro a b c hab hbc
    exact isa2Mo_trans a b c ⟨hab, hbc⟩
  mo_irrefl := by
    intro a
    show ¬ isa2Mo a a
    cases a <;> decide
  mo_total := by intro a b ha hb ho hne; exact isa2Mo_total m a b ha hb ho hne
  rmw_nicht_na := by
    intro a h
    cases a <;> simp only [Graph.istRmw, isa2Graph, isa2Lab, reduceCtorEq] at h

theorem isa2_kein_rmw (m : Modus) (u : Isa2Ev) : ¬ (isa2Graph m).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, isa2Graph, isa2Lab, reduceCtorEq] at hu

theorem isa2_rb {m : Modus} {r w : Isa2Ev} (h : (isa2Graph m).rb r w) : r = r3 ∧ w = wx := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show isa2Rf w' r → isa2Mo w' w → _
  cases w' <;> cases r <;> cases w <;> decide

theorem isa2_eco_schritt {m : Modus} {a b : Isa2Ev} (h : (isa2Graph m).ecoSchritt a b) : isa2Eco a b := by
  rcases h with h | h | h
  · revert h
    show isa2Rf a b → isa2Eco a b
    cases a <;> cases b <;> decide
  · revert h
    show isa2Mo a b → isa2Eco a b
    cases a <;> cases b <;> decide
  · rcases isa2_rb h with ⟨rfl, rfl⟩ <;> decide

theorem isa2_eco {m : Modus} {a b : Isa2Ev} (h : (isa2Graph m).eco a b) : isa2Eco a b :=
  transGen_von_trans (fun x y z hxy hyz => isa2Eco_trans x y z ⟨hxy, hyz⟩)
    (transGen_mono (fun _ _ h => isa2_eco_schritt h) h)

theorem isa2_modus (m : Modus) (a : Isa2Ev) : (isa2Graph m).modus a = m := by
  cases a <;> rfl

/-- With a non-synchronising mode no `sw` edge exists, so `hb` is contained in `po`. -/
theorem isa2_hb (m : Modus) (hm : ¬ m.stark) {a b : Isa2Ev} (h : (isa2Graph m).hb a b) : isa2Po a b := by
  have hs : ∀ x y, (isa2Graph m).hbSchritt x y → isa2Po x y := by
    intro x y hxy
    rcases hxy with hpo | hsw
    · exact hpo
    · obtain ⟨_, hst, _, _, _⟩ := hsw
      rw [isa2_modus m x] at hst
      exact False.elim (hm hst)
  exact transGen_von_trans (fun x y z hxy hyz => isa2Po_trans x y z ⟨hxy, hyz⟩)
    (transGen_mono hs h)

theorem isa2_kein_sc (m : Modus) (hm : ¬ m.stark) (a : Isa2Ev) : ¬ (isa2Graph m).sc a := by
  have hmsc : m ≠ .sc := by
    intro h
    subst h
    exact hm trivial
  cases a <;> simp only [Graph.sc, Graph.modus, isa2Graph, isa2Lab, reduceCtorEq] <;> exact hmsc

/-- The outcome's shape in the small graph, independent of the mode. -/
theorem isa2_shape (m : Modus) :
    (isa2Graph m).po wx wy ∧ (isa2Graph m).rf wy r1 ∧ (isa2Graph m).po r1 wz ∧
      (isa2Graph m).rf wz r2 ∧ (isa2Graph m).po r2 r3 ∧ (isa2Graph m).rb r3 wx := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  · exact ⟨ix, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩, by decide⟩

/-- **The ISA2 outcome is consistent in every non-synchronising mode.** Feeds: closed-form
    well-formedness, coherence, empty `psc`, empty atomicity obligations, rank for `ohneLB`. -/
theorem isa2_ohne_stark_erlaubt (m : Modus) (hm : ¬ m.stark) :
    (isa2Graph m).Konsistent ∧ (isa2Graph m).po wx wy ∧ (isa2Graph m).rf wy r1 ∧
      (isa2Graph m).po r1 wz ∧ (isa2Graph m).rf wz r2 ∧ (isa2Graph m).po r2 r3 ∧
      (isa2Graph m).rb r3 wx := by
  refine ⟨⟨isa2_wf m, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a h
    have hp := isa2_hb m hm h
    revert hp
    cases a <;> decide
  · intro a b hab he
    have hp := isa2_hb m hm hab
    have he' := isa2_eco he
    revert hp he'
    cases a <;> cases b <;> decide
  · intro w u _ _ hu
    exact absurd hu (isa2_kein_rmw m u)
  · intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    exact isa2_kein_sc m hm a hc.1
  · refine azyklisch_von_rang isa2Rang ?_
    intro a b
    show isa2Po a b ∨ isa2Rf a b → isa2Rang a < isa2Rang b
    cases a <;> cases b <;> decide
  · intro w u _ hu
    exact absurd hu (isa2_kein_rmw m u)
  · exact (isa2_shape m).1
  · exact (isa2_shape m).2.1
  · exact (isa2_shape m).2.2.1
  · exact (isa2_shape m).2.2.2.1
  · exact (isa2_shape m).2.2.2.2.1
  · exact (isa2_shape m).2.2.2.2.2

theorem isa2_vollstaendig (m : Modus) : (isa2Graph m).Vollstaendig := by
  intro r hr
  cases r with
  | ix => exact (hr : False).elim
  | iy => exact (hr : False).elim
  | iz => exact (hr : False).elim
  | wx => exact (hr : False).elim
  | wy => exact (hr : False).elim
  | r1 => exact ⟨wy, Or.inl ⟨rfl, rfl⟩⟩
  | wz => exact (hr : False).elim
  | r2 => exact ⟨wz, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | r3 => exact ⟨ix, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- **Forbidden ISA2.** No consistent graph with every access `stark` has the shape. -/
def Isa2StarkVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ (∀ a, (G.modus a).stark) ∧
      ∃ wx wy r1 wz r2 r3 : E,
        G.po wx wy ∧ G.rf wy r1 ∧ G.po r1 wz ∧ G.rf wz r2 ∧ G.po r2 r3 ∧ G.rb r3 wx

/-- **Allowed ISA2.** Some consistent and complete graph (all `.rlx`) has the shape. -/
def Isa2RlxErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wx wy r1 wz r2 r3 : E,
        G.po wx wy ∧ G.rf wy r1 ∧ G.po r1 wz ∧ G.rf wz r2 ∧ G.po r2 r3 ∧ G.rb r3 wx

/-- **The pinned ISA2 group root.** -/
def Isa2LitmusAussage : Prop := Isa2StarkVerbotenAussage ∧ Isa2RlxErlaubtAussage

theorem isa2_stark_verboten_kat : Isa2StarkVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, hs, wx, wy, r1, wz, r2, r3, p0, f1, p1, f2, p2, rb⟩
  exact Graph.isa2_stark_verboten hk hs p0 f1 p1 f2 p2 rb

theorem isa2_rlx_erlaubt_kat : Isa2RlxErlaubtAussage := by
  obtain ⟨hk, p0, f1, p1, f2, p2, rb⟩ := isa2_ohne_stark_erlaubt .rlx (by intro h; cases h)
  exact ⟨Isa2Ev, Nat, Nat, isa2Graph .rlx, hk, isa2_vollstaendig .rlx,
    wx, wy, r1, wz, r2, r3, p0, f1, p1, f2, p2, rb⟩

theorem isa2_litmus : Isa2LitmusAussage := ⟨isa2_stark_verboten_kat, isa2_rlx_erlaubt_kat⟩

/-- Non-vacuity of the forbidden half: the same shape with `.ra` is not consistent. -/
theorem isa2_stark_inkonsistent : ¬ (isa2Graph .ra).Konsistent := by
  intro hk
  obtain ⟨p0, f1, p1, f2, p2, rb⟩ := isa2_shape .ra
  exact Graph.isa2_stark_verboten hk (by intro a; cases a <;> trivial) p0 f1 p1 f2 p2 rb

end Gabbro.Core.Speicher
