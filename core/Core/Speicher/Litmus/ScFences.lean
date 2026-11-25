/-
  File:      core/Core/Speicher/Litmus/ScFences.lean
  Subject:   SC-FENCES litmus group: store buffering with `sc` fences between relaxed accesses and
             message passing with fences, as catalogue entries over the RC11 model.

  Source: Lahav, Vafeiadis, Kang, Hur, Dreyer, "Repairing Sequential Consistency in C/C++11",
  PLDI 2017 (SC-fences section: `x := rlx 1; fence sc; a := y rlx ‖ y := rlx 1; fence sc; b := x rlx`
  admits only `a = 1 ∨ b = 1`); Batty et al. and the herd/C11 catalogue (MP with fences).

  Modes: the four memory accesses are `.rlx`; a barrier is an `.sc` outside event in program order
  between a write and its read (`Core/Speicher/Basis.lean` has no fence form, so an outside event is
  the stand-in). The allowed halves keep `.rlx` accesses and do not strengthen a mode.

  Expected: FORBIDDEN for both fenced shapes in RC11, ALLOWED for the relaxed shapes without fences.

  MODEL FINDING: `Core/Speicher` is the FENCE-FREE RC11 fragment: `psc` has no fence clause, so an
  `.sc` outside event carries no ordering power. Both `…VerbotenAussage` are FALSE in this model;
  their negations are proved with consistent and complete graphs (`fGraph`), and the pinned root
  records that refutation as the model-side result. The model is not changed here.
-/
module

public import Core.Speicher.Litmus.Sb

@[expose] public section

namespace Gabbro.Core.Speicher

/-- Eight events: initial writes `ix`/`iy`, writers `a1`/`a2`, readers `b1`/`b2` and the two `sc`
    barriers `f1`/`f2`. With `mp = false` the graph is SB, with `mp = true` it is MP. -/
inductive FenceEv where
  | ix | iy | a1 | b1 | a2 | b2 | f1 | f2
  deriving DecidableEq, Repr

open FenceEv

/-- Program order: initial writes precede all other events; `a1; f1; b1` and `a2; f2; b2` are the
    two threads, with a barrier between each write and its read. -/
abbrev fPo (a b : FenceEv) : Prop :=
  (a = ix ∧ b ≠ ix) ∨
  (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨
  (a = a1 ∧ (b = b1 ∨ b = f1)) ∨
  (a = f1 ∧ b = b1) ∨
  (a = a2 ∧ (b = b2 ∨ b = f2)) ∨
  (a = f2 ∧ b = b2)

/-- SB: `b1` reads the initial `y`, `b2` the initial `x`. MP: `a2` reads the flag from `b1`, `b2`
    the data from `ix`. -/
abbrev fRf (mp : Bool) (a b : FenceEv) : Prop :=
  (a = ix ∧ b = b2) ∨ (if mp then a = b1 ∧ b = a2 else a = iy ∧ b = b1)

abbrev fMo (mp : Bool) (a b : FenceEv) : Prop :=
  (a = ix ∧ b = a1) ∨ (if mp then a = iy ∧ b = b1 else a = iy ∧ b = a2)

/-- The closure of `rf ∪ mo ∪ rb` in either graph, in closed form. -/
abbrev fEco (a b : FenceEv) : Prop :=
  (a = ix ∧ (b = a1 ∨ b = b2)) ∨
  (a = iy ∧ (b = a2 ∨ b = b1)) ∨
  (a = b1 ∧ b = a2) ∨
  (a = b2 ∧ b = a1)

/-- SB: writes to `x`/`y`, reads of `y`/`x`, two `.rlx` readers. MP: a data write, a flag write, a
    flag read returning 1 and a data read returning 0, all `.rlx`. Both barriers are `.sc` outside
    events, so no barrier reads or writes memory. -/
def fLab (mp : Bool) : FenceEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, .rlx, 0, 0⟩
  | iy => ⟨.schreiben, true, .rlx, 0, 0⟩
  | a1 => ⟨.schreiben, false, .rlx, 0, 1⟩
  | b1 => if mp then ⟨.schreiben, true, .rlx, 0, 1⟩ else ⟨.lesen, true, .rlx, 0, 0⟩
  | a2 => if mp then ⟨.lesen, true, .rlx, 1, 0⟩ else ⟨.schreiben, true, .rlx, 0, 1⟩
  | b2 => ⟨.lesen, false, .rlx, 0, 0⟩
  | f1 | f2 => ⟨.aussen, false, .sc, 0, 0⟩

def fGraph (mp : Bool) : Graph FenceEv Bool Nat := ⟨fLab mp, fPo, fRf mp, fMo mp⟩

theorem f_po_trans (a b c : FenceEv) : (fPo a b ∧ fPo b c) → fPo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem f_mo_trans (mp : Bool) (a b c : FenceEv) :
    (fMo mp a b ∧ fMo mp b c) → fMo mp a c := by
  cases mp <;> cases a <;> cases b <;> cases c <;> decide

theorem f_rf_eindeutig (mp : Bool) (w w' r : FenceEv) :
    (fRf mp w r ∧ fRf mp w' r) → w = w' := by
  cases mp <;> cases w <;> cases w' <;> cases r <;> decide

theorem f_wf (mp : Bool) : (fGraph mp).Wohlgeformt where
  po_trans := by
    intro a b c hab hbc
    exact f_po_trans a b c ⟨hab, hbc⟩
  po_irrefl := by
    intro a
    show ¬ fPo a a
    cases a <;> decide
  rf_schreibt := by
    intro w r h
    cases mp
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial
  rf_liest := by
    intro w r h
    cases mp
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> trivial
  rf_ort := by
    intro w r h
    cases mp
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rf_wert := by
    intro w r h
    cases mp
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rf_eindeutig := by
    intro w w' r h1 h2
    exact f_rf_eindeutig mp w w' r ⟨h1, h2⟩
  mo_schreibt := by
    intro a b h
    cases mp
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨trivial, trivial⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨trivial, trivial⟩
  mo_ort := by
    intro a b h
    cases mp
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  mo_trans := by
    intro a b c hab hbc
    exact f_mo_trans mp a b c ⟨hab, hbc⟩
  mo_irrefl := by
    intro a
    show ¬ fMo mp a a
    cases mp <;> cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    cases mp <;> cases a <;> cases b <;>
      first
        | exact Or.inl (by decide)
        | exact Or.inr (by decide)
        | exact False.elim ha
        | exact False.elim hb
        | exact False.elim (hne rfl)
        | (simp only [Graph.ort, fGraph, fLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)

/-- No synchronises-with edge: a memory event is `.rlx` (not `stark`) and a barrier reads and
    writes nothing. -/
theorem f_kein_sw (mp : Bool) (a b : FenceEv) : ¬ (fGraph mp).sw a b := by
  intro h
  obtain ⟨hsa, hsta, hlb, hstb, x, hrs, hrf⟩ := h
  cases mp <;> cases a <;>
    simp only [Graph.schreibt, Graph.modus, fGraph, fLab, Modus.stark, reduceCtorEq] at hsa hsta

theorem f_hb_in_po {mp : Bool} {a b : FenceEv} (h : (fGraph mp).hb a b) : fPo a b :=
  transGen_von_trans (f_wf mp).po_trans
    (transGen_mono (fun x y s => by
      rcases s with hp | hs
      · exact hp
      · exact False.elim (f_kein_sw mp x y hs)) h)

theorem fEco_trans (a b c : FenceEv) : (fEco a b ∧ fEco b c) → fEco a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem f_rb_eco (mp : Bool) (w a b : FenceEv) :
    (fRf mp w a ∧ fMo mp w b ∧ a ≠ b) → fEco a b := by
  cases mp <;> cases w <;> cases a <;> cases b <;> decide

theorem f_koh (a b : FenceEv) : (fPo a b ∧ fEco b a) → False := by
  cases a <;> cases b <;> decide

theorem f_eco_schritt {mp : Bool} {a b : FenceEv} (h : (fGraph mp).ecoSchritt a b) : fEco a b := by
  rcases h with hrf | hmo | hrb
  · revert hrf
    cases mp <;> cases a <;> cases b <;> decide
  · revert hmo
    cases mp <;> cases a <;> cases b <;> decide
  · rcases hrb with ⟨w, h1, h2, hne⟩
    exact f_rb_eco mp w a b ⟨h1, h2, hne⟩

theorem f_eco {mp : Bool} {a b : FenceEv} (h : (fGraph mp).eco a b) : fEco a b :=
  transGen_von_trans (fun x y z hxy hyz => fEco_trans x y z ⟨hxy, hyz⟩)
    (transGen_mono (fun _ _ h => f_eco_schritt h) h)

/-- An `sc` event is a barrier; barriers are in different threads and neither write nor read. -/
theorem f_kein_psc (mp : Bool) (a b : FenceEv) : ¬ (fGraph mp).psc a b := by
  intro h
  obtain ⟨hsa, hsb, hscb⟩ := h
  have hfa : a = f1 ∨ a = f2 := by
    cases mp <;> cases a <;>
      simp only [Graph.sc, Graph.modus, fGraph, fLab, reduceCtorEq] at hsa ⊢ <;>
      first | contradiction | decide
  have hfb : b = f1 ∨ b = f2 := by
    cases mp <;> cases b <;>
      simp only [Graph.sc, Graph.modus, fGraph, fLab, reduceCtorEq] at hsb ⊢ <;>
      first | contradiction | decide
  have hpo : ¬ fPo a b := by
    rcases hfa with rfl | rfl <;> rcases hfb with rfl | rfl <;> decide
  rcases hscb with hp | h₂ | h₃ | hmo | hrb
  · exact hpo hp
  · obtain ⟨c, d, hpc, _, hcd, hdb, _⟩ := h₂
    exact hpo ((f_wf mp).po_trans a c b hpc
      ((f_wf mp).po_trans c d b (f_hb_in_po hcd) hdb))
  · exact hpo (f_hb_in_po h₃.1)
  · revert hmo
    rcases hfa with rfl | rfl <;> cases mp <;> cases b <;> decide
  · obtain ⟨w, hrf, _, _⟩ := hrb
    revert hrf
    rcases hfa with rfl | rfl <;> cases mp <;> cases w <;> decide

theorem f_psc_acyclisch (mp : Bool) : Azyklisch (fGraph mp).psc := by
  intro a h
  obtain ⟨c, hc⟩ := transGen_kopf h
  exact f_kein_psc mp a c hc

/-- A rank that every `po` and `rf` edge raises, for `ohneLB`. -/
def fRang : FenceEv → Nat
  | ix => 0
  | iy => 1
  | a1 => 2
  | f1 => 3
  | b1 => 4
  | a2 => 5
  | f2 => 6
  | b2 => 7

theorem f_konsistent (mp : Bool) : (fGraph mp).Konsistent where
  wf := f_wf mp
  hb_irrefl := by
    intro a h
    exact (by cases a <;> decide : ¬ fPo a a) (f_hb_in_po h)
  kohaerent := by
    intro a b h he
    exact f_koh a b ⟨f_hb_in_po h, f_eco he⟩
  atomar := by
    intro w u w' hrf hu hmo
    cases mp <;> cases u <;> simp only [fGraph, fLab, Graph.istRmw, reduceCtorEq] at hu
  psc := f_psc_acyclisch mp
  ohneLB := by
    refine azyklisch_von_rang fRang ?_
    intro a b h
    revert h
    cases mp <;> cases a <;> cases b <;> decide
  liest_vorher := by
    intro w u hrf hu
    cases mp <;> cases u <;> simp only [fGraph, fLab, Graph.istRmw, reduceCtorEq] at hu

theorem f_vollstaendig (mp : Bool) : (fGraph mp).Vollstaendig := by
  intro r hr
  cases mp <;> cases r <;> simp only [Graph.liest, fGraph, fLab, Art.liest, reduceCtorEq] at hr
  · exact ⟨iy, by decide⟩
  · exact ⟨ix, by decide⟩
  · exact ⟨b1, by decide⟩
  · exact ⟨ix, by decide⟩

theorem f_rb_b1_a2 : (fGraph false).rb b1 a2 :=
  ⟨iy, (by show fRf false iy b1; decide), (by show fMo false iy a2; decide), by decide⟩

theorem f_rb_b2_a1 (mp : Bool) : (fGraph mp).rb b2 a1 :=
  ⟨ix, (by show fRf mp ix b2; decide), (by show fMo mp ix a1; decide), by decide⟩

/-- **Literature statement, FALSE in this model:** SB with an `sc` fence between each relaxed
    write and its read cannot have both reads miss the other thread's write. Feeds: its negation
    `sc_fences_sb_nicht_verboten`. -/
def ScFencesSbVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ wx f₁ rx wy f₂ ry ix iy : E,
        G.modus wx = .rlx ∧ G.modus rx = .rlx ∧ G.modus wy = .rlx ∧ G.modus ry = .rlx ∧
        G.sc f₁ ∧ G.sc f₂ ∧
        G.po wx f₁ ∧ G.po f₁ rx ∧ G.po wy f₂ ∧ G.po f₂ ry ∧
        G.rf iy rx ∧ G.rf ix ry ∧ G.rb rx wy ∧ G.rb ry wx

/-- The RC11-forbidden SB outcome is consistent here: the fences have no `psc` clause. -/
theorem sc_fences_sb_nicht_verboten : ¬ ScFencesSbVerbotenAussage := by
  intro h
  apply h
  refine ⟨FenceEv, Bool, Nat, fGraph false, f_konsistent false,
    a1, f1, b1, a2, f2, b2, ix, iy, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (by decide : (fGraph false).po a1 f1), (by decide : (fGraph false).po f1 b1),
    (by decide : (fGraph false).po a2 f2), (by decide : (fGraph false).po f2 b2),
    (by decide : (fGraph false).rf iy b1), (by decide : (fGraph false).rf ix b2),
    f_rb_b1_a2, f_rb_b2_a1 false⟩

/-- **The relaxed SB outcome is allowed:** a consistent and complete graph with the two writes
    and their reads and both reads-before edges. Feeds: `sb_ohne_sc_erlaubt`, `sb_vollstaendig`. -/
def ScFencesSbErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wx rx wy ry ix iy : E,
        G.modus wx = .rlx ∧ G.modus rx = .rlx ∧ G.modus wy = .rlx ∧ G.modus ry = .rlx ∧
        G.po wx rx ∧ G.po wy ry ∧ G.rf iy rx ∧ G.rf ix ry ∧ G.rb rx wy ∧ G.rb ry wx

theorem sc_fences_sb_erlaubt : ScFencesSbErlaubtAussage := by
  obtain ⟨hk, p₁, p₂, r₁, r₂⟩ := sb_ohne_sc_erlaubt .rlx (by decide)
  have hf₁ : (sbGraph .rlx).rf iy b1 := by
    show sbRf iy b1
    decide
  have hf₂ : (sbGraph .rlx).rf ix b2 := by
    show sbRf ix b2
    decide
  refine ⟨SbEv, Bool, Nat, sbGraph .rlx, hk, sb_vollstaendig .rlx,
    a1, b1, a2, b2, ix, iy, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide, p₁, p₂, hf₁, hf₂, r₁, r₂⟩

/-- **Literature statement, FALSE in this model:** message passing with an `sc` fence after the
    relaxed data write and before the relaxed flag write, and one between the flag read and the
    data read, cannot see the flag and still read stale data. Feeds: its negation. -/
def ScFencesMpVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ wd f₁ wf rf' f₂ rd id : E,
        G.modus wd = .rlx ∧ G.modus wf = .rlx ∧ G.modus rf' = .rlx ∧ G.modus rd = .rlx ∧
        G.sc f₁ ∧ G.sc f₂ ∧
        G.po wd f₁ ∧ G.po f₁ wf ∧ G.po rf' f₂ ∧ G.po f₂ rd ∧
        G.rf wf rf' ∧ G.rf id rd ∧ G.rb rd wd

/-- The RC11-forbidden MP outcome is consistent here for the same reason. -/
theorem sc_fences_mp_nicht_verboten : ¬ ScFencesMpVerbotenAussage := by
  intro h
  apply h
  refine ⟨FenceEv, Bool, Nat, fGraph true, f_konsistent true,
    a1, f1, b1, a2, f2, b2, ix, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (by decide : (fGraph true).po a1 f1), (by decide : (fGraph true).po f1 b1),
    (by decide : (fGraph true).po a2 f2), (by decide : (fGraph true).po f2 b2),
    (by decide : (fGraph true).rf b1 a2), (by decide : (fGraph true).rf ix b2),
    f_rb_b2_a1 true⟩

/-- **The relaxed MP outcome is allowed:** a consistent and complete graph in which the flag read
    sees the flag write while the data read sees the initial write. -/
def ScFencesMpErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wd wf rf' rd id : E,
        G.modus wd = .rlx ∧ G.modus wf = .rlx ∧ G.modus rf' = .rlx ∧ G.modus rd = .rlx ∧
        G.po wd wf ∧ G.po rf' rd ∧ G.rf wf rf' ∧ G.rf id rd ∧ G.rb rd wd

theorem sc_fences_mp_erlaubt : ScFencesMpErlaubtAussage := by
  refine ⟨FenceEv, Bool, Nat, fGraph true, f_konsistent true, f_vollstaendig true,
    a1, b1, a2, b2, ix, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide,
    (by decide : (fGraph true).po a1 b1), (by decide : (fGraph true).po a2 b2),
    (by decide : (fGraph true).rf b1 a2), (by decide : (fGraph true).rf ix b2),
    f_rb_b2_a1 true⟩

/-- **The SC-fence group root.** The two literature-forbidden halves are refuted by this model, so
    the pinned model-side result records their negations together with the two allowed halves. -/
def ScFencesLitmusAussage : Prop :=
  (¬ ScFencesSbVerbotenAussage ∧ ScFencesSbErlaubtAussage) ∧
  (¬ ScFencesMpVerbotenAussage ∧ ScFencesMpErlaubtAussage)

theorem sc_fences_litmus : ScFencesLitmusAussage :=
  ⟨⟨sc_fences_sb_nicht_verboten, sc_fences_sb_erlaubt⟩,
    ⟨sc_fences_mp_nicht_verboten, sc_fences_mp_erlaubt⟩⟩

end Gabbro.Core.Speicher
