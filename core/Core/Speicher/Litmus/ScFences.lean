/-
  File:      core/Core/Speicher/Litmus/ScFences.lean
  Subject:   SC-FENCES litmus group: store buffering with `sc` fences between relaxed accesses and
             message passing with fences, as catalogue entries over the RC11 model with fences.

  Source: Lahav, Vafeiadis, Kang, Hur, Dreyer, "Repairing Sequential Consistency in C/C++11",
  PLDI 2017 (SC-fences section: `x := rlx 1; fence sc; a := y rlx ‖ y := rlx 1; fence sc; b := x rlx`
  admits only `a = 1 ∨ b = 1`); Batty et al. and the herd/C11 catalogue (MP with fences).

  Modes: the four memory accesses are `.rlx`. A barrier is a real fence event (`Art.zaun`) with mode
  `sc` in the forbidden shape and mode `rlx` in the allowed counter-probe. The prohibition is a
  generic consequence of `pscZaun` and the acyclicity of `psc`; the allowance is a consistent and
  complete finite graph with `rlx` fences, so the refusal comes from the `sc` fence alone.

  Expected: FORBIDDEN for both fenced shapes in RC11, ALLOWED with `rlx` fences.
-/
module

public import Core.Speicher.Relationen
public import Core.Speicher.Erfuellbar
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- Eight events: initial writes `ix`/`iy`, writers `a1`/`a2`, readers `b1`/`b2` and the two
    fence events `f1`/`f2`. With `mp = false` the graph is SB, with `mp = true` it is MP. -/
inductive FenceEv where
  | ix | iy | a1 | b1 | a2 | b2 | f1 | f2
  deriving DecidableEq, Repr

open FenceEv

/-- Program order: initial writes precede all other events; `a1; f1; b1` and `a2; f2; b2` are the
    two threads, with a fence between each write and its read. -/
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
    flag read returning 1 and a data read returning 0, all `.rlx`. Both barriers are real fence
    events of the chosen mode `mf`; a fence neither reads nor writes memory. -/
def fLab (mp : Bool) (mf : Modus) : FenceEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, .rlx, 0, 0⟩
  | iy => ⟨.schreiben, true, .rlx, 0, 0⟩
  | a1 => ⟨.schreiben, false, .rlx, 0, 1⟩
  | b1 => if mp then ⟨.schreiben, true, .rlx, 0, 1⟩ else ⟨.lesen, true, .rlx, 0, 0⟩
  | a2 => if mp then ⟨.lesen, true, .rlx, 1, 0⟩ else ⟨.schreiben, true, .rlx, 0, 1⟩
  | b2 => ⟨.lesen, false, .rlx, 0, 0⟩
  | f1 | f2 => ⟨.zaun, false, mf, 0, 0⟩

def fGraph (mp : Bool) (mf : Modus) : Graph FenceEv Bool Nat := ⟨fLab mp mf, fPo, fRf mp, fMo mp⟩

theorem f_po_trans (a b c : FenceEv) : (fPo a b ∧ fPo b c) → fPo a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem f_mo_trans (mp : Bool) (a b c : FenceEv) :
    (fMo mp a b ∧ fMo mp b c) → fMo mp a c := by
  cases mp <;> cases a <;> cases b <;> cases c <;> decide

theorem f_rf_eindeutig (mp : Bool) (w w' r : FenceEv) :
    (fRf mp w r ∧ fRf mp w' r) → w = w' := by
  cases mp <;> cases w <;> cases w' <;> cases r <;> decide

theorem f_wf (mp : Bool) (mf : Modus) : (fGraph mp mf).Wohlgeformt where
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
    show fMo mp a b ∨ fMo mp b a
    cases mp <;> cases a <;> cases b <;>
      first
        | exact Or.inl (by decide)
        | exact Or.inr (by decide)
        | exact False.elim ha
        | exact False.elim hb
        | exact False.elim (hne rfl)
        | (simp only [Graph.ort, fGraph, fLab, Art.schreibt, reduceCtorEq, if_false, if_true,
            Bool.false_eq_true, Bool.true_eq_false] at ho; done)
  rmw_nicht_na := by
    intro a h
    cases mp <;> cases a <;>
      simp only [fGraph, fLab, Graph.istRmw, reduceCtorEq, if_false, if_true] at h

/-- With `rlx` fences every event has a non-strong mode, so there is no synchronises-with edge. -/
theorem f_kein_sw (mp : Bool) (a b : FenceEv) : ¬ (fGraph mp .rlx).sw a b := by
  intro h
  have hs := Graph.sw_stark_links h
  cases mp <;> cases a <;>
    simp only [Graph.modus, fGraph, fLab, Modus.stark, reduceCtorEq, if_false, if_true] at hs

theorem f_hb_in_po {mp : Bool} {a b : FenceEv} (h : (fGraph mp .rlx).hb a b) : fPo a b :=
  transGen_von_trans (f_wf mp .rlx).po_trans
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

theorem f_eco_schritt {mp : Bool} {a b : FenceEv} (h : (fGraph mp .rlx).ecoSchritt a b) :
    fEco a b := by
  rcases h with hrf | hmo | hrb
  · revert hrf
    show fRf mp a b → fEco a b
    cases mp <;> cases a <;> cases b <;> decide
  · revert hmo
    show fMo mp a b → fEco a b
    cases mp <;> cases a <;> cases b <;> decide
  · rcases hrb with ⟨w, h1, h2, hne⟩
    exact f_rb_eco mp w a b ⟨h1, h2, hne⟩

theorem f_eco {mp : Bool} {a b : FenceEv} (h : (fGraph mp .rlx).eco a b) : fEco a b :=
  transGen_von_trans (fun x y z hxy hyz => fEco_trans x y z ⟨hxy, hyz⟩)
    (transGen_mono (fun _ _ h => f_eco_schritt h) h)

/-- With `rlx` fences no event is `seq_cst`, so every `psc` edge is impossible. -/
theorem f_kein_psc (mp : Bool) (a b : FenceEv) : ¬ (fGraph mp .rlx).psc a b := by
  intro h
  have hs := Graph.psc_sc_links h
  cases mp <;> cases a <;>
    simp only [Graph.sc, Graph.modus, fGraph, fLab, reduceCtorEq, if_false, if_true] at hs

theorem f_psc_acyclisch (mp : Bool) : Azyklisch (fGraph mp .rlx).psc := by
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

theorem f_konsistent (mp : Bool) : (fGraph mp .rlx).Konsistent where
  wf := f_wf mp .rlx
  hb_irrefl := by
    intro a h
    exact (by cases a <;> decide : ¬ fPo a a) (f_hb_in_po h)
  kohaerent := by
    intro a b h he
    exact f_koh a b ⟨f_hb_in_po h, f_eco he⟩
  atomar := by
    intro w u w' hrf hu hmo
    cases mp <;> cases u <;>
      simp only [fGraph, fLab, Graph.istRmw, reduceCtorEq, if_false, if_true] at hu
  psc := f_psc_acyclisch mp
  ohneLB := by
    refine azyklisch_von_rang fRang ?_
    intro a b h
    revert h
    show (fPo a b ∨ fRf mp a b) → fRang a < fRang b
    cases mp <;> cases a <;> cases b <;> decide
  liest_vorher := by
    intro w u hrf hu
    cases mp <;> cases u <;>
      simp only [fGraph, fLab, Graph.istRmw, reduceCtorEq, if_false, if_true] at hu

theorem f_vollstaendig (mp : Bool) : (fGraph mp .rlx).Vollstaendig := by
  intro r hr
  cases mp <;> cases r <;>
    simp only [Graph.liest, fGraph, fLab, Art.liest, reduceCtorEq, if_false, if_true] at hr
  · exact ⟨iy, (by show fRf false iy b1; decide)⟩
  · exact ⟨ix, (by show fRf false ix b2; decide)⟩
  · exact ⟨b1, (by show fRf true b1 a2; decide)⟩
  · exact ⟨ix, (by show fRf true ix b2; decide)⟩

theorem f_rb_b1_a2 : (fGraph false .rlx).rb b1 a2 :=
  ⟨iy, (by show fRf false iy b1; decide), (by show fMo false iy a2; decide), by decide⟩

theorem f_rb_b2_a1 (mp : Bool) : (fGraph mp .rlx).rb b2 a1 := by
  cases mp
  · exact ⟨ix, (by show fRf false ix b2; decide), (by show fMo false ix a1; decide), by decide⟩
  · exact ⟨ix, (by show fRf true ix b2; decide), (by show fMo true ix a1; decide), by decide⟩

/-- **SC fences forbid store buffering.** No consistent graph has two relaxed writes, each followed
    by an `sc` fence and a relaxed read, with both reads missing the other thread's write
    (`r1 = r2 = 0`). The two fences are related in both directions by `pscZaun`, which contradicts
    the acyclicity of `psc`. -/
def ScFencesSbVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ wx f₁ rx wy f₂ ry ix iy : E,
        G.modus wx = .rlx ∧ G.modus rx = .rlx ∧ G.modus wy = .rlx ∧ G.modus ry = .rlx ∧
        G.istZaun f₁ ∧ G.sc f₁ ∧ G.istZaun f₂ ∧ G.sc f₂ ∧
        G.po wx f₁ ∧ G.po f₁ rx ∧ G.po wy f₂ ∧ G.po f₂ ry ∧
        G.rf iy rx ∧ G.rf ix ry ∧ G.rb rx wy ∧ G.rb ry wx

theorem sc_fences_sb_verboten : ScFencesSbVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, wx, f₁, rx, wy, f₂, ry, ix, iy,
    hmwx, hmrx, hmwy, hmry, hzf₁, hsf₁, hzf₂, hsf₂, p₁, p₂, p₃, p₄, rf₁, rf₂, rb₁, rb₂⟩
  have hza₁ : G.istSCZaun f₁ := ⟨hzf₁, hsf₁⟩
  have hza₂ : G.istSCZaun f₂ := ⟨hzf₂, hsf₂⟩
  have h₁₂ : G.psc f₁ f₂ :=
    Or.inr ⟨hza₁, hza₂, Or.inr ⟨rx, wy, G.hb_von_po p₂, G.eco_von_rb rb₁, G.hb_von_po p₃⟩⟩
  have h₂₁ : G.psc f₂ f₁ :=
    Or.inr ⟨hza₂, hza₁, Or.inr ⟨ry, wx, G.hb_von_po p₄, G.eco_von_rb rb₂, G.hb_von_po p₁⟩⟩
  exact hk.psc f₁ ((Relation.TransGen.single h₁₂).tail h₂₁)

/-- **The relaxed counterpart is allowed:** a consistent and complete graph with two `rlx` fences
    has both reads miss the other thread's write. The fences do not order because their mode is
    `rlx`; the refusal above is due to the `sc` mode alone. -/
def ScFencesSbErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wx f₁ rx wy f₂ ry ix iy : E,
        G.modus wx = .rlx ∧ G.modus rx = .rlx ∧ G.modus wy = .rlx ∧ G.modus ry = .rlx ∧
        G.istZaun f₁ ∧ G.modus f₁ = .rlx ∧ G.istZaun f₂ ∧ G.modus f₂ = .rlx ∧
        G.po wx f₁ ∧ G.po f₁ rx ∧ G.po wy f₂ ∧ G.po f₂ ry ∧
        G.rf iy rx ∧ G.rf ix ry ∧ G.rb rx wy ∧ G.rb ry wx

theorem sc_fences_sb_erlaubt : ScFencesSbErlaubtAussage := by
  refine ⟨FenceEv, Bool, Nat, fGraph false .rlx, f_konsistent false, f_vollstaendig false,
    a1, f1, b1, a2, f2, b2, ix, iy, ?_⟩
  exact ⟨(by show (fGraph false .rlx).modus a1 = .rlx; decide),
    (by show (fGraph false .rlx).modus b1 = .rlx; decide),
    (by show (fGraph false .rlx).modus a2 = .rlx; decide),
    (by show (fGraph false .rlx).modus b2 = .rlx; decide),
    (by show (fLab false .rlx f1).art = .zaun; rfl),
    (by show (fGraph false .rlx).modus f1 = .rlx; decide),
    (by show (fLab false .rlx f2).art = .zaun; rfl),
    (by show (fGraph false .rlx).modus f2 = .rlx; decide),
    (by show fPo a1 f1; decide), (by show fPo f1 b1; decide),
    (by show fPo a2 f2; decide), (by show fPo f2 b2; decide),
    (by show fRf false iy b1; decide), (by show fRf false ix b2; decide),
    f_rb_b1_a2, f_rb_b2_a1 false⟩

/-- **SC fences forbid message passing.** No consistent graph has a relaxed data write, an `sc`
    fence, a relaxed flag write, a relaxed flag read that sees it, an `sc` fence and a relaxed data
    read that sees the initial value (`flag seen, data stale`). The first fence reaches the flag
    read through coherence, the second reaches the data write through `rb`, so `pscZaun` relates
    them in both directions. -/
def ScFencesMpVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ wd f₁ wf rf' f₂ rd id : E,
        G.modus wd = .rlx ∧ G.modus wf = .rlx ∧ G.modus rf' = .rlx ∧ G.modus rd = .rlx ∧
        G.istZaun f₁ ∧ G.sc f₁ ∧ G.istZaun f₂ ∧ G.sc f₂ ∧
        G.po wd f₁ ∧ G.po f₁ wf ∧ G.po rf' f₂ ∧ G.po f₂ rd ∧
        G.rf wf rf' ∧ G.rf id rd ∧ G.rb rd wd

theorem sc_fences_mp_verboten : ScFencesMpVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, wd, f₁, wf, rf', f₂, rd, id,
    hmwd, hmwf, hmrf, hmrd, hzf₁, hsf₁, hzf₂, hsf₂, p₁, p₂, p₃, p₄, rf₁, rf₂, rb⟩
  have hza₁ : G.istSCZaun f₁ := ⟨hzf₁, hsf₁⟩
  have hza₂ : G.istSCZaun f₂ := ⟨hzf₂, hsf₂⟩
  have h₁₂ : G.psc f₁ f₂ :=
    Or.inr ⟨hza₁, hza₂, Or.inr ⟨wf, rf', G.hb_von_po p₂, G.eco_von_rf rf₁, G.hb_von_po p₃⟩⟩
  have h₂₁ : G.psc f₂ f₁ :=
    Or.inr ⟨hza₂, hza₁, Or.inr ⟨rd, wd, G.hb_von_po p₄, G.eco_von_rb rb, G.hb_von_po p₁⟩⟩
  exact hk.psc f₁ ((Relation.TransGen.single h₁₂).tail h₂₁)

/-- **The relaxed counterpart is allowed:** a consistent and complete graph with two `rlx` fences
    has the flag read see the flag write while the data read sees the initial write. -/
def ScFencesMpErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧ G.Vollstaendig ∧
      ∃ wd f₁ wf rf' f₂ rd id : E,
        G.modus wd = .rlx ∧ G.modus wf = .rlx ∧ G.modus rf' = .rlx ∧ G.modus rd = .rlx ∧
        G.istZaun f₁ ∧ G.modus f₁ = .rlx ∧ G.istZaun f₂ ∧ G.modus f₂ = .rlx ∧
        G.po wd f₁ ∧ G.po f₁ wf ∧ G.po rf' f₂ ∧ G.po f₂ rd ∧
        G.rf wf rf' ∧ G.rf id rd ∧ G.rb rd wd

theorem sc_fences_mp_erlaubt : ScFencesMpErlaubtAussage := by
  refine ⟨FenceEv, Bool, Nat, fGraph true .rlx, f_konsistent true, f_vollstaendig true,
    a1, f1, b1, a2, f2, b2, ix, ?_⟩
  exact ⟨(by show (fGraph true .rlx).modus a1 = .rlx; decide),
    (by show (fGraph true .rlx).modus b1 = .rlx; decide),
    (by show (fGraph true .rlx).modus a2 = .rlx; decide),
    (by show (fGraph true .rlx).modus b2 = .rlx; decide),
    (by show (fLab true .rlx f1).art = .zaun; rfl),
    (by show (fGraph true .rlx).modus f1 = .rlx; decide),
    (by show (fLab true .rlx f2).art = .zaun; rfl),
    (by show (fGraph true .rlx).modus f2 = .rlx; decide),
    (by show fPo a1 f1; decide), (by show fPo f1 b1; decide),
    (by show fPo a2 f2; decide), (by show fPo f2 b2; decide),
    (by show fRf true b1 a2; decide), (by show fRf true ix b2; decide),
    f_rb_b2_a1 true⟩

/-- **The SC-fence group root:** each forbidden half and its `rlx`-fence counterpart, joined by
    conjunction. This root is now a conjunct of `LitmusKatalogAussage`. -/
def ScFencesLitmusAussage : Prop :=
  (ScFencesSbVerbotenAussage ∧ ScFencesSbErlaubtAussage) ∧
  (ScFencesMpVerbotenAussage ∧ ScFencesMpErlaubtAussage)

theorem sc_fences_litmus : ScFencesLitmusAussage :=
  ⟨⟨sc_fences_sb_verboten, sc_fences_sb_erlaubt⟩,
    ⟨sc_fences_mp_verboten, sc_fences_mp_erlaubt⟩⟩

end Gabbro.Core.Speicher
