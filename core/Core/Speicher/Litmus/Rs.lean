/-
  File:      core/Core/Speicher/Litmus/Rs.lean
  Subject:   RELEASE SEQUENCE catalogue entry: a relaxed read-modify-write that reads from a
             release write continues that write's release sequence, so a later acquire read of
             the update's write synchronises with the release and sees the preceding data write.
             The allowed half keeps the same data outcome but has the update read an unrelated
             relaxed write, so it does not extend the release sequence.

  Source: Lahav, Vafeiadis, Kang, Hur, Dreyer, "Repairing Sequential Consistency in C/C++11"
  (PLDI 2017), §3.2, `rs = [W]; sb|loc?; [W ⊒ rlx]; (rf; rmw)*` and `sw`; §7, "eliminating an
  acquire read after a relaxed update may remove the synchronization due to a release sequence
  ending in this update". The same `rs` appears in herd's `rc11.cat`. Batty et al. (POPL 2011)
  supply the message-passing shape; the herd/cpp catalogue names the contrasting test
  `mp-rs-add-est-atomic`.
  Modes: FORBIDDEN with the flag write release and the flag read acquire (`Modus.stark`, i.e.
  `.ra` or `.sc`); the extending update is `.rlx`; ALLOWED with the same two strong modes but the
  update reading from a plain `.rlx` write outside the release sequence.
  Expected: FORBIDDEN when the rlx-RMW carries the release; ALLOWED when it does not.
-/
module

public import Core.Speicher.Trennung
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **A relaxed RMW extends a release sequence: the stale data read is forbidden.** A release
    flag write `wf` is preceded by the data write `wd`; an update `u` reads from `wf`; an acquire
    read `r` reads from `u` and is followed by a data read `rd` that reads before `wd` in `rb`.
    Then `Rs.rmw` puts `u` in `wf`'s release sequence, `sw wf r` holds and `hb ; eco?` is cyclic. -/
def RsVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ ∃ wd wf u r rd : E,
      G.po wd wf ∧ (G.modus wf).stark ∧ G.rf wf u ∧ G.istRmw u ∧
        G.rf u r ∧ (G.modus r).stark ∧ G.po r rd ∧ G.rb rd wd

theorem rs_verboten_kat : RsVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, wd, wf, u, r, rd, p1, hf, hrf1, hu, hrf2, hr, p2, hrb⟩
  have hwf : G.schreibt wf := hk.wf.rf_schreibt wf u hrf1
  have hrs1 : G.Rs wf wf := Graph.Rs.selbst hwf (Modus.stark_atomar hf)
  have hrs : G.Rs wf u := Graph.Rs.rmw hrs1 hrf1 hu
  have hl : G.liest r := hk.wf.rf_liest u r hrf2
  have hsw : G.sw wf r := by
    apply Graph.sw_von_klassisch
    exact ⟨hwf, hf, hl, hr, u, hrs, hrf2⟩
  have hhb : G.hb wd rd :=
    G.hb_trans (G.hb_trans (G.hb_von_po p1) (G.hb_von_sw hsw)) (G.hb_von_po p2)
  exact hk.kohaerent wd rd hhb (G.eco_von_rb hrb)

/-- The nine events: initial data and flag writes, the data/flag writes of thread 0, a relaxed
    flag write of another thread, the relaxed update, the acquire reader and its data read. -/
inductive RelEv where
  | ix
  | iy
  | wd
  | wf
  | w3
  | u
  | r
  | rd
  deriving DecidableEq, Repr

open RelEv

/-- Location `false` is the data cell, `true` the flag. `wf` is the release write (value `1`),
    `w3` an unrelated relaxed write of the same value, `u` the relaxed update reading `1` and
    writing `2`, `r` the acquire read of `2`, `rd` the data read of the initial `0`. -/
def rsLab : RelEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, .rlx, 0, 0⟩
  | iy => ⟨.schreiben, true, .rlx, 0, 0⟩
  | wd => ⟨.schreiben, false, .rlx, 0, 1⟩
  | wf => ⟨.schreiben, true, .ra, 0, 1⟩
  | w3 => ⟨.schreiben, true, .rlx, 0, 1⟩
  | u => ⟨.rmw, true, .rlx, 1, 2⟩
  | r => ⟨.lesen, true, .ra, 2, 0⟩
  | rd => ⟨.lesen, false, .rlx, 0, 0⟩

/-- Initial writes precede every other event; thread 0 is `wd ; wf`, the reader thread is
    `r ; rd`. There is no order from `wf` to `w3` or `u`, so the release sequence stops at `wf`. -/
@[reducible] def rsPo (a b : RelEv) : Prop :=
  (a = ix ∧ b ≠ ix) ∨
  (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨
  (a = wd ∧ b = wf) ∨
  (a = r ∧ b = rd)

/-- `rd` reads the initial data, `u` reads the unrelated relaxed write `w3`, `r` reads `u`. -/
@[reducible] def rsRf (a b : RelEv) : Prop :=
  (a = ix ∧ b = rd) ∨ (a = w3 ∧ b = u) ∨ (a = u ∧ b = r)

/-- Modification order: `ix < wd` and `iy < wf < w3 < u`. -/
@[reducible] def rsMo (a b : RelEv) : Prop :=
  (a = ix ∧ b = wd) ∨
    (a = iy ∧ (b = wf ∨ b = w3 ∨ b = u)) ∨
      (a = wf ∧ (b = w3 ∨ b = u)) ∨
        (a = w3 ∧ b = u)

/-- The closure of `rf ∪ mo ∪ rb` in this graph. -/
@[reducible] def rsEco (a b : RelEv) : Prop :=
  (a = ix ∧ (b = wd ∨ b = rd)) ∨
    (a = iy ∧ (b = wf ∨ b = w3 ∨ b = u ∨ b = r)) ∨
      (a = wf ∧ (b = w3 ∨ b = u ∨ b = r)) ∨
        (a = w3 ∧ (b = u ∨ b = r)) ∨
          (a = u ∧ b = r) ∨
            (a = rd ∧ b = wd)

def rsGraph : Graph RelEv Bool Nat := ⟨rsLab, rsPo, rsRf, rsMo⟩

abbrev rsSchreibt (a : RelEv) : Prop := (rsLab a).art.schreibt
abbrev rsLiest (a : RelEv) : Prop := (rsLab a).art.liest
abbrev rsIstRmw (a : RelEv) : Prop := (rsLab a).art = .rmw
abbrev rsOrt (a : RelEv) : Bool := (rsLab a).ort

theorem rsWf : rsGraph.Wohlgeformt where
  po_trans := by
    intro a b c
    show rsPo a b → rsPo b c → rsPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ rsPo a a
    cases a <;> decide
  rf_schreibt := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_liest := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_ort := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_wert := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_eindeutig := by
    intro a b c h1 h2
    revert h1 h2
    show rsRf a c → rsRf b c → a = b
    cases a <;> cases b <;> cases c <;> decide
  mo_schreibt := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, (rfl | rfl | rfl)⟩ | ⟨rfl, (rfl | rfl)⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨trivial, trivial⟩
  mo_ort := by
    rintro _ _ (⟨rfl, rfl⟩ | ⟨rfl, (rfl | rfl | rfl)⟩ | ⟨rfl, (rfl | rfl)⟩ | ⟨rfl, rfl⟩) <;>
      rfl
  mo_trans := by
    intro a b c
    show rsMo a b → rsMo b c → rsMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ rsMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    have ha' : rsSchreibt a := ha
    have hb' : rsSchreibt b := hb
    have ho' : rsOrt a = rsOrt b := ho
    show rsMo a b ∨ rsMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha'
        | exact False.elim hb'
        | exact False.elim (hne rfl)
        | (simp only [rsOrt, rsLab, Bool.false_eq_true, Bool.true_eq_false] at ho'; done)

/-- The only `rb` edge is from the stale data read to the data write. -/
theorem rsRb {r w : RelEv} (h : rsGraph.rb r w) : r = rd ∧ w = wd := by
  rcases h with ⟨w', h1, h2, hne⟩
  revert h1 h2 hne
  show rsRf w' r → rsMo w' w → r ≠ w → (r = rd ∧ w = wd)
  cases w' <;> cases r <;> cases w <;> decide

theorem rsEcoTrans (a b c : RelEv) : rsEco a b → rsEco b c → rsEco a c := by
  intro hxy hyz
  cases a <;> cases b <;> cases c <;>
    simp only [rsEco, reduceCtorEq, and_true, true_and, and_false, false_and, or_true, true_or,
      or_false, false_or, not_false_eq_true] at hxy hyz ⊢

theorem rsEcoSchritt (a b : RelEv) (h : rsGraph.ecoSchritt a b) : rsEco a b := by
  rcases h with h | h | h
  · revert h
    show rsRf a b → rsEco a b
    cases a <;> cases b <;> decide
  · revert h
    show rsMo a b → rsEco a b
    cases a <;> cases b <;> decide
  · rcases rsRb h with ⟨rfl, rfl⟩
    decide

theorem rsEcoVonEco {a b : RelEv} (h : rsGraph.eco a b) : rsEco a b :=
  transGen_von_trans rsEcoTrans (transGen_mono (fun _ _ h' => rsEcoSchritt _ _ h') h)

/-- The release write `wf` is the only event that is both a stark write; the acquire read `r`
    is the only stark read. -/
theorem rsStarkSchreibt (a : RelEv) (hsch : rsGraph.schreibt a)
    (hst : (rsGraph.modus a).stark) : a = wf := by
  cases a <;>
    simp only [Graph.schreibt, Graph.modus, rsGraph, rsLab, Art.schreibt, Modus.stark] at hsch hst ⊢

theorem rsStarkLiest (b : RelEv) (hl : rsGraph.liest b)
    (hst : (rsGraph.modus b).stark) : b = r := by
  cases b <;>
    simp only [Graph.liest, Graph.modus, rsGraph, rsLab, Art.liest, Modus.stark] at hl hst ⊢

/-- The release sequence headed by `wf` contains only `wf`: no `po` successor of `wf` writes
    the flag, and no update reads from `wf`. -/
theorem rsRsWfNur (x : RelEv) (h : rsGraph.Rs wf x) : x = wf := by
  induction h with
  | selbst _ => rfl
  | po _ hpo _ _ _ =>
      exfalso
      rcases hpo with ⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> cases h1
  | rmw _ hrf _ ih =>
      rw [ih] at hrf
      exfalso
      rcases hrf with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> cases h1

theorem rs_kein_zaun (a : RelEv) : ¬ rsGraph.istZaun a := by
  intro ha
  cases a <;> simp only [Graph.istZaun, rsGraph, rsLab, reduceCtorEq] at ha

/-- The update does not read from the release write, so no `sw` edge exists in this graph. -/
theorem rsKeinSw (a b : RelEv) : ¬ rsGraph.sw a b := by
  intro h
  obtain ⟨hsch, hst, hl, hstb, x, hrs, hrf⟩ :=
    Graph.sw_klassisch (rs_kein_zaun a) (rs_kein_zaun b) h
  have ha : a = wf := rsStarkSchreibt a hsch hst
  have hb : b = r := rsStarkLiest b hl hstb
  subst a
  subst b
  have hx : x = u := by
    revert hrf
    show rsRf x r → x = u
    cases x <;> decide
  subst x
  have hwu : u = wf := rsRsWfNur u hrs
  cases hwu

theorem rsPoTrans (a b c : RelEv) : rsPo a b → rsPo b c → rsPo a c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Happens-before is program order: `sw` is empty and `po` is transitive. -/
theorem rsHb {a b : RelEv} (h : rsGraph.hb a b) : rsPo a b := by
  have schritt : ∀ x y, rsGraph.hbSchritt x y → rsPo x y := by
    intro x y hxy
    rcases hxy with hp | hsw
    · exact hp
    · exact False.elim (rsKeinSw x y hsw)
  exact transGen_von_trans rsPoTrans (transGen_mono schritt h)

theorem rsKoh (a b : RelEv) : rsPo a b → rsEco b a → False := by
  cases a <;> cases b <;> decide

def rsRang : RelEv → Nat
  | ix => 0
  | iy => 1
  | wd => 2
  | wf => 3
  | w3 => 2
  | u => 3
  | r => 4
  | rd => 5

theorem rsKonsistent : rsGraph.Konsistent where
  wf := rsWf
  hb_irrefl := by
    intro a h
    have hp := rsHb h
    revert hp
    cases a <;> decide
  kohaerent := by
    intro a b hab he
    exact rsKoh a b (rsHb hab) (rsEcoVonEco he)
  atomar := by
    intro w u w' hrf _ hmo
    revert hrf hmo
    show rsRf w u → rsMo w w' → ¬ rsMo w' u
    cases w <;> cases u <;> cases w' <;> decide
  psc := by
    intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    have hsc : rsGraph.sc a := Graph.psc_sc_links hc
    cases a <;> simp only [Graph.sc, Graph.modus, rsGraph, rsLab, reduceCtorEq] at hsc
  ohneLB := by
    refine azyklisch_von_rang rsRang ?_
    intro a b h
    rcases h with hp | hrf
    · revert hp
      show rsPo a b → rsRang a < rsRang b
      cases a <;> cases b <;> decide
    · revert hrf
      show rsRf a b → rsRang a < rsRang b
      cases a <;> cases b <;> decide
  liest_vorher := by
    intro w u hrf hu
    have hu' : rsIstRmw u := hu
    revert hrf hu'
    show rsRf w u → rsIstRmw u → rsMo w u
    cases w <;> cases u <;> decide

/-- Every read has a source, including the stale data read. -/
theorem rsVollstaendig : rsGraph.Vollstaendig := by
  intro a ha
  cases a with
  | ix => exact (ha : False).elim
  | iy => exact (ha : False).elim
  | wd => exact (ha : False).elim
  | wf => exact (ha : False).elim
  | w3 => exact (ha : False).elim
  | u => exact ⟨w3, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  | r => exact ⟨u, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  | rd => exact ⟨ix, Or.inl ⟨rfl, rfl⟩⟩

/-- **The release sequence stops at the release write: the stale data read is allowed.** The
    relaxed update reads the unrelated relaxed write, not `wf`, hence `¬ Rs wf u`. -/
def RsErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧ ∃ wd wf w3 u r rd : E,
      G.po wd wf ∧ (G.modus wf).stark ∧ G.rf w3 u ∧ G.istRmw u ∧
        G.rf u r ∧ (G.modus r).stark ∧ G.po r rd ∧ G.rb rd wd ∧ ¬ G.Rs wf u

theorem rs_erlaubt_kat : RsErlaubtAussage := by
  refine ⟨RelEv, Bool, Nat, rsGraph, rsKonsistent, rsVollstaendig, wd, wf, w3, u, r, rd,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · simp only [Graph.modus, rsGraph, rsLab, Modus.stark]
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rfl
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp only [Graph.modus, rsGraph, rsLab, Modus.stark]
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact ⟨ix, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, by decide⟩
  · intro hrs
    have hwu : u = wf := rsRsWfNur u hrs
    cases hwu

/-- **The release-sequence catalogue entry.** -/
def RsLitmusAussage : Prop := RsVerbotenAussage ∧ RsErlaubtAussage

theorem rs_litmus : RsLitmusAussage := ⟨rs_verboten_kat, rs_erlaubt_kat⟩

end Gabbro.Core.Speicher
