/-
  File:      core/Core/Speicher/Atom/NutzlastSchwach.lean
  Subject:   THE PAYLOAD STATEMENT IS NOT TRIVIAL (MK-04): with a flag mode that is too weak the observer can read
             a stale payload, and the memory model represents that run. The graph is message passing: thread 1
             writes the plain payload `x := 1`, then the flag `y := 1` in the mode `mw`; thread 2 reads the flag `1`
             in the mode `mr`, then reads the payload `x` and takes the INITIAL value `0`. It is consistent
             whenever `mw` and `mr` are not both at least release/acquire (`stGraph_konsistent`): then no
             synchronises-with edge exists, the payload write does not happen before the payload read, and
             coherence has nothing to forbid. The instructions `veroeffentliche` and `erwarte` carry their mode
             (`Atom/Form`), so a relaxed publication IS an instruction of the model; the checker's refusal of it is
             what excludes this run (`payloadSichtbar_nichtTrivial`).
-/
module

public import Core.Speicher.Atom.Nutzlast

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Atom

/-- The events: the two initial writes, thread 1 `wx; wy`, thread 2 `ry; rx`. -/
inductive StEv where
  | ix
  | iy
  | wx
  | wy
  | ry
  | rx
  deriving DecidableEq, Repr

open StEv

/-- Location `false` is the plain payload `x`, `true` the flag `y` in the modes `mw` (write) and `mr` (read). -/
def stLab (mw mr : Modus) : StEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, .na, 0, 0⟩
  | iy => ⟨.schreiben, true, .na, 0, 0⟩
  | wx => ⟨.schreiben, false, .na, 0, 1⟩
  | wy => ⟨.schreiben, true, mw, 0, 1⟩
  | ry => ⟨.lesen, true, mr, 1, 0⟩
  | rx => ⟨.lesen, false, .na, 0, 0⟩

@[reducible] def stPo (a b : StEv) : Prop := (a = wx ∧ b = wy) ∨ (a = ry ∧ b = rx)

/-- The flag is read from the flag write; the payload read takes the initial payload. -/
@[reducible] def stRf (a b : StEv) : Prop := (a = wy ∧ b = ry) ∨ (a = ix ∧ b = rx)

@[reducible] def stMo (a b : StEv) : Prop := (a = ix ∧ b = wx) ∨ (a = iy ∧ b = wy)

/-- The extended coherence order of this graph. -/
@[reducible] def stEco (a b : StEv) : Prop :=
  (a = ix ∧ (b = wx ∨ b = rx)) ∨ (a = iy ∧ (b = wy ∨ b = ry)) ∨ (a = wy ∧ b = ry) ∨ (a = rx ∧ b = wx)

/-- The location of an event, independent of the flag modes. -/
def stOrt : StEv → Bool
  | ix => false
  | iy => true
  | wx => false
  | wy => true
  | ry => true
  | rx => false

theorem stLab_ort (mw mr : Modus) (a : StEv) : (stLab mw mr a).ort = stOrt a := by
  cases a <;> rfl

def stRang : StEv → Nat
  | ix => 0
  | iy => 1
  | wx => 2
  | wy => 3
  | ry => 4
  | rx => 5

def stGraph (mw mr : Modus) : Graph StEv Bool Nat := ⟨stLab mw mr, stPo, stRf, stMo⟩

theorem stGraph_wf (mw mr : Modus) : (stGraph mw mr).Wohlgeformt where
  po_trans := by
    intro a b c
    show stPo a b → stPo b c → stPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ stPo a a
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
    show stMo a b → stMo b c → stMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ stMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    show stMo a b ∨ stMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha
        | exact False.elim hb
        | exact absurd rfl hne
        | (simp only [Graph.ort, stGraph, stLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)
  rmw_nicht_na := by
    intro a h
    cases a <;> simp only [Graph.istRmw, stGraph, stLab, reduceCtorEq] at h

theorem stGraph_kein_rmw (mw mr : Modus) (u : StEv) : ¬ (stGraph mw mr).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, stGraph, stLab, reduceCtorEq] at hu

/-- The stale-payload graph has no fences. -/
theorem stGraph_kein_zaun (mw mr : Modus) (u : StEv) : ¬ (stGraph mw mr).istZaun u := by
  intro hu
  cases u <;> simp only [Graph.istZaun, stGraph, stLab, reduceCtorEq] at hu

/-- With the flag modes not both at least release/acquire, nothing synchronises. -/
theorem stGraph_kein_sw {mw mr : Modus} (h : ¬ (mw.stark ∧ mr.stark)) {a b : StEv} :
    ¬ (stGraph mw mr).sw a b := by
  intro hsw
  obtain ⟨_, hma, _, hmb, x, hrs, hrf⟩ :=
    Graph.sw_klassisch (stGraph_kein_zaun mw mr a) (stGraph_kein_zaun mw mr b) hsw
  have hx := Graph.Rs.ohne_rmw (stGraph_kein_rmw mw mr) hrs
  have hrf' : stRf x b := hrf
  rcases hrf' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hmr : mr.stark := hmb
    rcases hx with rfl | hpo
    · exact h ⟨hma, hmr⟩
    · have hpo' : stPo a wy := hpo
      rcases hpo' with ⟨rfl, _⟩ | ⟨_, h2⟩
      · exact hma
      · cases h2
  · exact hmb

theorem stGraph_hb {mw mr : Modus} (h : ¬ (mw.stark ∧ mr.stark)) {a b : StEv}
    (hab : (stGraph mw mr).hb a b) : stPo a b := by
  have htr : ∀ x y z, stPo x y → stPo y z → stPo x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) hab)
  rcases hxy with hpo | hsw
  · exact hpo
  · exact (stGraph_kein_sw h hsw).elim

theorem stGraph_rb {mw mr : Modus} {r w : StEv} (h : (stGraph mw mr).rb r w) : r = rx ∧ w = wx := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show stRf w' r → stMo w' w → r = rx ∧ w = wx
  cases w' <;> cases r <;> cases w <;> decide

theorem stGraph_eco {mw mr : Modus} {a b : StEv} (h : (stGraph mw mr).eco a b) : stEco a b := by
  have htr : ∀ x y z, stEco x y → stEco y z → stEco x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) h)
  rcases hxy with h | h | h
  · revert h
    show stRf x y → stEco x y
    cases x <;> cases y <;> decide
  · revert h
    show stMo x y → stEco x y
    cases x <;> cases y <;> decide
  · obtain ⟨rfl, rfl⟩ := stGraph_rb h
    decide

/-- The SC base of this graph only relates events of which one is a plain access. -/
theorem stGraph_scb {mw mr : Modus} (h : ¬ (mw.stark ∧ mr.stark)) {a b : StEv}
    (hs : (stGraph mw mr).scb a b) :
    (a = wx ∧ b = wy) ∨ (a = ry ∧ b = rx) ∨ (a = ix ∧ b = wx) ∨ (a = iy ∧ b = wy) ∨ (a = rx ∧ b = wx) := by
  rcases hs with hpo | ⟨c, d, h1, _, h3, h4, _⟩ | ⟨h1, h2⟩ | hmo | hrb
  · rcases (hpo : stPo a b) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exfalso
    have h1' : stPo a c := h1
    have h3' := stGraph_hb h h3
    revert h1' h3'
    cases a <;> cases c <;> cases d <;> decide
  · exfalso
    have h1' := stGraph_hb h h1
    have h2' : stOrt a = stOrt b := by
      rw [← stLab_ort mw mr a, ← stLab_ort mw mr b]
      exact h2
    revert h1' h2'
    cases a <;> cases b <;> decide
  · rcases (hmo : stMo a b) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  · obtain ⟨h1, h2⟩ := stGraph_rb hrb
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))

/-- **No two events of this graph are related by `psc`**: of every pair the SC base relates, one is a plain access. -/
theorem stGraph_psc {mw mr : Modus} (h : ¬ (mw.stark ∧ mr.stark)) {a b : StEv}
    (hp : (stGraph mw mr).psc a b) : False := by
  rcases hp with ⟨c, d, hscb, hl, hr⟩ | ⟨hza, _, _⟩
  · rcases hl with ⟨ha, hac⟩ | ⟨hza, _⟩
    · rcases hr with ⟨hb, hdb⟩ | ⟨hzb, _⟩
      · have ha' : (stLab mw mr a).modus = .sc := ha
        have hb' : (stLab mw mr b).modus = .sc := hb
        subst hac
        subst hdb
        rcases stGraph_scb h hscb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd ha' (by intro hh; cases hh)
        · exact absurd hb' (by intro hh; cases hh)
        · exact absurd ha' (by intro hh; cases hh)
        · exact absurd ha' (by intro hh; cases hh)
        · exact absurd ha' (by intro hh; cases hh)
      · exact absurd hzb.1 (stGraph_kein_zaun mw mr _)
    · exact absurd hza.1 (stGraph_kein_zaun mw mr _)
  · exact absurd hza.1 (stGraph_kein_zaun mw mr _)

theorem stGraph_konsistent {mw mr : Modus} (h : ¬ (mw.stark ∧ mr.stark)) :
    (stGraph mw mr).Konsistent where
  wf := stGraph_wf mw mr
  hb_irrefl := by
    intro a hh
    have hp := stGraph_hb h hh
    revert hp
    cases a <;> decide
  kohaerent := by
    intro a b h1 h2
    have hp := stGraph_hb h h1
    have he := stGraph_eco h2
    revert hp he
    cases a <;> cases b <;> decide
  atomar := fun _ u _ _ hu _ => absurd hu (stGraph_kein_rmw mw mr u)
  liest_vorher := fun _ u _ hu => absurd hu (stGraph_kein_rmw mw mr u)
  psc := fun a hh => by
    obtain ⟨_, hk⟩ := transGen_kopf hh
    exact stGraph_psc h hk
  ohneLB := by
    refine azyklisch_von_rang stRang ?_
    intro a b
    show stPo a b ∨ stRf a b → stRang a < stRang b
    cases a <;> cases b <;> decide

end Atom

/-- **The payload statement is not trivial.** For every pair of flag modes that are not both at least
    release/acquire, there is a consistent graph with a publication and an observation that reads it, in which
    the observer's payload read takes a write OLDER than the published payload write. Dropping the mode premises of
    `PayloadSichtbarAussage` makes it false, and the graph is a run of the model: an instruction of the model with a
    weak mode is the instruction the checker refuses. -/
theorem payloadSichtbar_nichtTrivial (mw mr : Modus) (h : ¬ (mw.stark ∧ mr.stark)) :
    ∃ (G : Graph Atom.StEv Bool Nat), G.Konsistent ∧
      ∃ p w r q s : Atom.StEv, G.po p w ∧ G.schreibt p ∧ G.rf w r ∧ G.modus w = mw ∧ G.modus r = mr ∧
        G.po r q ∧ G.ort p = G.ort q ∧ G.rf s q ∧ ¬ (p = s ∨ G.mo p s) := by
  refine ⟨Atom.stGraph mw mr, Atom.stGraph_konsistent h, .wx, .wy, .ry, .rx, .ix,
    Or.inl ⟨rfl, rfl⟩, trivial, Or.inl ⟨rfl, rfl⟩, rfl, rfl, Or.inr ⟨rfl, rfl⟩, rfl,
    Or.inr ⟨rfl, rfl⟩, ?_⟩
  rintro (e | hmo)
  · cases e
  · rcases (hmo : Atom.stMo .wx .ix) with ⟨e, _⟩ | ⟨e, _⟩ <;> cases e

end Gabbro.Core.Speicher
