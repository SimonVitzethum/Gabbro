/-
  File:      core/Core/Speicher/Erfuellbar.lean
  Subject:   SATISFIABILITY of the premise bundle of `drf_sc` (AGENTS.md §3): a consistent graph with
              only `seq_cst` atomics and no race in which both premises bite -- a plain carrier with
              conflicting accesses and a `seq_cst` carrier (`drf_sc_erfuellbar`). The graph is
             message passing: thread 1 writes the plain `x := 1`, then the `seq_cst` flag
             `y := 1`; thread 2 reads the flag `1`, then reads `x = 1`. A second witness
             (`drf_sc_zaun_erfuellbar`) places a real `seq_cst` fence in program order between a
             plain write and its plain read and satisfies the premises with that fence present.
-/
module

public import Core.Speicher.Trennung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- The events: the two initial writes, thread 1 `wx; wy`, thread 2 `ry; rx`. -/
inductive MpEv where
  | ix
  | iy
  | wx
  | wy
  | ry
  | rx
  deriving DecidableEq, Repr

open MpEv

/-- Location `false` is the plain `x`, `true` the `seq_cst` flag `y`. -/
def mpLab : MpEv → Etikett Bool Nat
  | ix => ⟨.schreiben, false, .na, 0, 0⟩
  | iy => ⟨.schreiben, true, .sc, 0, 0⟩
  | wx => ⟨.schreiben, false, .na, 0, 1⟩
  | wy => ⟨.schreiben, true, .sc, 0, 1⟩
  | ry => ⟨.lesen, true, .sc, 1, 0⟩
  | rx => ⟨.lesen, false, .na, 1, 0⟩

@[reducible] def mpPo (a b : MpEv) : Prop :=
  (a = ix ∧ b ≠ ix) ∨ (a = iy ∧ b ≠ ix ∧ b ≠ iy) ∨ (a = wx ∧ b = wy) ∨ (a = ry ∧ b = rx)

@[reducible] def mpRf (a b : MpEv) : Prop := (a = wy ∧ b = ry) ∨ (a = wx ∧ b = rx)

@[reducible] def mpMo (a b : MpEv) : Prop := (a = ix ∧ b = wx) ∨ (a = iy ∧ b = wy)

/-- Happens-before of this graph: program order and thread 1 before thread 2. -/
@[reducible] def mpHb (a b : MpEv) : Prop :=
  mpPo a b ∨ ((a = wx ∨ a = wy) ∧ (b = ry ∨ b = rx))

/-- The extended coherence order of this graph. -/
@[reducible] def mpEco (a b : MpEv) : Prop :=
  (a = ix ∧ (b = wx ∨ b = rx)) ∨ (a = iy ∧ (b = wy ∨ b = ry)) ∨ (a = wx ∧ b = rx) ∨
    (a = wy ∧ b = ry)

def mpRang : MpEv → Nat
  | ix => 0
  | iy => 1
  | wx => 2
  | wy => 3
  | ry => 4
  | rx => 5

def mpGraph : Graph MpEv Bool Nat := ⟨mpLab, mpPo, mpRf, mpMo⟩

theorem mp_wf : mpGraph.Wohlgeformt where
  po_trans := by
    intro a b c
    show mpPo a b → mpPo b c → mpPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ mpPo a a
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
    show mpMo a b → mpMo b c → mpMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ mpMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    show mpMo a b ∨ mpMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha
        | exact False.elim hb
        | exact absurd rfl hne
        | (simp only [Graph.ort, mpGraph, mpLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)
  rmw_nicht_na := by
    intro a h
    cases a <;> simp only [Graph.istRmw, mpGraph, mpLab, reduceCtorEq] at h

theorem mp_kein_rmw (u : MpEv) : ¬ mpGraph.istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, mpGraph, mpLab, reduceCtorEq] at hu

/-- The message-passing graph has no fences. -/
theorem mp_kein_zaun (a : MpEv) : ¬ mpGraph.istZaun a := by
  intro hu
  cases a <;> simp only [Graph.istZaun, mpGraph, mpLab, reduceCtorEq] at hu

theorem mp_hb {a b : MpEv} (h : mpGraph.hb a b) : mpHb a b := by
  have htr : ∀ x y z, mpHb x y → mpHb y z → mpHb x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) h)
  rcases hxy with hpo | hsw
  · exact Or.inl hpo
  · obtain ⟨z, hz, hzy⟩ := Graph.sw_ohne_rmw mp_kein_zaun mp_kein_rmw hsw
    revert hz hzy
    show (x = z ∨ mpPo x z) → mpRf z y → mpHb x y
    cases x <;> cases z <;> cases y <;> decide

theorem mp_rb_leer {r w : MpEv} (h : mpGraph.rb r w) : False := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show mpRf w' r → mpMo w' w → False
  cases w' <;> cases r <;> cases w <;> decide

theorem mp_eco {a b : MpEv} (h : mpGraph.eco a b) : mpEco a b := by
  have htr : ∀ x y z, mpEco x y → mpEco y z → mpEco x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) h)
  rcases hxy with h | h | h
  · revert h
    show mpRf x y → mpEco x y
    cases x <;> cases y <;> decide
  · revert h
    show mpMo x y → mpEco x y
    cases x <;> cases y <;> decide
  · exact (mp_rb_leer h).elim

theorem mp_hb_rang {a b : MpEv} (h : mpHb a b) : mpRang a < mpRang b := by
  revert h
  cases a <;> cases b <;> decide

theorem mp_konsistent : mpGraph.Konsistent where
  wf := mp_wf
  hb_irrefl := by
    intro a h
    exact Nat.lt_irrefl _ (mp_hb_rang (mp_hb h))
  kohaerent := by
    intro a b h1 h2
    have hp := mp_hb h1
    have he := mp_eco h2
    revert hp he
    cases a <;> cases b <;> decide
  atomar := fun _ u _ _ hu _ => absurd hu (mp_kein_rmw u)
  liest_vorher := fun _ u _ hu => absurd hu (mp_kein_rmw u)
  psc := by
    refine azyklisch_von_rang mpRang (fun a b h => ?_)
    rcases h with ⟨c, d, hscb, hl, hr⟩ | ⟨hza, _, _⟩
    · rcases hl with ⟨_, hac⟩ | ⟨hza, _⟩
      · rcases hr with ⟨_, hdb⟩ | ⟨hzb, _⟩
        · subst hac
          subst hdb
          rcases hscb with h | ⟨x, y, h1, -, h3, h4, -⟩ | ⟨h1, -⟩ | h | h
          · exact mp_hb_rang (Or.inl h)
          · exact Nat.lt_trans (mp_hb_rang (Or.inl h1))
              (Nat.lt_trans (mp_hb_rang (mp_hb h3)) (mp_hb_rang (Or.inl h4)))
          · exact mp_hb_rang (mp_hb h1)
          · revert h
            show mpMo a d → mpRang a < mpRang d
            cases a <;> cases d <;> decide
          · exact (mp_rb_leer h).elim
        · exact absurd hzb.1 (mp_kein_zaun _)
      · exact absurd hza.1 (mp_kein_zaun _)
    · exact absurd hza.1 (mp_kein_zaun _)
  ohneLB := by
    refine azyklisch_von_rang mpRang ?_
    intro a b
    show mpPo a b ∨ mpRf a b → mpRang a < mpRang b
    cases a <;> cases b <;> decide

theorem mp_nur_sc : mpGraph.NurSC := by
  intro a
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The data write happens before the data read: through the `seq_cst` flag. -/
theorem mp_hb_wx_rx : mpGraph.hb wx rx :=
  mpGraph.hb_trans
    (mpGraph.hb_trans (mpGraph.hb_von_po (show mpPo wx wy by decide))
      (mpGraph.hb_von_sw (a := wy) (b := ry)
        ⟨wy, wy, ry, Or.inl ⟨rfl, trivial, trivial⟩, .selbst trivial trivial,
        show mpRf wy ry by decide, trivial, trivial, Or.inl ⟨rfl, trivial, trivial⟩⟩))
    (mpGraph.hb_von_po (show mpPo ry rx by decide))

theorem mp_rennfrei : mpGraph.Rennfrei := by
  rintro a b ⟨hne, ho, hw⟩ hna
  cases a <;> cases b <;>
    first
      | exact absurd rfl hne
      | exact Or.inl (mpGraph.hb_von_po (show mpPo _ _ by decide))
      | exact Or.inr (mpGraph.hb_von_po (show mpPo _ _ by decide))
      | exact Or.inl mp_hb_wx_rx
      | exact Or.inr mp_hb_wx_rx
      | (simp only [Graph.ort, mpGraph, mpLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)
      | (simp only [Graph.na, Graph.modus, mpGraph, mpLab, reduceCtorEq, or_self] at hna; done)
      | (simp only [Graph.schreibt, mpGraph, mpLab, Art.schreibt, or_self] at hw; done)

/-- **Satisfiability of the premises of `drf_sc`**: a consistent graph with only `seq_cst`
    atomics and no race, containing a `seq_cst` access and a conflicting pair on a plain carrier. -/
theorem drf_sc_erfuellbar :
    ∃ G : Graph MpEv Bool Nat, G.Konsistent ∧ G.NurSC ∧ G.Rennfrei ∧ (∃ a, G.sc a) ∧
    ∃ a b, G.Konflikt a b ∧ G.na a ∧ G.na b :=
  ⟨mpGraph, mp_konsistent, mp_nur_sc, mp_rennfrei, ⟨wy, rfl⟩,
    wx, rx, ⟨by decide, rfl, Or.inl trivial⟩, rfl, rfl⟩

/-- The events of the fenced witness: the initial writes, a plain write/read pair with a real
    `seq_cst` fence in between, and a `seq_cst` write. -/
inductive ZfEv where
  | zix | ziy | zwx | zfz | zrx
  deriving DecidableEq, Repr

open ZfEv

/-- Location `false` is the plain `x`, `true` the `seq_cst` carrier `y`. The fence is an
    `Art.zaun` event of mode `sc`; it neither reads nor writes. -/
def zfLab : ZfEv → Etikett Bool Nat
  | zix => ⟨.schreiben, false, .na, 0, 0⟩
  | ziy => ⟨.schreiben, true, .sc, 0, 0⟩
  | zwx => ⟨.schreiben, false, .na, 0, 1⟩
  | zfz => ⟨.zaun, false, .sc, 0, 0⟩
  | zrx => ⟨.lesen, false, .na, 1, 0⟩

@[reducible] def zfPo (a b : ZfEv) : Prop :=
  (a = zix ∧ b ≠ zix) ∨ (a = ziy ∧ (b = zwx ∨ b = zfz ∨ b = zrx)) ∨
  (a = zwx ∧ (b = zfz ∨ b = zrx)) ∨ (a = zfz ∧ b = zrx)

@[reducible] def zfRf (a b : ZfEv) : Prop := a = zwx ∧ b = zrx

@[reducible] def zfMo (a b : ZfEv) : Prop := a = zix ∧ b = zwx

def zfGraph : Graph ZfEv Bool Nat := ⟨zfLab, zfPo, zfRf, zfMo⟩

def zfRang : ZfEv → Nat
  | zix => 0
  | ziy => 1
  | zwx => 2
  | zfz => 3
  | zrx => 4

theorem zf_po_trans {a b c : ZfEv} (h1 : zfPo a b) (h2 : zfPo b c) : zfPo a c := by
  revert h1 h2
  cases a <;> cases b <;> cases c <;> decide

theorem zf_po_rang {a b : ZfEv} (h : zfPo a b) : zfRang a < zfRang b := by
  revert h
  cases a <;> cases b <;> decide

theorem zf_rf_rang {a b : ZfEv} (h : zfRf a b) : zfRang a < zfRang b := by
  revert h
  cases a <;> cases b <;> decide

theorem zf_mo_rang {a b : ZfEv} (h : zfMo a b) : zfRang a < zfRang b := by
  revert h
  cases a <;> cases b <;> decide

theorem zf_wf : zfGraph.Wohlgeformt where
  po_trans := by
    intro a b c
    show zfPo a b → zfPo b c → zfPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ zfPo a a
    cases a <;> decide
  rf_schreibt := by
    rintro w r ⟨rfl, rfl⟩
    exact trivial
  rf_liest := by
    rintro w r ⟨rfl, rfl⟩
    exact trivial
  rf_ort := by
    rintro w r ⟨rfl, rfl⟩
    rfl
  rf_wert := by
    rintro w r ⟨rfl, rfl⟩
    rfl
  rf_eindeutig := by
    rintro w w' r ⟨rfl, rfl⟩ ⟨h, _⟩
    exact h.symm
  mo_schreibt := by
    rintro a b ⟨rfl, rfl⟩
    exact ⟨trivial, trivial⟩
  mo_ort := by
    rintro a b ⟨rfl, rfl⟩
    rfl
  mo_trans := by
    intro a b c
    show zfMo a b → zfMo b c → zfMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ zfMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    show zfMo a b ∨ zfMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha
        | exact False.elim hb
        | exact absurd rfl hne
        | (simp only [Graph.ort, zfGraph, zfLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)
  rmw_nicht_na := by
    intro a h
    cases a <;> simp only [Graph.istRmw, zfGraph, zfLab, reduceCtorEq] at h

theorem zf_kein_rmw (u : ZfEv) : ¬ zfGraph.istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, zfGraph, zfLab, reduceCtorEq] at hu

/-- The single `rf` edge goes from a plain write to a plain read, so there is no synchronisation. -/
theorem zf_kein_sw (a b : ZfEv) : ¬ zfGraph.sw a b := by
  intro h
  obtain ⟨w, x, r, hkopf, hrs, hrf, hrat, hlies, hschwanz⟩ := h
  revert hrf hrat
  show zfRf x r → (zfGraph.modus r).atomar → False
  cases x <;> cases r <;> decide

theorem zf_hb_in_po {a b : ZfEv} (h : zfGraph.hb a b) : zfPo a b := by
  refine transGen_von_trans zf_po_trans (transGen_mono (fun x y hs => ?_) h)
  rcases hs with hp | hsw
  · exact hp
  · exact False.elim (zf_kein_sw x y hsw)

theorem zf_hb_rang {a b : ZfEv} (h : zfGraph.hb a b) : zfRang a < zfRang b := by
  refine transGen_von_trans (fun x y z hxy hyz => lt_trans hxy hyz)
    (transGen_mono (fun x y hs => ?_) h)
  rcases hs with hp | hsw
  · exact zf_po_rang hp
  · exact False.elim (zf_kein_sw x y hsw)

theorem zf_rb_leer {r w : ZfEv} (h : zfGraph.rb r w) : False := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show zfRf w' r → zfMo w' w → False
  cases w' <;> cases r <;> cases w <;> decide

theorem zf_eco_rang {a b : ZfEv} (h : zfGraph.eco a b) : zfRang a < zfRang b := by
  refine transGen_von_trans (fun x y z hxy hyz => lt_trans hxy hyz)
    (transGen_mono (fun x y hs => ?_) h)
  rcases hs with hrf | hmo | hrb
  · exact zf_rf_rang hrf
  · exact zf_mo_rang hmo
  · exact False.elim (zf_rb_leer hrb)

theorem zf_zaun {a : ZfEv} (h : zfGraph.istSCZaun a) : a = zfz := by
  cases a <;>
    simp only [Graph.istSCZaun, Graph.istZaun, Graph.modus, zfGraph, zfLab, reduceCtorEq] at h ⊢ <;>
    contradiction

theorem zf_psc_rang {a b : ZfEv} (h : zfGraph.psc a b) : zfRang a < zfRang b := by
  rcases h with ⟨c, d, hscb, hl, hr⟩ | ⟨hza, hzb, hord⟩
  · have hcd : zfRang c < zfRang d := by
      rcases hscb with hp | hcross | hhb | hmo | hrb
      · exact zf_po_rang hp
      · obtain ⟨u, v, hpu, -, huv, hpv, -⟩ := hcross
        exact lt_trans (zf_po_rang hpu) (lt_trans (zf_hb_rang huv) (zf_po_rang hpv))
      · exact zf_hb_rang hhb
      · exact zf_mo_rang hmo
      · exact False.elim (zf_rb_leer hrb)
    have ha : zfRang a ≤ zfRang c := by
      rcases hl with ⟨_, rfl⟩ | ⟨_, rfl | hac⟩
      · exact le_rfl
      · exact le_of_lt (zf_hb_rang hac)
    have hb : zfRang d ≤ zfRang b := by
      rcases hr with ⟨_, rfl⟩ | ⟨_, rfl | hdb⟩
      · exact le_rfl
      · exact le_of_lt (zf_hb_rang hdb)
    exact lt_of_le_of_lt ha (lt_of_lt_of_le hcd hb)
  · subst a
    subst b
    rcases hord with hhb | ⟨c, d, hac, heco, hdb⟩
    · exact False.elim (Nat.lt_irrefl _ (zf_hb_rang hhb))
    · have hcycl : zfRang zfz < zfRang zfz :=
        lt_trans (zf_hb_rang hac) (lt_trans (zf_eco_rang heco) (zf_hb_rang hdb))
      exact False.elim (Nat.lt_irrefl _ hcycl)

theorem zf_konsistent : zfGraph.Konsistent where
  wf := zf_wf
  hb_irrefl := fun a h => Nat.lt_irrefl _ (zf_hb_rang h)
  kohaerent := fun a b hab he => Nat.lt_asymm (zf_hb_rang hab) (zf_eco_rang he)
  atomar := fun _ u _ _ hu _ => absurd hu (zf_kein_rmw u)
  liest_vorher := fun _ u _ hu => absurd hu (zf_kein_rmw u)
  psc := azyklisch_von_rang zfRang (fun a b h => zf_psc_rang h)
  ohneLB := azyklisch_von_rang zfRang (fun a b h => h.elim zf_po_rang zf_rf_rang)

theorem zf_nur_sc : zfGraph.NurSC := by
  intro a
  show (zfLab a).modus = .na ∨ (zfLab a).modus = .sc
  cases a <;> decide

theorem zf_rennfrei : zfGraph.Rennfrei := by
  rintro a b ⟨hne, ho, hw⟩ hna
  cases a <;> cases b <;>
    first
      | exact absurd rfl hne
      | exact Or.inl (zfGraph.hb_von_po (show zfPo _ _ by decide))
      | exact Or.inr (zfGraph.hb_von_po (show zfPo _ _ by decide))
      | (simp only [Graph.ort, zfGraph, zfLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)
      | (simp only [Graph.na, Graph.modus, zfGraph, zfLab, reduceCtorEq, or_self] at hna; done)
      | (simp only [Graph.schreibt, zfGraph, zfLab, Art.schreibt, or_self] at hw; done)

/-- **Satisfiability of the premises of `drf_sc` with a fence**: a consistent graph with only
    `seq_cst` atomics and no race, containing a real `seq_cst` fence in program order, a
    `seq_cst` write, and a conflicting pair of plain accesses. -/
theorem drf_sc_zaun_erfuellbar :
    ∃ G : Graph ZfEv Bool Nat, G.Konsistent ∧ G.NurSC ∧ G.Rennfrei ∧ (∃ a, G.istSCZaun a) ∧
      (∃ a, G.sc a) ∧ ∃ a b, G.Konflikt a b ∧ G.na a ∧ G.na b :=
  ⟨zfGraph, zf_konsistent, zf_nur_sc, zf_rennfrei, ⟨zfz, rfl, rfl⟩, ⟨ziy, rfl⟩,
    zwx, zrx, ⟨by decide, rfl, Or.inl trivial⟩, rfl, rfl⟩

end Gabbro.Core.Speicher
