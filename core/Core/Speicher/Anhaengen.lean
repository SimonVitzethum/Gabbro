/-
  File:      core/Core/Speicher/Anhaengen.lean
  Subject:   THE ONE-EVENT APPEND (`senke_schritt`): appending one event of context `k` with label
             `l` -- program order from a set `P` of earlier events that contains the context's own
             events and is closed under program order, reads-from from a write `q` last in `mo` at
             its location (when it reads), modification order after every write of its location
             (when it writes) -- to a consistent and complete state is a step of the graph machine.
             The new event is a sink (`Senke.lean`), so consistency follows from the old graph's.
             Every machine of M4 takes this step for a memory access, an outside event (it neither
             reads nor writes) included; `mo_letzte_existiert` supplies `q`.
-/
module

public import Core.Speicher.MoLetzte

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Zustand

variable {F Ort Wert : Type}

/-- **The premises of the one-event append.** `P` holds of every earlier event of context `k`
    and is closed under program order; a reading event's source `q` is an earlier write at its
    location, carrying the value read, last in `mo` there. -/
structure Anhang (Z : Zustand F Ort Wert) (k : F) (l : Etikett Ort Wert) (P : Nat → Prop)
    (q : Nat) : Prop where
  faden : ∀ i (h : i < Z.ev.length), (Z.ev[i]'h).kontext = k → P i
  zu : ∀ i j, i < Z.ev.length → j < Z.ev.length → P j → Z.po i j → P i
  quelle : l.art.liest → ∃ hq : q < Z.ev.length, (Z.ev[q]'hq).lab.art.schreibt ∧
    (Z.ev[q]'hq).lab.ort = l.ort ∧ (Z.ev[q]'hq).lab.geschrieben = l.gelesen ∧
    ∀ v (hv : v < Z.ev.length), (Z.ev[v]'hv).lab.art.schreibt → (Z.ev[v]'hv).lab.ort = l.ort →
      v = q ∨ Z.mo v q

/-- **The state with the event appended as a sink.** -/
def senke (Z : Zustand F Ort Wert) (k : F) (l : Etikett Ort Wert) (P : Nat → Prop) (q : Nat) :
    Zustand F Ort Wert :=
  Z.anhaengen ⟨k, l⟩
    (fun i j => (i < Z.ev.length ∧ j < Z.ev.length ∧ Z.po i j) ∨
      (i < Z.ev.length ∧ j = Z.ev.length ∧ P i))
    (fun i j => (i < Z.ev.length ∧ j < Z.ev.length ∧ Z.rf i j) ∨
      (j = Z.ev.length ∧ l.art.liest ∧ i = q))
    (fun i j => (i < Z.ev.length ∧ j < Z.ev.length ∧ Z.mo i j) ∨
      (j = Z.ev.length ∧ l.art.schreibt ∧ ∃ h : i < Z.ev.length,
        (Z.ev[i]'h).lab.art.schreibt ∧ (Z.ev[i]'h).lab.ort = l.ort))

section Senke

variable {Z : Zustand F Ort Wert} {k : F} {l : Etikett Ort Wert} {P : Nat → Prop} {q : Nat}

theorem getElem_gleich {α : Type} {xs : List α} {i j : Nat} (e : i = j) (hi : i < xs.length)
    (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst e
  rfl

theorem senke_laenge : (senke Z k l P q).ev.length = Z.ev.length + 1 :=
  anhaengen_laenge _ _ _ _ _

theorem senke_idx (a : Fin (senke Z k l P q).ev.length) :
    a.1 < Z.ev.length ∨ a.1 = Z.ev.length := by
  have h1 : a.1 < (senke Z k l P q).ev.length := a.2
  have h2 : (senke Z k l P q).ev.length = Z.ev.length + 1 := senke_laenge
  omega

theorem senke_lab_alt (a : Fin (senke Z k l P q).ev.length) (h : a.1 < Z.ev.length) :
    (senke Z k l P q).graph.lab a = Z.graph.lab ⟨a.1, h⟩ :=
  congrArg Ereignis.lab (anhaengen_alt Z _ _ _ _ h a.2)

theorem senke_lab_neu (a : Fin (senke Z k l P q).ev.length) (h : a.1 = Z.ev.length) :
    (senke Z k l P q).graph.lab a = l :=
  congrArg Ereignis.lab (List.getElem_concat_length h a.2)

/-- The source of a reading new event, in the old graph. -/
theorem Anhang.q_lab (A : Anhang Z k l P q) (hl : l.art.liest) {i : Nat} (hi : i < Z.ev.length)
    (e : i = q) : (Z.ev[i]'hi).lab.art.schreibt ∧ (Z.ev[i]'hi).lab.ort = l.ort ∧
      (Z.ev[i]'hi).lab.geschrieben = l.gelesen ∧
      ∀ v (hv : v < Z.ev.length), (Z.ev[v]'hv).lab.art.schreibt →
        (Z.ev[v]'hv).lab.ort = l.ort → v = q ∨ Z.mo v q := by
  obtain ⟨hq, h1, h2, h3, h4⟩ := A.quelle hl
  rw [getElem_gleich e hi hq]
  exact ⟨h1, h2, h3, h4⟩

/-- No write of the source's location follows the source in `mo`. -/
theorem Anhang.nicht_nach (A : Anhang Z k l P q) (hk : Z.graph.Konsistent) (hl : l.art.liest)
    {y : Nat} (hq : q < Z.ev.length) (hy : y < Z.ev.length) (h : Z.mo q y) : False := by
  have hs := hk.wf.mo_schreibt ⟨q, hq⟩ ⟨y, hy⟩ h
  have ho := hk.wf.mo_ort ⟨q, hq⟩ ⟨y, hy⟩ h
  obtain ⟨_, hqo, _, hmax⟩ := A.q_lab hl hq rfl
  have hyo : (Z.ev[y]'hy).lab.ort = l.ort := ho.symm.trans hqo
  rcases hmax y hy hs.2 hyo with e | e
  · subst e
    exact hk.wf.mo_irrefl ⟨y, hq⟩ h
  · exact hk.wf.mo_irrefl ⟨q, hq⟩ (hk.wf.mo_trans ⟨q, hq⟩ ⟨y, hy⟩ ⟨q, hq⟩ h e)

/-- The appended state is well formed. -/
theorem senke_wf (A : Anhang Z k l P q) (hk : Z.graph.Konsistent) :
    (senke Z k l P q).graph.Wohlgeformt := by
  have hw := hk.wf
  have sch : ∀ (a : Fin (senke Z k l P q).ev.length) (h : a.1 < Z.ev.length),
      (senke Z k l P q).graph.schreibt a ↔ (Z.ev[a.1]'h).lab.art.schreibt := fun a h => by
    unfold Graph.schreibt; rw [senke_lab_alt a h]; exact Iff.rfl
  have ort : ∀ (a : Fin (senke Z k l P q).ev.length) (h : a.1 < Z.ev.length),
      (senke Z k l P q).graph.ort a = (Z.ev[a.1]'h).lab.ort := fun a h => by
    unfold Graph.ort; rw [senke_lab_alt a h]; rfl
  have schN : ∀ (a : Fin (senke Z k l P q).ev.length), a.1 = Z.ev.length →
      ((senke Z k l P q).graph.schreibt a ↔ l.art.schreibt) := fun a h => by
    unfold Graph.schreibt; rw [senke_lab_neu a h]
  have ortN : ∀ (a : Fin (senke Z k l P q).ev.length), a.1 = Z.ev.length →
      (senke Z k l P q).graph.ort a = l.ort := fun a h => by
    unfold Graph.ort; rw [senke_lab_neu a h]
  exact {
    po_trans := fun a b c h1 h2 => by
      rcases h1 with ⟨ha, hb, h1⟩ | ⟨ha, hb, h1⟩ <;> rcases h2 with ⟨hb', hc, h2⟩ | ⟨hb', hc, h2⟩
      · exact Or.inl ⟨ha, hc, hw.po_trans ⟨a.1, ha⟩ ⟨b.1, hb⟩ ⟨c.1, hc⟩ h1 h2⟩
      · exact Or.inr ⟨ha, hc, A.zu a.1 b.1 ha hb h2 h1⟩
      · omega
      · omega
    po_irrefl := fun a h => by
      rcases h with ⟨ha, _, h⟩ | ⟨ha, hb, _⟩
      · exact hw.po_irrefl ⟨a.1, ha⟩ h
      · omega
    rf_schreibt := fun w r h => by
      rcases h with ⟨hw', hr, h⟩ | ⟨_, hl, hq⟩
      · exact (sch w hw').2 (hw.rf_schreibt ⟨w.1, hw'⟩ ⟨r.1, hr⟩ h)
      · obtain ⟨hqn, _⟩ := A.quelle hl
        have hwn : w.1 < Z.ev.length := hq ▸ hqn
        exact (sch w hwn).2 (A.q_lab hl hwn hq).1
    rf_liest := fun w r h => by
      rcases h with ⟨hw', hr, h⟩ | ⟨hr, hl, _⟩
      · have h1 := hw.rf_liest ⟨w.1, hw'⟩ ⟨r.1, hr⟩ h
        unfold Graph.liest; rw [senke_lab_alt r hr]; exact h1
      · unfold Graph.liest; rw [senke_lab_neu r hr]; exact hl
    rf_ort := fun w r h => by
      rcases h with ⟨hw', hr, h⟩ | ⟨hr, hl, hq⟩
      · rw [ort w hw', ort r hr]; exact hw.rf_ort ⟨w.1, hw'⟩ ⟨r.1, hr⟩ h
      · obtain ⟨hqn, _⟩ := A.quelle hl
        have hwn : w.1 < Z.ev.length := hq ▸ hqn
        rw [ort w hwn, ortN r hr]; exact (A.q_lab hl hwn hq).2.1
    rf_wert := fun w r h => by
      rcases h with ⟨hw', hr, h⟩ | ⟨hr, hl, hq⟩
      · rw [senke_lab_alt w hw', senke_lab_alt r hr]; exact hw.rf_wert ⟨w.1, hw'⟩ ⟨r.1, hr⟩ h
      · obtain ⟨hqn, _⟩ := A.quelle hl
        have hwn : w.1 < Z.ev.length := hq ▸ hqn
        rw [senke_lab_alt w hwn, senke_lab_neu r hr]; exact (A.q_lab hl hwn hq).2.2.1
    rf_eindeutig := fun w w' r h1 h2 => by
      rcases h1 with ⟨hw1, hr, h1⟩ | ⟨hr, _, hq⟩ <;> rcases h2 with ⟨hw2, hr', h2⟩ | ⟨hr', _, hq'⟩
      · have e := hw.rf_eindeutig ⟨w.1, hw1⟩ ⟨w'.1, hw2⟩ ⟨r.1, hr⟩ h1 h2
        have e' := congrArg Fin.val e
        exact Fin.ext e'
      · omega
      · omega
      · exact Fin.ext (hq.trans hq'.symm)
    mo_schreibt := fun a b h => by
      rcases h with ⟨ha, hb, h⟩ | ⟨hb, hls, ha, has, _⟩
      · obtain ⟨x, y⟩ := hw.mo_schreibt ⟨a.1, ha⟩ ⟨b.1, hb⟩ h
        exact ⟨(sch a ha).2 x, (sch b hb).2 y⟩
      · exact ⟨(sch a ha).2 has, (schN b hb).2 hls⟩
    mo_ort := fun a b h => by
      rcases h with ⟨ha, hb, h⟩ | ⟨hb, _, ha, _, hao⟩
      · rw [ort a ha, ort b hb]; exact hw.mo_ort ⟨a.1, ha⟩ ⟨b.1, hb⟩ h
      · rw [ort a ha, ortN b hb]; exact hao
    mo_trans := fun a b c h1 h2 => by
      rcases h1 with ⟨ha, hb, h1⟩ | ⟨hb, _, _⟩ <;> rcases h2 with ⟨hb', hc, h2⟩ | ⟨hc, hls, hb', hbs, hbo⟩
      · exact Or.inl ⟨ha, hc, hw.mo_trans ⟨a.1, ha⟩ ⟨b.1, hb⟩ ⟨c.1, hc⟩ h1 h2⟩
      · have hs := hw.mo_schreibt ⟨a.1, ha⟩ ⟨b.1, hb⟩ h1
        have ho := hw.mo_ort ⟨a.1, ha⟩ ⟨b.1, hb⟩ h1
        exact Or.inr ⟨hc, hls, ha, hs.1, ho.trans hbo⟩
      · omega
      · omega
    mo_irrefl := fun a h => by
      rcases h with ⟨ha, _, h⟩ | ⟨ha, _, ha', _⟩
      · exact hw.mo_irrefl ⟨a.1, ha⟩ h
      · omega
    mo_total := fun a b ha hb ho hne => by
      rcases senke_idx a with ha' | ha' <;> rcases senke_idx b with hb' | hb'
      · rw [ort a ha', ort b hb'] at ho
        rcases hw.mo_total ⟨a.1, ha'⟩ ⟨b.1, hb'⟩ ((sch a ha').1 ha) ((sch b hb').1 hb) ho
            (fun e => hne (by have e' := congrArg Fin.val e; exact Fin.ext e')) with h | h
        · exact Or.inl (Or.inl ⟨ha', hb', h⟩)
        · exact Or.inr (Or.inl ⟨hb', ha', h⟩)
      · rw [ort a ha', ortN b hb'] at ho
        exact Or.inl (Or.inr ⟨hb', (schN b hb').1 hb, ha', (sch a ha').1 ha, ho⟩)
      · rw [ortN a ha', ort b hb'] at ho
        exact Or.inr (Or.inr ⟨ha', (schN a ha').1 ha, hb', (sch b hb').1 hb, ho.symm⟩)
      · exact absurd (Fin.ext (ha'.trans hb'.symm)) hne }

/-- The index of the new event. -/
def neuIdx (Z : Zustand F Ort Wert) (k : F) (l : Etikett Ort Wert) (P : Nat → Prop) (q : Nat) :
    Fin (senke Z k l P q).ev.length :=
  ⟨Z.ev.length, by rw [senke_laenge]; exact Nat.lt_succ_self _⟩

/-- **The new event is a sink.** -/
theorem senke_ist_senke (A : Anhang Z k l P q) (hk : Z.graph.Konsistent) :
    (senke Z k l P q).graph.Senke (neuIdx Z k l P q) where
  po := fun x h => by
    rcases h with ⟨h, _, _⟩ | ⟨h, _, _⟩ <;> exact Nat.lt_irrefl _ h
  rf := fun x h => by
    rcases h with ⟨h, _, _⟩ | ⟨_, hl, hq⟩
    · exact Nat.lt_irrefl _ h
    · obtain ⟨hqn, _⟩ := A.quelle hl
      have hq' : Z.ev.length = q := hq
      omega
  mo := fun x h => by
    rcases h with ⟨h, _, _⟩ | ⟨_, _, h, _⟩ <;> exact Nat.lt_irrefl _ h
  rb := fun y h => by
    obtain ⟨w, hrf, hmo, hne⟩ := h
    rcases hrf with ⟨_, h, _⟩ | ⟨_, hl, hq⟩
    · exact Nat.lt_irrefl _ h
    · obtain ⟨hqn, _⟩ := A.quelle hl
      have hwn : w.1 < Z.ev.length := hq ▸ hqn
      rcases hmo with ⟨_, hy, h⟩ | ⟨hy, _⟩
      · rw [hq] at h
        exact A.nicht_nach hk hl hqn hy h
      · exact hne (Fin.ext hy.symm)

/-- The old graph is the new one without the new event. -/
def ohneAbb (Z : Zustand F Ort Wert) (k : F) (l : Etikett Ort Wert) (P : Nat → Prop) (q : Nat)
    (a : {x : Fin (senke Z k l P q).ev.length // x ≠ neuIdx Z k l P q}) : Fin Z.ev.length :=
  ⟨a.1.1, by
    rcases senke_idx a.1 with h | h
    · exact h
    · exact absurd (Fin.ext h) a.2⟩

theorem senke_ohne_einbettung :
    Graph.Einbettung (Graph.Senke.ohne (senke Z k l P q).graph (neuIdx Z k l P q)) Z.graph
      (ohneAbb Z k l P q) where
  inj := fun a b e => by
    have e' := congrArg Fin.val e
    exact Subtype.ext (Fin.ext e')
  lab := fun a => senke_lab_alt a.1 (ohneAbb Z k l P q a).2
  po := fun a b => by
    have hb := (ohneAbb Z k l P q b).2
    constructor
    · rintro (⟨_, _, h⟩ | ⟨_, hb', _⟩)
      · exact h
      · exact absurd hb' (Nat.ne_of_lt hb)
    · exact fun h => Or.inl ⟨(ohneAbb Z k l P q a).2, hb, h⟩
  rf := fun a b => by
    have hb := (ohneAbb Z k l P q b).2
    constructor
    · rintro (⟨_, _, h⟩ | ⟨hb', _, _⟩)
      · exact h
      · exact absurd hb' (Nat.ne_of_lt hb)
    · exact fun h => Or.inl ⟨(ohneAbb Z k l P q a).2, hb, h⟩
  mo := fun a b => by
    have hb := (ohneAbb Z k l P q b).2
    constructor
    · rintro (⟨_, _, h⟩ | ⟨hb', _, _⟩)
      · exact h
      · exact absurd hb' (Nat.ne_of_lt hb)
    · exact fun h => Or.inl ⟨(ohneAbb Z k l P q a).2, hb, h⟩

/-- **The appended state is consistent.** -/
theorem senke_konsistent_zustand (A : Anhang Z k l P q) (hk : Z.graph.Konsistent) :
    (senke Z k l P q).graph.Konsistent := by
  refine Graph.senke_konsistent (senke_ist_senke A hk) (senke_wf A hk)
    (senke_ohne_einbettung.konsistent hk) (fun w w' h1 _ h3 h4 => ?_)
  rcases h1 with ⟨_, h, _⟩ | ⟨_, hl, hq⟩
  · exact Nat.lt_irrefl _ h
  · obtain ⟨hqn, _⟩ := A.quelle hl
    rcases h3 with ⟨_, hw', h3⟩ | ⟨hw', _⟩
    · rw [hq] at h3
      exact A.nicht_nach hk hl hqn hw' h3
    · rcases h4 with ⟨h4, _, _⟩ | ⟨_, _, h4, _⟩ <;> omega

/-- **The appended state is complete.** -/
theorem senke_vollstaendig (A : Anhang Z k l P q) (hv : Z.graph.Vollstaendig) :
    (senke Z k l P q).graph.Vollstaendig := by
  intro r hr
  rcases senke_idx r with h | h
  · have hr' : Z.graph.liest ⟨r.1, h⟩ := by
      unfold Graph.liest at hr ⊢
      rw [senke_lab_alt r h] at hr
      exact hr
    obtain ⟨w, hw⟩ := hv _ hr'
    exact ⟨⟨w.1, by rw [senke_laenge]; exact Nat.lt_succ_of_lt w.2⟩, Or.inl ⟨w.2, h, hw⟩⟩
  · have hl : l.art.liest := by
      unfold Graph.liest at hr
      rw [senke_lab_neu r h] at hr
      exact hr
    obtain ⟨hqn, _⟩ := A.quelle hl
    exact ⟨⟨q, by rw [senke_laenge]; exact Nat.lt_succ_of_lt hqn⟩, Or.inr ⟨h, hl, rfl⟩⟩

/-- **THE ONE-EVENT APPEND IS A STEP OF THE GRAPH MACHINE.** -/
theorem senke_schritt (A : Anhang Z k l P q) (hk : Z.graph.Konsistent)
    (hv : Z.graph.Vollstaendig) : Schritt Z k l (senke Z k l P q) where
  ev := rfl
  po_alt := fun i j hi hj => ⟨fun h => by
    rcases h with ⟨_, _, h⟩ | ⟨_, hj', _⟩
    · exact h
    · omega, fun h => Or.inl ⟨hi, hj, h⟩⟩
  rf_alt := fun i j hi hj => ⟨fun h => by
    rcases h with ⟨_, _, h⟩ | ⟨hj', _, _⟩
    · exact h
    · omega, fun h => Or.inl ⟨hi, hj, h⟩⟩
  mo_alt := fun i j hi hj => ⟨fun h => by
    rcases h with ⟨_, _, h⟩ | ⟨hj', _, _⟩
    · exact h
    · omega, fun h => Or.inl ⟨hi, hj, h⟩⟩
  po_faden := fun i h hf => Or.inr ⟨h, rfl, A.faden i h hf⟩
  po_ende := fun i _ h => by
    rcases h with ⟨h, _, _⟩ | ⟨h, _, _⟩ <;> exact Nat.lt_irrefl _ h
  rf_ende := fun i hi h => by
    rcases h with ⟨h, _, _⟩ | ⟨hi', _, _⟩
    · exact Nat.lt_irrefl _ h
    · omega
  konsistent := senke_konsistent_zustand A hk
  vollstaendig := senke_vollstaendig A hv

end Senke

end Zustand

end Gabbro.Core.Speicher
