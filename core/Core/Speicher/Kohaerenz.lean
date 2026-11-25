/-
  File:      core/Core/Speicher/Kohaerenz.lean
  Subject:   Two consequences of COHERENCE used by the machines of M4 over the graph machine, and the
             extension of a state by several events at once:
             * `liest_mo_max`: a read takes a write that no write happening before it follows in
               modification order;
             * `hb_mo`: a write happening before another write of its location precedes it in
               modification order;
             * `Zustand.Erweitert`: a state with events appended and the old relations kept --
               its old graph embeds (`Erweitert.einbettung`).
-/
module

public import Core.Speicher.Graphmaschine

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E Ort Wert : Type} {G : Graph E Ort Wert}

/-- **A read takes a write that is newest among the writes happening before it**: every write
    `x` of the read's location with `hb x r` is the source or precedes it in `mo`. -/
theorem liest_mo_max (hk : G.Konsistent) {w r x : E} (hrf : G.rf w r) (hx : G.schreibt x)
    (ho : G.ort x = G.ort r) (hb : G.hb x r) : x = w ∨ G.mo x w := by
  by_cases e : x = w
  · exact Or.inl e
  · right
    have ho' : G.ort x = G.ort w := ho.trans (hk.wf.rf_ort w r hrf).symm
    rcases hk.wf.mo_total x w hx (hk.wf.rf_schreibt _ _ hrf) ho' e with h | h
    · exact h
    · exfalso
      have hne : r ≠ x := by
        intro e'
        rw [e'] at hb
        exact hk.hb_irrefl x hb
      exact hk.kohaerent x r hb (G.eco_von_rb ⟨w, hrf, h, hne⟩)

/-- **Happens-before orders writes of one location in modification order.** -/
theorem hb_mo (hk : G.Konsistent) {x w : E} (hx : G.schreibt x) (hw : G.schreibt w)
    (ho : G.ort x = G.ort w) (hb : G.hb x w) : G.mo x w := by
  have hne : x ≠ w := by
    intro e
    rw [e] at hb
    exact hk.hb_irrefl w hb
  rcases hk.wf.mo_total x w hx hw ho hne with h | h
  · exact h
  · exact absurd (G.eco_von_mo h) (hk.kohaerent x w hb)

/-- A write and a release-acquire read of it synchronise when both are at least
    release/acquire (a release sequence of length zero). -/
theorem sw_direkt (hw : G.Wohlgeformt) {w r : E} (hrf : G.rf w r) (hmw : (G.modus w).stark)
    (hmr : (G.modus r).stark) : G.sw w r :=
  sw_von_klassisch ⟨hw.rf_schreibt _ _ hrf, hmw, hw.rf_liest _ _ hrf, hmr, w,
    .selbst (hw.rf_schreibt _ _ hrf) (Modus.stark_atomar hmw), hrf⟩

end Graph

namespace Zustand

variable {F Ort Wert : Type}

/-- **`Z'` extends `Z`**: events appended at the end, the relations among the old events
    kept. -/
structure Erweitert (Z Z' : Zustand F Ort Wert) : Prop where
  praefix : ∃ es, Z'.ev = Z.ev ++ es
  po_alt : ∀ i j, i < Z.ev.length → j < Z.ev.length → (Z'.po i j ↔ Z.po i j)
  rf_alt : ∀ i j, i < Z.ev.length → j < Z.ev.length → (Z'.rf i j ↔ Z.rf i j)
  mo_alt : ∀ i j, i < Z.ev.length → j < Z.ev.length → (Z'.mo i j ↔ Z.mo i j)

variable {Z Z' : Zustand F Ort Wert}

theorem Erweitert.laenge_le (h : Erweitert Z Z') : Z.ev.length ≤ Z'.ev.length := by
  obtain ⟨es, e⟩ := h.praefix
  rw [e, List.length_append]
  exact Nat.le_add_right _ _

/-- An old event in the extended state. -/
theorem Erweitert.getElem (h : Erweitert Z Z') {i : Nat} (hi : i < Z.ev.length)
    (hi' : i < Z'.ev.length) : Z'.ev[i]'hi' = Z.ev[i]'hi := by
  obtain ⟨es, e⟩ := h.praefix
  rw [List.getElem_of_eq e]
  exact List.getElem_append_left hi

/-- The index of an old event in the extended state. -/
def Erweitert.alt (h : Erweitert Z Z') (a : Fin Z.ev.length) : Fin Z'.ev.length :=
  ⟨a.1, Nat.lt_of_lt_of_le a.2 h.laenge_le⟩

/-- **The old graph embeds into the extended one.** -/
theorem Erweitert.einbettung (h : Erweitert Z Z') : Graph.Einbettung Z.graph Z'.graph h.alt where
  inj := fun a b e => by
    have e' := congrArg Fin.val e
    exact Fin.ext e'
  lab := fun a => (congrArg Ereignis.lab (h.getElem a.2 (h.alt a).2)).symm
  po := fun a b => (h.po_alt a.1 b.1 a.2 b.2).symm
  rf := fun a b => (h.rf_alt a.1 b.1 a.2 b.2).symm
  mo := fun a b => (h.mo_alt a.1 b.1 a.2 b.2).symm

theorem Erweitert.refl (Z : Zustand F Ort Wert) : Erweitert Z Z where
  praefix := ⟨[], (List.append_nil _).symm⟩
  po_alt := fun _ _ _ _ => Iff.rfl
  rf_alt := fun _ _ _ _ => Iff.rfl
  mo_alt := fun _ _ _ _ => Iff.rfl

theorem Erweitert.trans {Z'' : Zustand F Ort Wert} (h1 : Erweitert Z Z') (h2 : Erweitert Z' Z'') :
    Erweitert Z Z'' where
  praefix := by
    obtain ⟨es, e1⟩ := h1.praefix
    obtain ⟨es', e2⟩ := h2.praefix
    exact ⟨es ++ es', by rw [e2, e1, List.append_assoc]⟩
  po_alt := fun i j hi hj => (h2.po_alt i j (Nat.lt_of_lt_of_le hi h1.laenge_le)
    (Nat.lt_of_lt_of_le hj h1.laenge_le)).trans (h1.po_alt i j hi hj)
  rf_alt := fun i j hi hj => (h2.rf_alt i j (Nat.lt_of_lt_of_le hi h1.laenge_le)
    (Nat.lt_of_lt_of_le hj h1.laenge_le)).trans (h1.rf_alt i j hi hj)
  mo_alt := fun i j hi hj => (h2.mo_alt i j (Nat.lt_of_lt_of_le hi h1.laenge_le)
    (Nat.lt_of_lt_of_le hj h1.laenge_le)).trans (h1.mo_alt i j hi hj)

/-- A step of the graph machine extends the state. -/
theorem Schritt.erweitert {t : F} {l : Etikett Ort Wert} (s : Schritt Z t l Z') :
    Erweitert Z Z' where
  praefix := ⟨_, s.ev⟩
  po_alt := s.po_alt
  rf_alt := s.rf_alt
  mo_alt := s.mo_alt

/-- **Every reachable state extends the empty one along steps of the machine.** -/
theorem erreichbar_erweitert {Z : Zustand F Ort Wert} (h : Erreichbar Z) : Erweitert leer Z := by
  induction h with
  | start => exact Erweitert.refl _
  | schritt _ _ _ s ih => exact ih.trans s.erweitert

end Zustand

end Gabbro.Core.Speicher
