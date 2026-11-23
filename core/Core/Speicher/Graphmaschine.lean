/-
  File:      core/Core/Speicher/Graphmaschine.lean
  Subject:   THE OPERATIONAL GRAPH MACHINE over the axiomatic memory model W (PERFECT-MODEL §3.5,
             step M3): a state is a consistent, complete execution-graph prefix; a step appends ONE
             event at the end of one thread, choosing its reads-from source among the earlier
             events and its place in modification order, and the result must again be consistent
             and complete. Soundness (`erreichbar_gut`, `erreichbar_ordnung`, `Schritt.alt_gut`)
             is here; completeness against `Konsistent` is `GraphmaschineVollstaendig.lean`.

  Because `po ∪ rf` is acyclic, no promises are needed: an event is appended after everything it
  depends on in program order and reads-from (`ausfuehrung_in_ordnung`); only modification order
  may place a new write BEFORE older writes of its location (`mo` is not part of the append
  order).
-/
module

public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

/-- An event of the machine: the context (thread, handler, core) that appended it and its label. -/
structure Ereignis (F Ort Wert : Type) where
  kontext : F
  lab : Etikett Ort Wert

/-- **A state of the graph machine**: the events in the order they were appended, and program
    order, reads-from and modification order between their indices (only pairs of indices below
    the number of events are meaningful). -/
structure Zustand (F Ort Wert : Type) where
  ev : List (Ereignis F Ort Wert)
  po : Nat → Nat → Prop
  rf : Nat → Nat → Prop
  mo : Nat → Nat → Prop

namespace Zustand

variable {F Ort Wert : Type}

/-- **The execution graph of a state**, over the indices of its events. -/
def graph (Z : Zustand F Ort Wert) : Graph (Fin Z.ev.length) Ort Wert where
  lab a := (Z.ev[a.1]'a.2).lab
  po a b := Z.po a.1 b.1
  rf a b := Z.rf a.1 b.1
  mo a b := Z.mo a.1 b.1

/-- The empty state: no event. -/
def leer : Zustand F Ort Wert := ⟨[], fun _ _ => False, fun _ _ => False, fun _ _ => False⟩

/-- A state with one more event at the end and the given relations. -/
def anhaengen (Z : Zustand F Ort Wert) (x : Ereignis F Ort Wert) (po rf mo : Nat → Nat → Prop) :
    Zustand F Ort Wert :=
  ⟨Z.ev ++ [x], po, rf, mo⟩

/-- **One step of the graph machine**: thread `t` appends ONE event with label `l`.
    * `ev`: the event is appended at the end of the list;
    * `po_alt`, `rf_alt`, `mo_alt`: the relations among the earlier events are unchanged;
    * `po_faden`: the new event comes after every earlier event of its thread in program order
      (it is appended at the END of the thread);
    * `po_ende`, `rf_ende`: no earlier event comes after it in program order or reads from it
      (the step depends only on what is already there; its own reads-from source is an earlier
      event or none -- and `vollstaendig` demands one for a read);
    * `konsistent`, `vollstaendig`: the new graph is consistent and complete. Modification order
      may place a new write anywhere among the writes of its location. -/
structure Schritt (Z : Zustand F Ort Wert) (t : F) (l : Etikett Ort Wert)
    (Z' : Zustand F Ort Wert) : Prop where
  ev : Z'.ev = Z.ev ++ [⟨t, l⟩]
  po_alt : ∀ i j, i < Z.ev.length → j < Z.ev.length → (Z'.po i j ↔ Z.po i j)
  rf_alt : ∀ i j, i < Z.ev.length → j < Z.ev.length → (Z'.rf i j ↔ Z.rf i j)
  mo_alt : ∀ i j, i < Z.ev.length → j < Z.ev.length → (Z'.mo i j ↔ Z.mo i j)
  po_faden : ∀ i (h : i < Z.ev.length), (Z.ev[i]'h).kontext = t → Z'.po i Z.ev.length
  po_ende : ∀ i, i < Z.ev.length → ¬ Z'.po Z.ev.length i
  rf_ende : ∀ i, i < Z.ev.length → ¬ Z'.rf Z.ev.length i
  konsistent : Z'.graph.Konsistent
  vollstaendig : Z'.graph.Vollstaendig

/-- **The states the graph machine reaches** from the empty state. -/
inductive Erreichbar : Zustand F Ort Wert → Prop
  | start : Erreichbar leer
  | schritt {Z Z' : Zustand F Ort Wert} (t : F) (l : Etikett Ort Wert) :
      Erreichbar Z → Schritt Z t l Z' → Erreichbar Z'

/-! ## Index arithmetic of appending -/

theorem anhaengen_laenge (Z : Zustand F Ort Wert) (x : Ereignis F Ort Wert)
    (po rf mo : Nat → Nat → Prop) : (Z.anhaengen x po rf mo).ev.length = Z.ev.length + 1 := by
  simp only [anhaengen, List.length_append, List.length_singleton]

theorem anhaengen_alt (Z : Zustand F Ort Wert) (x : Ereignis F Ort Wert)
    (po rf mo : Nat → Nat → Prop) {i : Nat} (h : i < Z.ev.length)
    (h' : i < (Z.anhaengen x po rf mo).ev.length) :
    (Z.anhaengen x po rf mo).ev[i]'h' = Z.ev[i]'h :=
  List.getElem_append_left h

theorem anhaengen_neu (Z : Zustand F Ort Wert) (x : Ereignis F Ort Wert)
    (po rf mo : Nat → Nat → Prop) (h' : Z.ev.length < (Z.anhaengen x po rf mo).ev.length) :
    (Z.anhaengen x po rf mo).ev[Z.ev.length]'h' = x :=
  List.getElem_concat_length rfl h'

/-- An event list that is another one with one event appended: the earlier entries. -/
theorem getElem_angehaengt {α : Type} {l l' : List α} {x : α} (he : l' = l ++ [x]) {i : Nat}
    (h : i < l.length) (h' : i < l'.length) : l'[i]'h' = l[i]'h := by
  rw [List.getElem_of_eq he]
  exact List.getElem_append_left h

/-- An event list that is another one with one event appended: the last entry. -/
theorem getElem_angehaengt_neu {α : Type} {l l' : List α} {x : α} (he : l' = l ++ [x])
    (h' : l.length < l'.length) : l'[l.length]'h' = x := by
  rw [List.getElem_of_eq he]
  exact List.getElem_concat_length rfl _

theorem laenge_angehaengt {α : Type} {l l' : List α} {x : α} (he : l' = l ++ [x]) :
    l'.length = l.length + 1 := by
  rw [he, List.length_append, List.length_singleton]

/-! ## Soundness -/

theorem leer_elim (a : Fin (leer : Zustand F Ort Wert).ev.length) : False :=
  Nat.not_lt_zero _ a.2

/-- The empty graph is consistent. -/
theorem leer_konsistent : (leer : Zustand F Ort Wert).graph.Konsistent where
  wf := {
    po_trans := fun a => (leer_elim a).elim
    po_irrefl := fun a => (leer_elim a).elim
    rf_schreibt := fun a => (leer_elim a).elim
    rf_liest := fun a => (leer_elim a).elim
    rf_ort := fun a => (leer_elim a).elim
    rf_wert := fun a => (leer_elim a).elim
    rf_eindeutig := fun a => (leer_elim a).elim
    mo_schreibt := fun a => (leer_elim a).elim
    mo_ort := fun a => (leer_elim a).elim
    mo_trans := fun a => (leer_elim a).elim
    mo_irrefl := fun a => (leer_elim a).elim
    mo_total := fun a => (leer_elim a).elim }
  hb_irrefl := fun a => (leer_elim a).elim
  kohaerent := fun a => (leer_elim a).elim
  atomar := fun a => (leer_elim a).elim
  psc := fun a => (leer_elim a).elim
  ohneLB := fun a => (leer_elim a).elim

theorem leer_vollstaendig : (leer : Zustand F Ort Wert).graph.Vollstaendig :=
  fun a => (leer_elim a).elim

/-- **Every reachable state is consistent and complete.** -/
theorem erreichbar_gut {Z : Zustand F Ort Wert} (h : Erreichbar Z) :
    Z.graph.Konsistent ∧ Z.graph.Vollstaendig := by
  cases h with
  | start => exact ⟨leer_konsistent, leer_vollstaendig⟩
  | schritt _ _ _ s => exact ⟨s.konsistent, s.vollstaendig⟩

/-- The index of an earlier event in the state after a step. -/
def Schritt.einbetten {Z Z' : Zustand F Ort Wert} {t : F} {l : Etikett Ort Wert}
    (s : Schritt Z t l Z') (a : Fin Z.ev.length) : Fin Z'.ev.length :=
  ⟨a.1, by rw [laenge_angehaengt s.ev]; exact Nat.lt_succ_of_lt a.2⟩

/-- **The state before a step is the prefix of the state after it**: its graph embeds. -/
theorem Schritt.alt_einbettung {Z Z' : Zustand F Ort Wert} {t : F} {l : Etikett Ort Wert}
    (s : Schritt Z t l Z') : Graph.Einbettung Z.graph Z'.graph s.einbetten where
  inj := fun a b h => by
    have h' := congrArg Fin.val h
    exact Fin.ext h'
  lab := fun a =>
    (congrArg Ereignis.lab (getElem_angehaengt s.ev a.2 (s.einbetten a).2)).symm
  po := fun a b => (s.po_alt a.1 b.1 a.2 b.2).symm
  rf := fun a b => (s.rf_alt a.1 b.1 a.2 b.2).symm
  mo := fun a b => (s.mo_alt a.1 b.1 a.2 b.2).symm

/-- The prefix before a step is consistent (the restriction argument of `Praefix.lean`, along
    the embedding). -/
theorem Schritt.alt_gut {Z Z' : Zustand F Ort Wert} {t : F} {l : Etikett Ort Wert}
    (s : Schritt Z t l Z') : Z.graph.Konsistent :=
  s.alt_einbettung.konsistent s.konsistent

/-- **The append order is an execution order** (the order `T` of `ausfuehrung_in_ordnung`):
    in a reachable state program order and reads-from only point from earlier to later
    indices. -/
theorem erreichbar_ordnung {Z : Zustand F Ort Wert} (h : Erreichbar Z) :
    ∀ i j, i < Z.ev.length → j < Z.ev.length → (Z.po i j ∨ Z.rf i j) → i < j := by
  induction h with
  | start => exact fun i _ hi => absurd hi (Nat.not_lt_zero _)
  | @schritt Z Z' t l hZ s ih =>
    intro i j hi hj hij
    rw [laenge_angehaengt s.ev] at hi hj
    rcases Nat.lt_or_ge i Z.ev.length with hi' | hi'
    · rcases Nat.lt_or_ge j Z.ev.length with hj' | hj'
      · refine ih i j hi' hj' ?_
        rcases hij with h1 | h1
        · exact Or.inl ((s.po_alt i j hi' hj').1 h1)
        · exact Or.inr ((s.rf_alt i j hi' hj').1 h1)
      · omega
    · have hi2 : i = Z.ev.length := by omega
      subst hi2
      rcases Nat.lt_or_ge j Z.ev.length with hj' | hj'
      · rcases hij with h1 | h1
        · exact absurd h1 (s.po_ende j hj')
        · exact absurd h1 (s.rf_ende j hj')
      · have hj2 : j = Z.ev.length := by omega
        subst hj2
        have hn : Z.ev.length < Z'.ev.length := by rw [laenge_angehaengt s.ev]; omega
        exfalso
        exact s.konsistent.ohneLB ⟨Z.ev.length, hn⟩ (.single hij)

/-- **The events of one thread are in program order in their append order.** -/
theorem erreichbar_faden {Z : Zustand F Ort Wert} (h : Erreichbar Z) :
    ∀ i j (hi : i < Z.ev.length) (hj : j < Z.ev.length),
      (Z.ev[i]'hi).kontext = (Z.ev[j]'hj).kontext → i < j → Z.po i j := by
  induction h with
  | start => exact fun i _ hi => absurd hi (Nat.not_lt_zero _)
  | @schritt Z Z' t l hZ s ih =>
    intro i j hi hj hf hij
    have hl := laenge_angehaengt s.ev
    have hi' : i < Z.ev.length := by omega
    rw [getElem_angehaengt s.ev hi'] at hf
    rcases Nat.lt_or_ge j Z.ev.length with hj' | hj'
    · rw [getElem_angehaengt s.ev hj'] at hf
      exact (s.po_alt i j hi' hj').2 (ih i j hi' hj' hf hij)
    · have hj2 : j = Z.ev.length := by omega
      subst hj2
      rw [getElem_angehaengt_neu s.ev] at hf
      exact s.po_faden i hi' hf

end Zustand

end Gabbro.Core.Speicher
