module

public import Core.Sicherheit.Regel

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog
open Speicher (Etikett)

variable {L Ort Wert Raum Lok Grund : Type}

theorem rennen_bei_leeren_ereignissen {g : SpeicherGraph Ort Wert} (leer : g.ev = []) :
    RennenImGraph g := by
  intro i
  have length : g.ev.length = 0 := congrArg List.length leer
  exact (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le i.isLt length.le)).elim

/-- Catalogue events extend the prefix with one non-memory label. They never materialise
    an initial write and introduce no conflicting access. -/
theorem aussen_label_speicher {initial : Ort → Wert} {vor nach : SpeicherGraph Ort Wert}
    {label : Etikett Ort Wert} {spur : SpeicherSpur Ort Wert}
    {actor : SpeicherAkteur Ort}
    (istAussen : label.art = .aussen)
    (folge : Speicherfolge initial actor vor [label] spur nach) :
    spur = [(actor, label)] ∧ (RennenImGraph vor → RennenImGraph nach) := by
  cases folge with
  | cons init anhang rest =>
    cases rest
    cases init with
    | erste nichtAussen _ _ => exact (nichtAussen istAussen).elim
    | ohne _ =>
      refine ⟨rfl, fun rennen i j konflikt => ?_⟩
      have erweitert := anhang.erweitert
      have alt (k : Fin nach.ev.length) (zugriff : AusgefuehrterZugriff nach k) :
          k.val < vor.ev.length := by
        by_contra! spaeter
        have length : nach.ev.length = vor.ev.length + 1 :=
          Speicher.Zustand.laenge_angehaengt anhang.ev
        have bound := Nat.lt_of_lt_of_le k.isLt length.le
        have idx : k.val = vor.ev.length := Nat.le_antisymm (Nat.lt_succ_iff.mp bound) spaeter
        have boundNeu : vor.ev.length < nach.ev.length :=
          Nat.lt_of_le_of_lt spaeter k.isLt
        have same : k = ⟨vor.ev.length, boundNeu⟩ := Fin.ext idx
        have lab : nach.graph.lab k = label :=
          (congrArg nach.graph.lab same).trans (congrArg Speicher.Ereignis.lab
            (Speicher.Zustand.getElem_angehaengt_neu anhang.ev boundNeu))
        have real := zugriff.1
        simp only [Speicher.Graph.liest, Speicher.Graph.schreibt, lab, istAussen] at real
        exact real.elim id id
      let a : Fin vor.ev.length := ⟨i.val, alt i konflikt.2.1⟩
      let b : Fin vor.ev.length := ⟨j.val, alt j konflikt.2.2.1⟩
      have eqA : erweitert.alt a = i := Fin.ext rfl
      have eqB : erweitert.alt b = j := Fin.ext rfl
      have eventA := erweitert.getElem a.isLt i.isLt
      have eventB := erweitert.getElem b.isLt j.isLt
      have altKonflikt : Konflikt vor a b := by
        have neq : a ≠ b :=
          fun gleich => konflikt.1 (eqA.symm.trans ((congrArg erweitert.alt gleich).trans eqB))
        refine ⟨neq, ?_⟩
        have h := konflikt.2
        simp only [AusgefuehrterZugriff, Speicher.Graph.liest, Speicher.Graph.schreibt,
          Speicher.Graph.ort, Speicher.Graph.na, Speicher.Graph.modus,
          Speicher.Zustand.graph] at h ⊢
        rwa [eventA, eventB] at h
      rcases rennen a b altKonflikt with order | order
      · exact Or.inl (eqA ▸ eqB ▸ erweitert.einbettung.hb order)
      · exact Or.inr (eqA ▸ eqB ▸ erweitert.einbettung.hb order)

theorem katalog_speicher {initial : Ort → Wert} {vor nach : SpeicherGraph Ort Wert}
    {label : Etikett Ort Wert} {spur : SpeicherSpur Ort Wert}
    (istAussen : label.art = .aussen)
    (folge : Speicherfolge initial .aussen vor [label] spur nach) :
    spur = [(.aussen, label)] ∧ (RennenImGraph vor → RennenImGraph nach) :=
  aussen_label_speicher istAussen folge

/-- A step that adds no effect to the ledger and leaves the authority state alone releases nothing. The holdings of the
    ledger may change (a hand-over of authority moves them): only the effects ledger and the rights are read. -/
theorem wirkungsloser_schritt_wirkungen {vor nach : Zustand L Ort Wert Raum Lok Grund}
    {spur : SchrittSpur Ort Wert} {hw t}
    (keinAbsturz : ¬ Absturz spur) (wirkungen : nach.buchung.wirkungen = vor.buchung.wirkungen)
    (rechte : nach.rechte = vor.rechte) :
    NeueWirkungen vor nach spur [] ∧ FreigabenGueltig vor nach hw t spur [] := by
  refine ⟨Or.inr ⟨keinAbsturz, ?_⟩,
    List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
  · rw [wirkungen, List.append_nil]
  · intro _ obj alive lost
    rw [rechte] at lost
    exact (Bool.false_ne_true (lost.symm.trans alive)).elim

theorem wirkungsloser_schritt {vor nach : Zustand L Ort Wert Raum Lok Grund}
    {spur : SchrittSpur Ort Wert} {hw t}
    (keinAbsturz : ¬ Absturz spur) (buchung : nach.buchung = vor.buchung)
    (rechte : nach.rechte = vor.rechte) :
    NeueWirkungen vor nach spur [] ∧ FreigabenGueltig vor nach hw t spur [] :=
  wirkungsloser_schritt_wirkungen keinAbsturz (congrArg Buchung.wirkungen buchung) rechte

theorem kein_sperrwechsel {vor nach : Zustand L Ort Wert Raum Lok Grund}
    {Bedingung Wahl Form : Type}
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (gleich : nach.sperren = vor.sperren) : InvariantenBeimWechsel E vor nach :=
  fun l wechselt => (wechselt (congrArg SperrZustand.besitzer (congrFun gleich l)).symm).elim

end Gabbro.Core.Sicherheit
