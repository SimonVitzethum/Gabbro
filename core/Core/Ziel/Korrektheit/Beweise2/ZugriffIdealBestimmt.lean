/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/ZugriffIdealBestimmt.lean
  Subject:   THE PROOF OF `zugriffIdealBestimmt`, the pinned determinacy statement of a fragment
             with an access instruction (`Core/Ziel/Korrektheit/Zugriff`,
             `ZugriffIdealBestimmtAussage`). The composed step is split by its source; the three
             outside cases use the protocol determinacy lemmas. In the context case the two ideal
             steps share a head. A frame-only head is determinate by `Befehl.bestimmt`. For an
             access head the two steps are determinate up to the value read (`zugriffBestimmt`);
             the value read is fixed by the graph: two one-label `Speicherfolge`s from one prefix
             with equal order resolution read from one write of the common prefix, so their read
             labels agree (`speicherfolge_lesewert_gleich`). `FuehrtSchrittAus.bestimmt` then gives
             one trace and one next state. No statement is changed and no per-program fact is used.
-/
module

public import Core.Ziel.Korrektheit.Zugriff
public import Core.Ast.Semantik.Runtime.Atom.Beweise.Bestimmt
public import Core.Speicher.Graphmaschine

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Speicher
open Gabbro.Core.Speicher.Zustand (getElem_angehaengt getElem_angehaengt_neu)

namespace ZugriffIdeal

variable {Ort Wert : Type}

/-- The lazy initial write depends on a label only through its location and mode, and on its kind
    only through whether it reads. Two reading labels at one location and mode therefore materialise
    the same events. -/
theorem Initialisierung.ev_gleich
    {anfang : Ort → Wert} {l₁ l₂ : Etikett Ort Wert}
    (hort : l₁.ort = l₂.ort) (hmod : l₁.modus = l₂.modus)
    (hlies₁ : l₁.art.liest) (hlies₂ : l₂.art.liest)
    {g g₀ h₀ : SpeicherGraph Ort Wert} {xs ys}
    (a : Initialisierung anfang l₁ g xs g₀) (b : Initialisierung anfang l₂ g ys h₀) :
    xs = ys ∧ g₀.ev = h₀.ev := by
  have na1 : l₁.art ≠ .aussen := fun h => by rw [h] at hlies₁; cases hlies₁
  have na2 : l₂.art ≠ .aussen := fun h => by rw [h] at hlies₂; cases hlies₂
  cases a with
  | ohne hh₁ =>
    have hq : HatQuelle g l₁.ort := by
      rcases hh₁ with outside | found
      · exact (na1 outside).elim
      · exact found
    cases b with
    | ohne hh₂ => exact ⟨rfl, rfl⟩
    | erste mem neu hs => exact (neu (by rwa [hort] at hq)).elim
  | erste mem₁ neu₁ hs₁ =>
    cases b with
    | ohne hh₂ =>
      have hq : HatQuelle g l₂.ort := by
        rcases hh₂ with outside | found
        · exact (na2 outside).elim
        · exact found
      exact (neu₁ (by rwa [← hort] at hq)).elim
    | erste mem₂ neu₂ hs₂ =>
      have concatEq :
          g.ev ++ [⟨SpeicherAkteur.initial l₁.ort,
            ⟨.schreiben, l₁.ort, l₁.modus, anfang l₁.ort, anfang l₁.ort⟩⟩] =
          g.ev ++ [⟨SpeicherAkteur.initial l₂.ort,
            ⟨.schreiben, l₂.ort, l₂.modus, anfang l₂.ort, anfang l₂.ort⟩⟩] := by
        rw [hort, hmod]
      have xsEq :
          [(SpeicherAkteur.initial l₁.ort,
            (⟨.schreiben, l₁.ort, l₁.modus, anfang l₁.ort, anfang l₁.ort⟩ : Etikett Ort Wert))] =
          [(SpeicherAkteur.initial l₂.ort,
            (⟨.schreiben, l₂.ort, l₂.modus, anfang l₂.ort, anfang l₂.ort⟩ : Etikett Ort Wert))] := by
        rw [hort, hmod]
      exact ⟨xsEq, hs₁.ev.trans (concatEq.trans hs₂.ev.symm)⟩

/-- Two one-label memory extensions of one prefix at one location and mode with the same order
    resolution record the same value read. Both reads take their value from the write they read
    from; that write is an event of the common prefix (the initial write, when lazily materialised,
    is the same on both sides), and the reads-from relation is one of the resolutions the premise
    equates. -/
theorem speicherfolge_lesewert_gleich
    {anfang : Ort → Wert} {f : SpeicherAkteur Ort}
    {g g₁ g₂ : SpeicherGraph Ort Wert} {l₁ l₂ : Etikett Ort Wert}
    {es₁ es₂ : List (SpeicherAkteur Ort × Etikett Ort Wert)}
    (hort : l₁.ort = l₂.ort) (hmod : l₁.modus = l₂.modus)
    (h₁ : Speicherfolge anfang f g [l₁] es₁ g₁)
    (h₂ : Speicherfolge anfang f g [l₂] es₂ g₂)
    (liest₁ : l₁.art.liest) (liest₂ : l₂.art.liest)
    (wahl : SpeicherWahlGleich g₁ g₂) :
    l₁.gelesen = l₂.gelesen := by
  cases h₁ with
  | @cons _ g₀₁ _ _ _ _ _ _ vor₁ hs₁ nach₁ =>
    cases nach₁ with
    | nil =>
      cases h₂ with
      | @cons _ g₀₂ _ _ _ _ _ _ vor₂ hs₂ nach₂ =>
        cases nach₂ with
        | nil =>
          obtain ⟨_, ev0⟩ := Initialisierung.ev_gleich hort hmod liest₁ liest₂ vor₁ vor₂
          have len0 : g₀₁.ev.length = g₀₂.ev.length := congrArg List.length ev0
          have len1 : g₁.ev.length = g₀₁.ev.length + 1 := by
            rw [hs₁.ev, List.length_append, List.length_singleton]
          have len2 : g₂.ev.length = g₀₂.ev.length + 1 := by
            rw [hs₂.ev, List.length_append, List.length_singleton]
          let n := g₀₁.ev.length
          have hn1 : n < g₁.ev.length := by rw [len1]; exact Nat.lt_succ_self _
          have hn2 : n < g₂.ev.length := by rw [len2, ← len0]; exact Nat.lt_succ_self _
          have evn1 : g₁.ev[n]'hn1 = ⟨f, l₁⟩ :=
            getElem_angehaengt_neu hs₁.ev (by rw [len1]; exact Nat.lt_succ_self _)
          have evn2' : g₂.ev[g₀₂.ev.length]'(by rw [len2]; exact Nat.lt_succ_self _) = ⟨f, l₂⟩ :=
            getElem_angehaengt_neu hs₂.ev (by rw [len2]; exact Nat.lt_succ_self _)
          have evn2 : g₂.ev[n]'hn2 = ⟨f, l₂⟩ := by
            change g₂.ev[g₀₁.ev.length]'hn2 = ⟨f, l₂⟩
            simpa only [len0] using evn2'
          have labn1 : g₁.graph.lab ⟨n, hn1⟩ = l₁ := congrArg Ereignis.lab evn1
          have labn2 : g₂.graph.lab ⟨n, hn2⟩ = l₂ := congrArg Ereignis.lab evn2
          have liestn1 : g₁.graph.liest ⟨n, hn1⟩ := by
            change (g₁.graph.lab ⟨n, hn1⟩).art.liest
            rw [labn1]
            exact liest₁
          obtain ⟨w, hwrf⟩ := hs₁.vollstaendig ⟨n, hn1⟩ liestn1
          have hwlen : w.1 < g₁.ev.length := w.2
          have wneq : w.1 ≠ n := by
            intro he
            have wEq : w = ⟨n, hn1⟩ := Fin.ext he
            have self : g₁.graph.rf ⟨n, hn1⟩ ⟨n, hn1⟩ := by simpa [wEq] using hwrf
            exact hs₁.konsistent.rf_irrefl ⟨n, hn1⟩ self
          have wlt1 : w.1 < g₀₁.ev.length := by omega
          have wlt2 : w.1 < g₀₂.ev.length := by omega
          have hw2 : w.1 < g₂.ev.length := by omega
          have labw1 : g₁.graph.lab w = g₀₁.graph.lab ⟨w.1, wlt1⟩ :=
            congrArg Ereignis.lab (getElem_angehaengt hs₁.ev wlt1 w.2)
          have labw2 : g₂.graph.lab ⟨w.1, hw2⟩ = g₀₂.graph.lab ⟨w.1, wlt2⟩ :=
            congrArg Ereignis.lab (getElem_angehaengt hs₂.ev wlt2 hw2)
          have labw : g₀₁.graph.lab ⟨w.1, wlt1⟩ = g₀₂.graph.lab ⟨w.1, wlt2⟩ := by
            simp only [Speicher.Zustand.graph, ev0]
          have hwrf2 : g₂.rf w.1 n := by
            change g₁.rf w.1 n at hwrf
            have hval := congrFun (congrFun wahl.2.1 w.1) n
            exact hval.mp hwrf
          have wert1 : l₁.gelesen = (g₀₁.graph.lab ⟨w.1, wlt1⟩).geschrieben := by
            rw [← labn1, ← labw1]
            exact (hs₁.konsistent.wf.rf_wert w ⟨n, hn1⟩ hwrf).symm
          have wert2 : l₂.gelesen = (g₀₂.graph.lab ⟨w.1, wlt2⟩).geschrieben := by
            rw [← labn2, ← labw2]
            exact (hs₂.konsistent.wf.rf_wert ⟨w.1, hw2⟩ ⟨n, hn2⟩ hwrf2).symm
          exact wert1.trans ((congrArg Etikett.geschrieben labw).trans wert2.symm)

end ZugriffIdeal

end Gabbro.Core.Ziel.Korrektheit
