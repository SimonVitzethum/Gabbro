/-
  File:      core/Core/Ast/Semantik/Runtime/ZugriffSicher/RennenBein.lean
  Subject:   THE RACE LEG (the second unit of `ZugriffSicherAussage`), GRAPH PART. A reachable
              graph whose executed accesses all belong to one memory actor is race free: the
              events of one actor are in program order in their append order (`erreichbar_faden`),
              and program order is happens-before. This closes every conflicting pair by its index
              order. WHAT IS NOT PROVED HERE: that the graph of a run of a source unit has all
              executed accesses from the one entry context. The unit's `eintritte` names no
              handler, so only `eintritt` holds arrival regions; a delivered handler has an empty
              arrival list and a refused access records no memory event, and catalogue events carry
              the outside label, which is neither a read nor a write. Those facts are a run
              induction, not a graph fact; the missing step is stated in the companion module.
              No statement is changed and nothing is weakened.
-/
module

public import Core.Ast.Semantik.Runtime.ZugriffSicher.KlassenBein

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Sicherheit (Konflikt AusgefuehrterZugriff RennenImGraph)
open Gabbro.Core.Speicher.Graph (hb_von_po)

/-- **A reachable graph whose executed accesses are all of one actor is race free.** Two
    conflicting events have the same actor, hence stand in program order in their append order;
    program order is happens-before, so one of the two ordering disjuncts holds. -/
theorem rennenAusEinemKontext {Ort Wert : Type} {c : SpeicherAkteur Ort}
    {g : SpeicherGraph Ort Wert} (h : Gabbro.Core.Speicher.Zustand.Erreichbar g)
    (alle : ∀ i (hi : i < g.ev.length), AusgefuehrterZugriff g ⟨i, hi⟩ → (g.ev[i]'hi).kontext = c) :
    RennenImGraph g := by
  intro i j konflikt
  obtain ⟨hne, hiEx, hjEx, _, _, _⟩ := konflikt
  have hiCtx : (g.ev[i.1]'i.2).kontext = c := alle i.1 i.2 hiEx
  have hjCtx : (g.ev[j.1]'j.2).kontext = c := alle j.1 j.2 hjEx
  have gleich : (g.ev[i.1]'i.2).kontext = (g.ev[j.1]'j.2).kontext := hiCtx.trans hjCtx.symm
  rcases Nat.lt_or_gt_of_ne (by
    intro hsame
    apply hne
    exact Fin.ext hsame) with hlt | hgt
  · exact Or.inl (hb_von_po g.graph (Gabbro.Core.Speicher.Zustand.erreichbar_faden h
      i.1 j.1 i.2 j.2 gleich hlt))
  · exact Or.inr (hb_von_po g.graph (Gabbro.Core.Speicher.Zustand.erreichbar_faden h
      j.1 i.1 j.2 i.2 gleich.symm hgt))

end Gabbro.Core.Ast.Semantik
