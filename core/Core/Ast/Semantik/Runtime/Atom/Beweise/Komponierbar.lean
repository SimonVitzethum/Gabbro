/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Beweise/Komponierbar.lean
  Subject:   THE COMPOSABILITY OF AN ACCESS STEP WITH THE MACHINE FRAME (`ZugriffKomponierbarAussage`).
             A step of `Befehl.zugriff` that the memory model accepts (its labels extend the state's graph
             by an RC11-consistent `Speicherfolge`) is a machine step: the access changes only the acting
             frame and the ledger, every label it records reads, its action is internal, so the protocol
             contributes `FuehrtAus.intern` with no lock or outside event, and the given `Speicherfolge`
             is replayed unchanged with the state `{ u with graph := g }`.
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Aussagen
public import Core.Ast.Semantik.Runtime.Regeln

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett Modus Art)

/-- An update records an event that always reads: a failed compare-and-swap is a load, every other
    update is a read-modify-write. -/
theorem aenderung_art_liest (a : Aenderung) (v : Int) : (a.art v).liest := by
  cases a with
  | tausche => simp only [Aenderung.art, Art.liest]
  | addiere => simp only [Aenderung.art, Art.liest]
  | vergleiche erwartet =>
    by_cases h : v = erwartet
    · simp only [Aenderung.art, h, ↓reduceIte, Art.liest]
    · simp only [Aenderung.art, h, ↓reduceIte, Art.liest]

/-- An access step changes only the acting frame and the ledger. The machine frame -- graph, cores,
    locks, questions, answers, consumption, history, delivery and the invariant fields -- is untouched,
    so the frame relation the machine step asks for holds between the pre-state and the post-state. -/
theorem zugriffsschritt_rahmen (F : Schrittform) (c : Kontext) (s u : Zustand) {p : Plan}
    (h : F.zugriffsschritt c s [p] u) : Zustandsrahmen s u := by
  rcases h with ⟨_, _, hu⟩ | ⟨_, _, _, _, hu⟩
  · subst u
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · subst u
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every label a class step puts into its read list is a reading label: a load records `.lesen`, an
    update records `.rmw` or the failed compare-and-swap's `.lesen`, a store, lock, question and private
    step record none, and a refused access records none. -/
theorem zugriffsschritt_liest (F : Schrittform) (c : Kontext) (s u : Zustand) {p : Plan}
    (h : F.zugriffsschritt c s [p] u) : ∀ l ∈ p.lesen, l.art.liest := by
  obtain ⟨k, o, t⟩ := F
  rcases h with ⟨_, hp, _⟩ | ⟨_, v, _, hp, _⟩
  · have heq : p = Semantik.plan := (List.cons.inj hp).1
    subst p
    intro l hl
    simp only [Semantik.plan] at hl
    cases hl
  · have heq : p = Wirkungsklasse.plan k (o (s.lokal c)) v := (List.cons.inj hp).1
    subst p
    cases k with
    | lokal =>
      intro l hl
      simp only [Wirkungsklasse.plan, Semantik.plan] at hl
      cases hl
    | ruf =>
      intro l hl
      simp only [Wirkungsklasse.plan, Semantik.plan] at hl
      cases hl
    | zaun m =>
      intro l hl
      simp only [Wirkungsklasse.plan, Semantik.plan] at hl
      cases hl
    | lesen m =>
      intro l hl
      simp only [Wirkungsklasse.plan, List.mem_singleton] at hl
      subst l
      simp only [Art.liest]
    | schreiben m =>
      intro l hl
      simp only [Wirkungsklasse.plan] at hl
      cases hl
    | rmw m =>
      intro l hl
      simp only [Wirkungsklasse.plan, List.mem_singleton] at hl
      subst l
      exact aenderung_art_liest (o (s.lokal c)).aenderung v
    | sperre a =>
      intro l hl
      simp only [Wirkungsklasse.plan] at hl
      cases hl
    | frage =>
      intro l hl
      have hleer := Operand.fragePlan_leer (o (s.lokal c))
      simp only [Wirkungsklasse.plan] at hl
      rw [hleer.1] at hl
      cases hl
    | starte =>
      intro l hl
      simp only [Wirkungsklasse.plan, planMit] at hl
      cases hl
    | beende =>
      intro l hl
      simp only [Wirkungsklasse.plan, planMit] at hl
      cases hl
    | verbinde =>
      intro l hl
      simp only [Wirkungsklasse.plan, planMit] at hl
      cases hl
    | wechsle =>
      intro l hl
      simp only [Wirkungsklasse.plan, planMit] at hl
      cases hl

/-- **Composability of the accepted steps of an access instruction** (`ZugriffKomponierbarAussage`).
    The step changes the machine frame only locally, its recorded labels all read, and its action is
    internal. With the empty protocol and outside trace and the state `{ u with graph := g }`,
    `FuehrtAus.intern` supplies the protocol action and the supplied `Speicherfolge` is replayed
    unchanged. -/
theorem zugriffKomponierbar : ZugriffKomponierbarAussage := by
  intro p platform z t s c w plan u es g _hkopf hstep hfolge
  let F : Schrittform := (Befehl.zugriff z).form
  have hschritt : F.zugriffsschritt c s [plan] u := by
    dsimp [F]
    cases z <;> simpa only [Befehl.ideal, Befehl.form, Befehl.klasse, Zugriffsform.klasse,
      Schrittform.ideal] using hstep
  have hrahmen : Zustandsrahmen s u := zugriffsschritt_rahmen F c s u hschritt
  have hliest : ∀ l ∈ plan.lesen, l.art.liest := zugriffsschritt_liest F c s u hschritt
  have hakt : plan.aktion = .intern := by
    rcases hschritt with ⟨_, hp, _⟩ | ⟨_, v, _, hp, _⟩
    · have e : plan = Semantik.plan := (List.cons.inj hp).1
      subst e
      rfl
    · have e : plan = F.plan (s.lokal c) v := (List.cons.inj hp).1
      subst e
      cases z <;> rfl
  refine ⟨⟨es, []⟩, { u with graph := g }, ?_⟩
  unfold FuehrtSchrittAus
  refine ⟨hrahmen, hliest, [], u, ?_, ?_, ?_⟩
  · rw [hakt]
    exact FuehrtAus.intern
  · simpa only [List.nil_append, List.map_nil, List.append_nil] using hfolge
  · rfl

end Gabbro.Core.Ast.Semantik
