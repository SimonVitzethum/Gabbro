/-
  File:      core/Core/Ast/Semantik/Runtime/UnitInvarianten.lean
  Subject:   DECLARED UNIT INVARIANTS (MK-19 design step 2): a source unit with the invariants it
             declares as expressions of the decidable predicate language, the checker's footprint
             rule, and the safety of checker-accepted elaborated units with invariants.

  `UnitMitInvarianten` and `programmMitInvarianten` live in `Elaborierung` (below the checker);
  the clause table of an elaborated unit is exactly the denotations of its declared predicates
  (`programmMitInvarianten_klauseln`, `rfl`), so `programm_keine_invarianten` is gone: plain
  units elaborate with the empty list and safety is proved for tables of predicate denotations
  accepted by the checker.

  The checker decides preservation per command in the decidable fragment
  (`Pruefung.pruefeBefehlErhalt`: disjointness of observed cells and write footprint) and the
  loader and crash-recovery premises on the memory plan (`pruefeStart`, `pruefeNeustart`);
  `pruefeEinheit` conjoins the three. `InvariantenSicherheitAussage` is the safety of
  checker-accepted elaborated units with invariants; anything the checker does not decide stays
  user duty (GabbroProve over `RegelSicher`).

  Open units:
  * MK-19/3 (Designer): surface syntax for unit-level invariant declarations with
    `UnitReads`/`printPieces`/`Category` round-trip (`reads_print`, `unique`), so the parser
    denotes `UnitMitInvarianten` instead of `Ast.Unit`.
  * MK-19/4 (Designer + Prover): memory commands (MK-04) populate `Befehl.schreibFussabdruck`
    and prove the conditional `fussabdruck_treu`; the stability certificate
    `Praedikat.haelt_stabil` already carries the rule.
  * MK-19/5 (Prover): the four falsifications at `Ast.Semantik.Einheit` for
    `SicherheitNichtLeerInstanzAussage` (the `InvariantenErhalten` conjunct over `R₀`).
-/
module

public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Pruefung.Praedikat
public import Core.Sicherheit.RegelnErfuellbar

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Sicherheit Katalog Pruefung

def elaborierenMitInvarianten (platform : Plattform) (u : UnitMitInvarianten) : Einheit :=
  (programmMitInvarianten u).einheit platform

theorem sicherheitsEinheit_invarianten (u : UnitMitInvarianten) (platform : Plattform) :
    ((programmMitInvarianten u).sicherheitsEinheit platform).invarianten =
      (u.invarianten.map Pruefung.Praedikat.gilt).map
        fun gilt => (⟨none, gilt⟩ : Invariante Nat Zustand) := rfl

/-- The declared part of `InvariantenAmSchnitt`: every tabled invariant holds outside its
    writers. -/
def DeklariertHalten
    (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl) (s : Zustand) : Prop :=
  ∀ i d, E.invarianten[i]? = some d →
    (∀ c, s.status c = .laeuft → ¬ s.buchung.schreibt c i) → d.gilt s

/-- EVERY RUN OF A CHECKER-ACCEPTED ELABORATED UNIT WITH INVARIANTS IS SAFE (the pinned
    `InvariantenSicherheitAussage` of MK-19 step 2): memory safety, preservation of the
    declared predicate invariants, race freedom and TOCTOU freedom hold on every run. The
    checker verdict `pruefeEinheit` supplies the loader, crash-recovery and per-command
    premises of `fragment_sicher`; anything it does not decide stays user duty. -/
def InvariantenSicherheitAussage (P : Plattform) : Prop :=
  ∀ (u : UnitMitInvarianten),
    pruefeEinheit (programmMitInvarianten u) u.invarianten = true →
    ∀ (H : Katalog.Umgebung) (ρ : Sicherheit.Lauf ((programmMitInvarianten u).sicherheitsEinheit P)),
      Laeufe (elaborierenMitInvarianten P u) H ρ →
        Speichersicher ((programmMitInvarianten u).sicherheitsEinheit P) H ρ ∧
        InvariantenErhalten ((programmMitInvarianten u).sicherheitsEinheit P) H ρ ∧
        Rennfrei ((programmMitInvarianten u).sicherheitsEinheit P) H ρ ∧
        ToctouFrei ((programmMitInvarianten u).sicherheitsEinheit P) H ρ

/-- Checker-accepted units with invariants elaborate to safe units. -/
theorem invariantenSicherheit (P : Plattform) : InvariantenSicherheitAussage P := by
  intro u ok H ρ lauf
  exact fragment_sicher (programmMitInvarianten u) P u.invarianten
    (programmMitInvarianten_klauseln u) ok H ρ lauf

/-- The checker premises hold jointly: the empty unit with a satisfied predicate passes. -/
theorem InvariantenSicherheitAussage.erfuellbar :
    ∃ (P : Plattform) (u : UnitMitInvarianten),
      pruefeEinheit (programmMitInvarianten u) u.invarianten = true := by
  refine ⟨.x86_64, ⟨⟨[], .done⟩,
    [Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 0)]⟩, ?_⟩
  rfl

/-- The checker refuses a unit whose plan breaks its invariant, and the model exhibits the
    violating state: safety with invariants is not trivially true. -/
theorem InvariantenSicherheitAussage.nichtTrivial :
    ∃ (u : UnitMitInvarianten),
      pruefeEinheit (programmMitInvarianten u) u.invarianten = false ∧
      ∃ (s : Zustand),
        ¬ DeklariertHalten ((programmMitInvarianten u).sicherheitsEinheit .x86_64) s := by
  refine ⟨⟨⟨[], .done⟩,
    [Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 5)]⟩, ?_, ?_⟩
  · rfl
  · refine ⟨Leerzustand, fun h => ?_⟩
    have h0 : (((programmMitInvarianten
      ⟨⟨[], .done⟩, [Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 5)]⟩).sicherheitsEinheit
        .x86_64)).invarianten[0]? =
      some (⟨none, Praedikat.gilt
        (Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 5))⟩ :
        Invariante Nat Zustand) := rfl
    have w : ∀ c, Leerzustand.status c = .laeuft → ¬ Leerzustand.buchung.schreibt c 0 :=
      fun _ _ schreibt => schreibt
    have hg := h 0 _ h0 w
    simp only [Praedikat.gilt, Praedikat.haelt, Vergleich.haelt, Ausdruck.wert] at hg
    have hzero : Leerzustand.initial (.region 0 0) = 0 := rfl
    rw [hzero] at hg
    omega

end Gabbro.Core.Ast.Semantik
