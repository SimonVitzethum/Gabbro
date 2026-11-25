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
  (`pruefeBefehlErhalt`: disjointness of observed cells and write footprint) and the
  loader and crash-recovery premises on the memory plan (`pruefeStart`, `pruefeNeustart`);
  `pruefeEinheit` conjoins the three. `InvariantenSicherheitAussage` is the safety of
  checker-accepted elaborated units with invariants; anything the checker does not decide stays
  user duty (GabbroProve over `RegelSicher`).

  Open units:
  * MK-19/3 (Designer): surface syntax for unit-level invariant declarations with
    `UnitReads`/`printPieces`/`Category` round-trip (`reads_print`, `unique`), so the parser
    denotes `UnitMitInvarianten` instead of `Ast.Unit`.
  * MK-19/4 (Designer + Prover): memory commands (MK-04) populate `Befehl.schreibtMoeglich` (`Atom/Fussabdruck`)
    and prove the conditional `fussabdruck_treu`; the stability certificate
    `Praedikat.haelt_stabil` already carries the rule.
  * MK-19/5 (Prover): the four falsifications at `Ast.Semantik.Einheit` for
    `SicherheitNichtLeerInstanzAussage` (the `InvariantenErhalten` conjunct over `R₀`).
-/
module

public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Praedikat
public import Core.Ast.Semantik.Runtime.Atom.Rein
public import Core.Ast.Semantik.Runtime.Atom.Klassenrein
public import Core.Sicherheit.RegelnErfuellbar

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Sicherheit Katalog

def elaborierenMitInvarianten (platform : Plattform) (u : UnitMitInvarianten) : Einheit :=
  (programmMitInvarianten u).einheit platform

theorem sicherheitsEinheit_invarianten (u : UnitMitInvarianten) (platform : Plattform) :
    ((programmMitInvarianten u).sicherheitsEinheit platform).invarianten =
      (u.invarianten.map Praedikat.gilt).map
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

/-- **The fragment of a source unit**: the elaboration of a source tree, with or without declared invariants. -/
def Fragment.Quelleinheit (p : Fragment) : Prop :=
  (∃ u : UnitMitInvarianten, p = programmMitInvarianten u) ∨ ∃ t : Ast.Unit, p = programm t

/-- **The four safety legs for the unit of a source tree with an access instruction** (MK-04b). The fragment of a source
    unit has only frame-only and access instructions (`programm_klassenrein`), an access instruction among them, and the
    checker's verdict on its declared invariants (`pruefeEinheit`: loader, restart and per-command premises, the
    command premise refusing an invariant that observes a cell an access may write, `Befehl.schreibtMoeglich`). Every run
    is memory safe, keeps the declared invariants, is race free and is TOCTOU free. Difficulty: schwer. Sketch: three
    independent units. (1) The class-determined legs (`klassenSicherheit`: booking, register, commit, questions) hold for
    every step of an access (`Befehl.eingebettet`), so `Speichersicher` and `ToctouFrei` follow by the induction of
    `sicherheit_aus_regeln` once its per-step race leg is replaced by a run invariant: `RegelSicher.rennen` quantifies
    over EVERY pre-state, so for a plain store it fails for a state with an unordered conflicting write, while the
    induction carries `RennenImGraph` along the run (`SchnittSicher`). (2) The race leg: a source unit runs in ONE
    context (no source form starts a thread or a handler: `eintritte` has only the entry), whose events are ordered by
    its program order, so every conflicting pair is ordered and `RennenImGraph` holds; a unit that starts threads needs
    the lock-window discipline instead (`Speicher.Graph.Abschnitte` with `rennfreiAusLokal`, finding MK-05 in
    `Sicherheit/Atom/RennfreiAusLokal`). (3) `InvariantenErhalten`: the checker's per-command verdict plus
    `Befehl.plan_schreibt_fussabdruck` (the footprint is sound against the plan of the access). NOTE: the denotation
    `Praedikat.gilt` reads `s.initial`, which no step changes (a store is an event of the graph), so the leg is only as
    strong as that denotation: it must read the CURRENT content of the cell (the last write of the graph) before the
    footprint carries meaning. -/
def ZugriffSicherAussage : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (ps : List Praedikat), p.Quelleinheit → p.MitZugriff →
    p.klauseln.invariant = ps.map Praedikat.gilt → pruefeEinheit p ps = true →
    ∀ (H : Katalog.Umgebung) (ρ : Sicherheit.Lauf (p.sicherheitsEinheit platform)),
      Laeufe (p.einheit platform) H ρ →
        Speichersicher (p.sicherheitsEinheit platform) H ρ ∧
        InvariantenErhalten (p.sicherheitsEinheit platform) H ρ ∧
        Rennfrei (p.sicherheitsEinheit platform) H ρ ∧
        ToctouFrei (p.sicherheitsEinheit platform) H ρ

/-- Checker-accepted units with invariants elaborate to safe units: a frame-only fragment by `fragment_sicher`, a fragment
    with an access instruction by the pinned `ZugriffSicherAussage`. -/
theorem invariantenSicherheit (P : Plattform) (zugriff : ZugriffSicherAussage) :
    InvariantenSicherheitAussage P := by
  intro u ok H ρ lauf
  by_cases rein : (programmMitInvarianten u).Rein
  · exact fragment_sicher (programmMitInvarianten u) P u.invarianten
      (programmMitInvarianten_klauseln u) ok rein H ρ lauf
  · exact zugriff (programmMitInvarianten u) P u.invarianten (Or.inl ⟨u, rfl⟩)
      ⟨programm_klassenrein u.baum, rein⟩ (programmMitInvarianten_klauseln u) ok H ρ lauf

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
