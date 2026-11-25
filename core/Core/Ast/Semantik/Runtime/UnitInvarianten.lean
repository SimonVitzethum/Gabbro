/-
  File:      core/Core/Ast/Semantik/Runtime/UnitInvarianten.lean
  Subject:   DECLARED UNIT INVARIANTS (MK-19 design step 1): a source unit together with the
             invariants it declares, elaborated into the fragment's clause table, plus the
             checker's first decidable preservation fragment.

  A unit carries a list of declared invariants — predicates over the observable unit state
  (`Zustand`), shaped like `Sicherheit.Invariante.gilt` and stored like
  `Quellklauseln.invariant`. Elaboration (`programmMitInvarianten`) keeps the code, entries
  and memory plan of `programm` and fills only the clause table, so
  `Fragment.sicherheitsEinheit` (and through it `sicherheitVon`) carries them with no lock
  scope, exactly as `KlauselnWahr` and `InvariantenErhalten` read them.

  `programm_keine_invarianten` is untouched: it speaks about `programm`, not about
  `programmMitInvarianten`. Removing it (with the migration of its use sites to
  `programmMitInvarianten_klauseln`) and the syntax-level change (the grammar must parse
  the declarations into `UnitMitInvarianten`) are the documented follow-ups MK-19/2 and
  MK-19/3 below.

  The checker decides preservation per command on the trivial fragment only
  (`pruefeBefehlErhalt`: every declared invariant is certified `True`, hence preserved by
  every step). Assignment preservation outside a footprint is the documented next case
  (MK-19/4): footprint-indexed invariants with a stability certificate plus a per-command
  write set (`Befehl.schreibFussabdruck`) proved against `Befehl.nach`. Anything the
  checker does not decide stays user duty (GabbroProve over `RegelSicher`).

  Open units:
  * MK-19/2 (Prover): drop `programm_keine_invarianten` (no legacy); migrate its use
    sites (`Runtime/Sicherheit.lean`, `ProgramObligations.lean`, `Function.lean`,
    `TextValue/*Proofs.lean`, batch/form proofs) to `programmMitInvarianten_klauseln`;
    generalise `fragment_sicher` (`GrenzenSicher` + `RegelPflichten`) to non-empty
    tables and re-prove `sicherheitAkzeptiert` over elaborated units with invariants.
  * MK-19/3 (Designer): surface syntax for unit-level invariant declarations with
    `UnitReads`/`printPieces`/`Category` round-trip (`reads_print`, `unique`), so the
    parser denotes `UnitMitInvarianten` instead of `Ast.Unit`.
  * MK-19/4 (Designer + Prover): footprint fragment (`beobachtet : List Zelle`,
    `stabil`, `Befehl.schreibFussabdruck` with soundness against `Befehl.nach`) and its
    per-command preservation proof feeding `RegelSicher`.
  * MK-19/5 (Prover): run-level refutation `∃ H ρ, Laeufe ∧ ¬ InvariantenErhalten` at an
    elaborated unit with a declared invariant (feeders: `Plattform.katalog_wohlgeformt`,
    `Laufkonstruktion.bild_gueltig`, `lauf_erfuellbar`, as in
    `sicherheit_aus_regeln_erfuellbar`); this is the `InvariantenErhalten` conjunct of
    `SicherheitNichtLeer` over `R₀`.
-/
module

public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Sicherheit Katalog

/-- A source unit together with the invariants it declares. The observable state is the
    unit state `Zustand`; the shape follows `Sicherheit.Invariante.gilt`. Units carry no
    lock scope (cf. `sicherheitVon`, which maps every clause predicate to `⟨none, ·⟩`). -/
structure UnitMitInvarianten where
  baum : Ast.Unit
  invarianten : List (Zustand → Prop)

/-- Elaboration carries the declared invariants into the fragment's clause table. Code,
    entries and memory plan are those of `programm`. -/
def programmMitInvarianten (u : UnitMitInvarianten) : Fragment :=
  { programm u.baum with klauseln := ⟨[], [], u.invarianten⟩ }

theorem programmMitInvarianten_klauseln (u : UnitMitInvarianten) :
    (programmMitInvarianten u).klauseln.invariant = u.invarianten := rfl

def elaborierenMitInvarianten (platform : Plattform) (u : UnitMitInvarianten) : Einheit :=
  (programmMitInvarianten u).einheit platform

theorem sicherheitsEinheit_invarianten (u : UnitMitInvarianten) (platform : Plattform) :
    ((programmMitInvarianten u).sicherheitsEinheit platform).invarianten =
      u.invarianten.map fun gilt => (⟨none, gilt⟩ : Invariante Nat Zustand) := rfl

/-- The declared part of `InvariantenAmSchnitt`: every tabled invariant holds outside its
    writers. Follows from `InvariantenAmSchnitt` by projection (`deklariertHalten_aus_schnitt`). -/
def DeklariertHalten
    (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl) (s : Zustand) : Prop :=
  ∀ i d, E.invarianten[i]? = some d →
    (∀ c, s.status c = .laeuft → ¬ s.buchung.schreibt c i) → d.gilt s

theorem deklariertHalten_aus_schnitt
    (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl) (s : Zustand)
    (h : InvariantenAmSchnitt E s) : DeklariertHalten E s :=
  fun i d get w => h.2 i d get w

/-- A declared invariant in the checker's decidable fragment. The flag names the trivial
    case; `treu` ties the flag to the predicate. Invariants with `trivial = false` are
    user proof duty; the checker refuses them. -/
structure PruefInvariante where
  gilt : Zustand → Prop
  trivial : Bool
  treu : trivial = true → gilt = fun _ => True

/-- The checker decides preservation per command on the trivial fragment: accept iff every
    declared invariant is certified trivial (hence preserved by every step, including the
    loader, answer, interrupt and crash boundaries). -/
def pruefeBefehlErhalt (invs : List PruefInvariante) (_ : Befehl) : Bool :=
  invs.all fun inv => inv.trivial

theorem pruefInvariante_hält (inv : PruefInvariante) (ok : inv.trivial = true) (s : Zustand) :
    inv.gilt s := by
  have h := inv.treu ok
  simp only [h]

theorem pruefeBefehlErhalt_richtig (u : UnitMitInvarianten) (invs : List PruefInvariante)
    (b : Befehl) (abbild : u.invarianten = invs.map PruefInvariante.gilt)
    (ok : pruefeBefehlErhalt invs b = true) (platform : Plattform) (s : Zustand) :
    DeklariertHalten ((programmMitInvarianten u).sicherheitsEinheit platform) s := by
  intro i d get w
  rw [sicherheitsEinheit_invarianten, abbild, List.getElem?_map] at get
  obtain ⟨a, hsome, rfl⟩ := Option.map_eq_some_iff.mp get
  rw [List.getElem?_map] at hsome
  obtain ⟨inv, hsome, rfl⟩ := Option.map_eq_some_iff.mp hsome
  have hmem : inv ∈ invs := List.mem_of_getElem? hsome
  have htrivial : inv.trivial = true := List.all_eq_true.mp ok inv hmem
  exact pruefInvariante_hält inv htrivial s

/-- The refusal witness: an invariant the checker rejects (flag `false`). -/
def falschInvariante : PruefInvariante :=
  ⟨fun _ => False, false, fun h => (Bool.false_ne_true h).elim⟩

theorem nichtTrivial_ablehnung :
    pruefeBefehlErhalt [falschInvariante] .ende = false := rfl

/-- The violation the model can represent: the empty state breaks the false invariant of
    an elaborated unit that declares it. Together with `nichtTrivial_ablehnung` this is
    the `_nichtTrivial` leg: violation and refusal for the same declared invariant. -/
theorem nichtTrivial_verletzbar :
    ∃ s : Zustand, ¬ DeklariertHalten
      ((programmMitInvarianten ⟨⟨[], .done⟩, [fun _ => False]⟩).sicherheitsEinheit .x86_64) s := by
  refine ⟨Leerzustand, fun h => ?_⟩
  have h0 : ((programmMitInvarianten ⟨⟨[], .done⟩, [fun _ => False]⟩).sicherheitsEinheit
      .x86_64).invarianten[0]? = some (⟨none, fun _ => False⟩ : Invariante Nat Zustand) := rfl
  have w : ∀ c, Leerzustand.status c = .laeuft → ¬ Leerzustand.buchung.schreibt c 0 :=
    fun _ _ schreibt => schreibt
  exact h 0 _ h0 w

end Gabbro.Core.Ast.Semantik
