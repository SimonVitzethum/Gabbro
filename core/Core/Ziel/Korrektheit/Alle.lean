/-
  File:      core/Core/Ziel/Korrektheit/Alle.lean
  Subject:   THE LIST OF CORRECTNESS STATEMENTS, as one pinned proposition.

  Every pinned statement of `Core/Ziel/Korrektheit` is a conjunct here, with its parameters universally
  quantified over platforms `P` and registry evidence `B`. The statements about the deployed checker
  (`Pruefer...`, `PrueferDecktFormenAussage`) and the deployed parser (`ParserKorrektAussage`) are
  EXISTENTIAL: there is a checker `C` and a parser `π` that satisfy them (the witnesses will be the
  concrete checker and parser of the Stage-0/Gabbro implementation). A universal closure over `C` and
  `π` would claim that EVERY checker is correct and non-trivial and EVERY parser agrees with the
  reference relation; a constantly refusing checker refutes that reading (recorded in
  `Core/Ziel/Review/Befunde.lean` as `KorrektheitAussagen.nichtTrivial`). All remaining conjuncts stay
  universally quantified over `P` and `B`.
  The hash pin of `KorrektheitAussagen` covers the dependency closure of all of them, so a statement cannot change
  unnoticed, and one pin root keeps the cost of the pin check constant (each root walks the closure of the whole
  model). The list may only grow; removing or weakening a conjunct is a change of the correctness package.
  Meaning change: from "every checker and every parser" to "there is a checker and there is a parser".
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Frontend
public import Core.Ziel.Korrektheit.Speicher

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

def KorrektheitAussagen : Prop :=
  ∀ (P : Katalog.Plattform) (B : FormBeleg),
    (∃ C : Pruefer,
      PrueferLokalKorrektAussage C ∧ PrueferLokalVollstaendigAussage C ∧
      PrueferKlauselnKorrektAussage C ∧ PrueferKlauselnVollstaendigAussage C ∧
      PrueferWaechterKorrektAussage C ∧ PrueferWaechterVollstaendigAussage C ∧
      PrueferKorrektAussage C ∧ PrueferVollstaendigAussage C ∧ PrueferNichtTrivialAussage C ∧
      PrueferDecktFormenAussage C B)
    ∧ (∃ π : Parser, ParserKorrektAussage π)
    ∧ (PrueferRestUnentscheidbarAussage ∧
      ParseDruckAussage ∧ ParseEindeutigAussage ∧ ElabKorrektAussage P ∧ BezeichnetFunktionalAussage P ∧
      TextWohlgeformtAussage P ∧ RealisiertAlleFormenAussage ∧
      GraphmaschineAequivalentAussage ∧ KohaerenzKatalogAussage ∧ RmwNichtDoppeltAussage ∧
      RmwAtomarAussage ∧ IriwScVerbotenAussage ∧ IriwRaErlaubtAussage ∧
      ProtokollSchrittErhaeltAussage ∧ ProtokollStartGutAussage ∧ ProtokollGutImLaufAussage ∧
      IdealProtokollGutImLaufAussage ∧ ImplBestimmtAussage ∧ IdealAkzeptierteEinheitAussage ∧
      VerfeinerungAkzeptiertAussage ∧ ZielFXAkzeptiertAussage ∧ FortschrittAkzeptiertAussage ∧
      RegelSimDiskriminiertAussage ∧ SimTrenntAussage ∧ SimRefutierbarAussage ∧
      BildGueltigAussage P ∧ FormenGedecktAussage P B ∧ SchrankenAkzeptiertAussage P ∧ NIAkzeptiertAussage P ∧
      ZielAusTeilenAussage P B ∧ SicherheitAkzeptiertAussage P ∧ SicherheitNichtLeerInstanzAussage P B ∧
      SicherheitAusTeilenAussage P B ∧ ZielInhaltAussage P ∧ LinkerAkzeptiertAussage ∧
      LinkerNichtTrivialAussage)

end Gabbro.Core.Ziel.Korrektheit
