/-
  File:      core/Core/Ziel/Korrektheit/Alle.lean
  Subject:   THE LIST OF CORRECTNESS STATEMENTS, as one pinned proposition.

  Every pinned statement of `Core/Ziel/Korrektheit` is a conjunct here, with its parameters universally quantified.
  The hash pin of `KorrektheitAussagen` covers the dependency closure of all of them, so a statement cannot change
  unnoticed, and one pin root keeps the cost of the pin check constant (each root walks the closure of the whole
  model). The list may only grow; removing or weakening a conjunct is a change of the correctness package.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Frontend
public import Core.Ziel.Korrektheit.Speicher

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

def KorrektheitAussagen : Prop :=
  ∀ (P : Katalog.Plattform) (B : FormBeleg) (C : Pruefer) (π : Parser),
    PrueferLokalKorrektAussage C ∧ PrueferLokalVollstaendigAussage C ∧
    PrueferKlauselnKorrektAussage C ∧ PrueferKlauselnVollstaendigAussage C ∧
    PrueferWaechterKorrektAussage C ∧ PrueferWaechterVollstaendigAussage C ∧
    PrueferKorrektAussage C ∧ PrueferVollstaendigAussage C ∧ PrueferNichtTrivialAussage C ∧
    PrueferDecktFormenAussage C B ∧ PrueferRestUnentscheidbarAussage ∧
    ParseDruckAussage ∧ ParseEindeutigAussage ∧ ElabKorrektAussage P ∧ BezeichnetFunktionalAussage P ∧
    TextWohlgeformtAussage P ∧ RealisiertAlleFormenAussage ∧ ParserKorrektAussage π ∧
    GraphmaschineAequivalentAussage ∧ KohaerenzKatalogAussage ∧ RmwNichtDoppeltAussage ∧
    IriwScVerbotenAussage ∧ IriwRaErlaubtAussage ∧
    ProtokollSchrittErhaeltAussage ∧ ProtokollStartGutAussage ∧ ProtokollGutImLaufAussage ∧
    IdealProtokollGutImLaufAussage ∧ ImplBestimmtAussage ∧ IdealAkzeptierteEinheitAussage ∧
    VerfeinerungAkzeptiertAussage ∧ ZielFXAkzeptiertAussage ∧ FortschrittAkzeptiertAussage ∧
    RegelSimDiskriminiertAussage ∧ SimTrenntAussage ∧ SimRefutierbarAussage ∧
    BildGueltigAussage P ∧ FormenGedecktAussage P B ∧ SchrankenAkzeptiertAussage P ∧ NIAkzeptiertAussage P ∧
    ZielAusTeilenAussage P B ∧ SicherheitAkzeptiertAussage P ∧ SicherheitNichtLeerInstanzAussage P B ∧
    SicherheitAusTeilenAussage P B ∧ ZielInhaltAussage P ∧ LinkerAkzeptiertAussage ∧
    LinkerNichtTrivialAussage

end Gabbro.Core.Ziel.Korrektheit
