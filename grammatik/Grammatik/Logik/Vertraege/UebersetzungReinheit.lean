/-
  File:      Grammatik/Logik/Vertraege/UebersetzungReinheit.lean
  Subject:   C02 item 6: pure execution, termination and effect/cost obligations.

  A certified translator's obligations, packaged as theorems over
  `TranslationDecl`/`TranslationCertificate` (`Uebersetzung.lean`): the
  execution answers with the declared translator's map and the unchanged
  world for every oracle, pass count and loop budget (no hidden runtime
  input, no carrier, foreign, atomic or lock effect behind the payload);
  the typed call graph is empty and bounded, so the source-derived measure
  duty holds with no trusted termination flag and no new hardware premise.
  The declared source effects must be pure (`effekteRein`); compilation
  work is compile-time (translators never reach the expanded unit -- see
  `Parser/Stmt/LibraryErweiterung.lean`), never charged to the runtime
  program's `ZeitAb`. No new language case is claimed complete by this
  module: product schemas need C01, general maps need C17.
-/

module

public import Grammatik.Logik.Vertraege.Uebersetzung

@[expose] public section

namespace Gabbro.Grammatik.Uebersetzung

open Gabbro.Grammatik.Parser

/-- The declared source effects of a stage-1 translator: every `effects`
    arm is `pure`. Reads, writes, locks, masks, allocations, takes, posts
    and loops all refuse; a translator body needing them has no certificate
    path (`TranslationDecl.noCalls`, or the `torZurErweiterung` gate). -/
def effekteRein (ks : List SKlausel) : Bool :=
  ks.all fun | .effs es => es.all fun | .pure => true | _ => false | _ => true

/-- The empty clause list is pure. -/
theorem effekteRein_leer : effekteRein [] = true := rfl

/-- A single `effects { pure }` clause is pure. -/
theorem effekteRein_rein : effekteRein [.effs [.pure]] = true := rfl

/-- A `writes` arm refuses: payload initialization is immutable, never a
    declared write. -/
theorem effekteRein_schreibt_verweigert :
    effekteRein [.effs [.writes (.variable "t")]] = false := rfl

/-- A `locks` arm refuses: translators take no lock. -/
theorem effekteRein_sperrt_verweigert :
    effekteRein [.effs [.locks false (.variable "M")]] = false := rfl

/-- The stronger C02 promise as a theorem: the certified execution answers
    exactly the declared translator's map on the decoded input, in the
    unchanged world. Equality of output types alone would admit a
    well-typed wrong result; this is the exact execution relation. -/
theorem translation_antwort_gleich_ausfuehrung {source : LibrarySource} {u : UProg}
    {decl : TranslationDecl source u} (certificate : TranslationCertificate decl)
    (oracle : Orakel (declOf u)) (passes : Nat) (world : World (declOf u)) :
    rufAt decl.program oracle passes certificate.fuel decl.translator world
      (decl.arguments certificate.input) =
      .ok world (decl.answer certificate.output) :=
  certificate.execution oracle passes world

/-- Termination obligation: the certified translator has no `forever`
    pass. -/
theorem translation_ohne_ewig {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) :
    (befund decl.program decl.translator).ewig = false :=
  decl.bounded

/-- Effect obligation, direct calls: the certified translator calls
    nothing. -/
theorem translation_ohne_rufe {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) :
    (befund decl.program decl.translator).rufe = [] :=
  decl.noCalls

/-- Effect obligation, indirect calls: the certified translator has no
    indirect call signatures either. -/
theorem translation_ohne_sigs {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) :
    (befund decl.program decl.translator).sigs = [] :=
  decl.noIndirectCalls

end Gabbro.Grammatik.Uebersetzung
