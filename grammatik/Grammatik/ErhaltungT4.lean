/-
  File:       Grammatik/ErhaltungT4.lean
  Subject:    Bridge lemmas from the T4 per-form correspondence lemmas
              (`CFormen.lean`, `CFormenI.lean`, `CFormenM.lean`,
              `CFormenH.lean`) to the ruling-table obligations of
              `Erhaltung.lean`.

  Claim (in one sentence):
    For every census slot of `Erhaltung.lean` (`OffeneForm`, 31 slots)
    whose admitted C shape has a T4 correspondence lemma, the bridge
    conjoins that lemma's correspondence with the slot's decided table
    row; slots without C semantics stay listed as uncovered with the
    reason, in the header table below.

  Measurement (all 31 slots, lemma names grep-verified 2026-09-13):
    COVERED (bridge below): logUndOder (`ecorr_und`, `ecorr_oder`),
      bitNicht (`ecorr_bnot`), boolLit (`ecorr_wahr`, `ecorr_falsch`),
      boolTyp (`truth_b2i`, `ecorr_wahr`), deref (`ev_ld`),
      cSizeof (`ev_sizeofQuot`), cConst (`constTab_read`,
      `ro_store_stuck`), adressVon (`ptrTo_named`), voidTyp
      (`retCorr_none`), bedingt (`scorr_ite`, adapter: the generator
      replaces `?:` by `if`), zeigerIndex (`ecorr_byteGuard`),
      pfeilZugriff (`ecorr_slotNamed`), zusammZuweisung
      (`scorr_plusGleich`), schrittStmt (`scorr_plusGleich`, adapter:
      the generator normalises `++` to `+= 1`), syscallStub
      (`scorr_axiomCall`, adapter: the stub is the `.ext` call whose
      assumption shape is `AxCorr`), cEnum (`ecorr_lit`, adapter:
      enum constants elaborate to integer literals).
    UNCOVERED (no C semantics, hence no lemma to bridge from):
      zeigerArithmetik (the price is a refusal; evaluation lemmas cover
      only the in-bounds shape), cInclude, cTypedef, cDefine, cAttribut,
      cInline, typOfErw, wennGnuC, statikAssert (preamble, aliases,
      macros, attributes, compile-time-only, no evaluation),
      doubleTyp, floatTyp (no floats in the C semantics: `CIT`/`CVal`
      are integer-only), schleifeStmt (`retry` is explicitly not
      covered, `CFormenI.lean:2170`), abbruchStmt, fortStmt (no
      `StmtCorr` lemma produces bare `.brk`/`.cont`; `scorr_leave`
      lowers to `.goto`, break/continue live only inside generated
      skeletons), unerreichbarBuiltin (no `Exec` rule, no lemma).
-/
import Grammatik.Erhaltung
import Grammatik.CFormenH

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The `logUndOder` row stands decided in the table (data, by `decide`). -/
theorem logUndOder_steht :
    EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid) :=
  ⟨by decide, by decide⟩

variable {X : TVCtx D} {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- Bridge (`logUndOder`, `&&`): short-circuit conjunction corresponds,
    and its ruling row stands decided. -/
theorem bridge_logUndOder_und {ca cb : CX} {a b : Expr D Γ Λ .bool}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) :
    ExprCorr X K (.land ca cb) (.und a b) ∧
      EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid) :=
  ⟨ecorr_und X K ha hb, logUndOder_steht⟩

/-
CUTS:
* Bridges for the remaining covered slots (bitNicht, boolLit, boolTyp,
  deref, cSizeof, cConst, adressVon, voidTyp, bedingt, zeigerIndex,
  pfeilZugriff, zusammZuweisung, schrittStmt, syscallStub, cEnum).
* No adapter from simulation to refusal: uncovered slots name an
  emitter/checker refusal or an unerased-trust item, which no
  evaluation lemma can prove.
-/

#print axioms Gabbro.Grammatik.logUndOder_steht
#print axioms Gabbro.Grammatik.bridge_logUndOder_und

end Gabbro.Grammatik
