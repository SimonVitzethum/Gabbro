module

public import Core.Ast.Aggregate.TupleValueProofs
public import Core.Ast.Aggregate.TupleFieldProofs
public import Core.Ast.Aggregate.TupleBindProofs
public import Core.Ast.Aggregate.Types.TupleProofs
public import Core.Ast.Semantik.Kernregister

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

private theorem tupleBindDirectCallWiderspruch {scope : Scope} {input : List Token}
    {tokens : List Token} {call : DirectCall scope} {rest : List Token}
    (read : CallReads scope tokens call (semicolon :: rest))
    (eq : letKeyword :: openParen :: input = tokens) : False := by
  subst tokens
  obtain ⟨args, same, _⟩ := CallReads.inversion read
  have headEq : letKeyword = .word call.name.val := (List.cons.inj same).1
  have nameEq : call.name.val = "let".toList := by
    simpa [letKeyword] using headEq.symm
  have inList : call.name.val ∈ ["let", "if", "return", "while", "for", "leave", "next", "match", "forever"].map String.toList := by
    rw [nameEq]
    exact List.mem_map.2 ⟨"let", List.mem_cons_self, rfl⟩
  exact (call.ordinary.2 inList).elim

private theorem tupleBindOptionLetWiderspruch (mutable : Bool) (name : Identifier) {input tail : List Token}
    (same : letKeyword :: openParen :: input = optionLetHead mutable name ++ tail) : False := by
  cases mutable <;> cases (List.cons.inj (List.cons.inj same).2).1

private theorem tupleBindInversionWitness : TupleBindInversionAussage := by
  intro scope result input tree rest read
  generalize htok : letKeyword :: openParen :: input = tokens at read
  cases read
  case tupleBind =>
      have patternRead : TuplePatternReads _ _ _ := ‹_›
      have annotationRead : TupleAnnotationReads scope _ _ _ := ‹_›
      have valueRead : ExprReads scope 0 _ _ (semicolon :: rest) := ‹_›
      rw [← (List.cons.inj htok).2] at patternRead
      refine ⟨⟨_,_,_,_,_,‹_›,_⟩, _, _, patternRead, annotationRead, valueRead, rfl⟩
  case directCall callRead =>
      exact (tupleBindDirectCallWiderspruch callRead htok).elim
  case letOption =>
      exact (tupleBindOptionLetWiderspruch _ _ htok).elim
  all_goals
    exfalso
    simpa [letKeyword, returnKeyword, ifKeyword, openParen, closeParen, semicolon,
      assignment, colon, comma, dot, keyword] using htok

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Waechter

private theorem tupleValuePacket : TupleValueProofPacket :=
  ⟨Surface.tupleValue_inversion, Surface.tupleValue_suffix, Surface.tupleValue_derivation,
    tupleValue_parse, tupleValue_elaboriert, tupleValue_realisiert, tupleValue_annahme,
    tupleValue_ideal, tupleValue_einheit, tupleValue_impl, tupleValue_erhaltung,
    tupleValue_regelSicher, tupleValue_erfuellbar⟩

private theorem tupleFieldPacket : TupleFieldProofPacket :=
  ⟨Surface.TupleFieldInversion, Surface.TupleFieldSuffix, Surface.TupleFieldDerivation,
    TupleFieldParse, TupleFieldElaboriert, TupleFieldRealisiert, TupleFieldAnnahme,
    TupleFieldIdeal, TupleFieldEinheit, TupleFieldImpl, TupleFieldErhaltung,
    TupleFieldRegelSicher, TupleFieldErfuellbarAm⟩

private theorem tupleBindPacket : TupleBindProofPacket :=
  ⟨Surface.tupleBindInversionWitness, Surface.tupleBind_suffix, Surface.tupleBind_derivation,
    tupleBind_parse, tupleBind_elaboriert, tupleBind_realisiert, tupleBind_annahme,
    tupleBind_ideal, tupleBind_einheit, tupleBind_impl, tupleBind_erhaltung,
    tupleBind_regelSicher, tupleBind_erfuellbar, tupleBind_locals⟩

private theorem tupleTypePacket : TupleTypeProofPacket :=
  ⟨Gabbro.Core.Ast.tupleType_inversion, Gabbro.Core.Ast.tupleType_suffix,
    Gabbro.Core.Ast.tupleType_derivation, Gabbro.Core.Ast.tupleType_index,
    Gabbro.Core.Ast.tupleType_syntax_erfuellbar, tupleType_parse, tupleType_elaboriert,
    tupleType_realisiert, tupleType_annahme, tupleType_ideal, tupleType_einheit,
    tupleType_impl, tupleType_erhaltung, tupleType_regelSicher, tupleType_erfuellbar⟩

public def tupleValueEntry :
    RegistryPacketEntry ``Expr.tupleValue (exprSchema ``Expr.tupleValue) TupleValueProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface tupleValue_parse tupleValue_elaboriert tupleValue_realisiert, tupleValue_annahme,
      tupleValue_ideal, tupleValue_einheit, tupleValue_impl, tupleValue_erhaltung, tupleValue_erfuellbar⟩
  packetProof := tupleValuePacket

public def tupleFieldEntry :
    RegistryPacketEntry ``Expr.tupleField (exprSchema ``Expr.tupleField) TupleFieldProofPacket where
  entry := by
    simp only [exprSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface TupleFieldParse TupleFieldElaboriert TupleFieldRealisiert, TupleFieldAnnahme,
      TupleFieldIdeal, TupleFieldEinheit, TupleFieldImpl, TupleFieldErhaltung, TupleFieldErfuellbarAm⟩
  packetProof := tupleFieldPacket

public def tupleBindEntry :
    RegistryPacketEntry ``Stmt.tupleBind (stmtSchema ``Stmt.tupleBind) TupleBindProofPacket where
  entry := by
    simp only [stmtSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.surface tupleBind_parse tupleBind_elaboriert tupleBind_realisiert, tupleBind_annahme,
      tupleBind_ideal, tupleBind_einheit, tupleBind_impl, tupleBind_erhaltung, tupleBind_erfuellbar⟩
  packetProof := tupleBindPacket

public def buildTupleEntry :
    RegistryPacketEntry ``Befehl.baueTupel (befehlSchema ``Befehl.baueTupel) TupleValueProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (tupleValue_ideal scope).1⟩, tupleValue_annahme,
      tupleValue_ideal, tupleValue_einheit, tupleValue_impl, tupleValue_erhaltung, tupleValue_erfuellbar⟩
  packetProof := tupleValuePacket

public def liesTupleFieldEntry :
    RegistryPacketEntry ``Befehl.liesTupelfeld (befehlSchema ``Befehl.liesTupelfeld) TupleFieldProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun scope => (TupleFieldIdeal scope).1⟩, TupleFieldAnnahme,
      TupleFieldIdeal, TupleFieldEinheit, TupleFieldImpl, TupleFieldErhaltung, TupleFieldErfuellbarAm⟩
  packetProof := tupleFieldPacket

public def bindeTupleEntry :
    RegistryPacketEntry ``Befehl.bindeTupel (befehlSchema ``Befehl.bindeTupel) TupleBindProofPacket where
  entry := by
    simp only [befehlSchema, Lean.Name.str.injEq, String.reduceEq, and_false, ite_true, ite_false]
    exact ⟨.core ⟨aus_elaborierung, fun ctx => (tupleBind_ideal ctx).1⟩, tupleBind_annahme,
      tupleBind_ideal, tupleBind_einheit, tupleBind_impl, tupleBind_erhaltung, tupleBind_erfuellbar⟩
  packetProof := tupleBindPacket

public theorem tupleTypeEntry : RegistryPacketProof ``WrittenType.tuple TupleTypeProofPacket :=
  ⟨tupleTypePacket⟩

end Gabbro.Core.Ast.Semantik
