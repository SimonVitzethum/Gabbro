/-
  File:      Grammatik/Logik/Vertraege/UebersetzungDecoder.lean
  Subject:   C02 items 3-4: sound input decoders and payload typing.

  The typed input schema (`IntegerSchema`) and its finite token decoder
  (`integerRows`, `decodeIntegerRows`) from `Uebersetzung.lean`. This module
  records what makes the decoder sound rather than a Rust-only convention:
  every decoded value satisfies its schema range by construction, every
  integer schema carries an immutable payload typing, and the certified
  expansion keeps the ordinary arguments once in source order with the
  per-site payload last. Non-numeric token kinds refuse; negative rows
  decode through the explicit minus branch. General translator maps need
  C17, product schemas need C01: both stay refused by name
  (`torZurErweiterung` in `Parser/Stmt/LibrarySource.lean`).
-/

module

public import Grammatik.Logik.Vertraege.Uebersetzung

namespace Gabbro.Grammatik.Uebersetzung

open Gabbro.Grammatik.Parser

/-- Every integer-row schema carries an immutable payload typing: the schema
    type is a by-value array of ranged integers, never a capability to an
    unrelated mutable runtime table. -/
theorem IntegerSchema_traegt (schema : IntegerSchema) : ImmutablePayload schema.ty := by
  unfold IntegerSchema.ty
  exact .arr _ _ (.int _ _)

/-- Decoder soundness: every decoded value satisfies its schema range at every
    row. The range proofs travel with the decoded rows (`Zahl`), so a
    well-typed wrong output can never reuse a certificate
    (`translation_result_unique` in `Uebersetzung.lean`). -/
theorem decodeIntegerRows_bereich {D : Deklaration} {schema : IntegerSchema}
    {tokens : List Token} {v : Wert D schema.ty}
    (h : decodeIntegerRows D schema tokens = some v) (i : Fin schema.count) :
    schema.lo ≤ (v i).n ∧ (v i).n ≤ schema.hi :=
  ⟨(v i).lo_le, (v i).le_hi⟩

/-- The certified expansion keeps the call shape: ordinary function key, the
    ordinary arguments once in source order, the per-site payload last. The
    caller omits exactly the final payload parameter (`libraryDecl`). -/
theorem exportLibraryCall_stelligkeit (lib : ULibrary) (c : SLibraryCall) :
    ∃ args, exportLibraryCall lib c = .call lib.function.name args ∧
      args.length = c.args.length + 1 := by
  exact ⟨_, rfl, by simp [exportLibraryCall]⟩

/-- The `let`-bound expansion keeps the same shape: the ordinary call value
    bound as usual, payload last. -/
theorem exportLibraryBind_stelligkeit (bind : Bool) (x : String) (ty : Option STyp)
    (lib : ULibrary) (c : SLibraryCall) :
    ∃ args, exportLibraryBind bind x ty lib c =
      .bind bind x ty (.call lib.function.name args) ∧
      args.length = c.args.length + 1 := by
  exact ⟨_, rfl, by simp [exportLibraryBind]⟩

/-- A non-degenerate two-row region decodes: the decoder accepts the exact
    token grammar and the rows are the certified rows. -/
theorem decodeIntegerRows_zwei_zeuge {D : Deklaration} :
    ∃ v, decodeIntegerRows D ⟨0, 10, 2⟩ [.num 3, .num 5] = some v ∧
      (v ⟨0, by decide⟩).n = 3 ∧ (v ⟨1, by decide⟩).n = 5 := by
  refine ⟨_, rfl, rfl, rfl⟩

/-- Negative rows decode through the explicit minus branch, with the range
    proof attached to the negated value. -/
theorem decodeIntegerRows_negativ_zeuge {D : Deklaration} :
    ∃ v, decodeIntegerRows D ⟨-10, 10, 1⟩ [.zeichen "-", .num 3] = some v ∧
      (v ⟨0, by decide⟩).n = -3 := by
  refine ⟨_, rfl, rfl⟩

/-- Too many rows refuse: the schema count is exact, never a prefix. -/
theorem decodeIntegerRows_zuviele_zeuge {D : Deklaration} :
    decodeIntegerRows D ⟨0, 10, 2⟩ [.num 3, .num 5, .num 7] = none := rfl

/-- An empty region refuses a positive schema count. -/
theorem decodeIntegerRows_leer_zeuge {D : Deklaration} :
    decodeIntegerRows D ⟨0, 10, 2⟩ [] = none := rfl

/-- A negative row outside its schema range refuses. -/
theorem decodeIntegerRows_negativ_ausserhalb_zeuge {D : Deklaration} :
    decodeIntegerRows D ⟨0, 10, 1⟩ [.zeichen "-", .num 3] = none := rfl

/-- Closed token grammar: words, identifiers, texts, floats, documentation and
    the end marker are not integer rows. Only `.num`, and `-` directly before
    `.num`, decode. -/
theorem integerRows_verweigert_wort : integerRows 0 10 [.wort "return"] = none := rfl

theorem integerRows_verweigert_ident : integerRows 0 10 [.ident "region"] = none := rfl

theorem integerRows_verweigert_text : integerRows 0 10 [.text "3 5"] = none := rfl

theorem integerRows_verweigert_float : integerRows 0 10 [.float "3.0"] = none := rfl

theorem integerRows_verweigert_doku : integerRows 0 10 [.doku "rows"] = none := rfl

theorem integerRows_verweigert_ende : integerRows 0 10 [.ende] = none := rfl

theorem integerRows_verweigert_klammer_auf : integerRows 0 10 [.zeichen "{"] = none := rfl

theorem integerRows_verweigert_klammer_zu : integerRows 0 10 [.zeichen "}"] = none := rfl

theorem integerRows_verweigert_plus : integerRows 0 10 [.zeichen "+", .num 3] = none := rfl

theorem integerRows_verweigert_minus_ohne_zahl : integerRows 0 10 [.zeichen "-"] = none := rfl

theorem integerRows_verweigert_minus_vor_wort :
    integerRows 0 10 [.zeichen "-", .wort "x"] = none := rfl

end Gabbro.Grammatik.Uebersetzung
