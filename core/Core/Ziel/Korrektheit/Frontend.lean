/-
  File:      core/Core/Ziel/Korrektheit/Frontend.lean
  Subject:   FRONT-END CORRECTNESS (PERFECT-MODEL §2.1 "Text", §3.1): printing and parsing, elaboration, the
             denotation of raw text, and the deployed parser, as pinned propositions.

  The front end is correct when (1) printing and parsing round-trip, (2) parsing is unambiguous, (3) elaboration
  is a function that realises the meaning of every form, (4) the denotation of raw text is functional and its
  domain is exactly the independently defined well-formed text, and (5) a deployed parser agrees with the
  reference parse relation. The first four are generic theorems of `Core/Ast` and `Core/Text` that are collected
  here under one name each; the fifth is a statement about a parser that does not exist yet (Stage 0 rebuilds it).

  The theorems below are compositions of existing lemmas (`parse_print`, `print_parse`, `parse_deterministic`,
  `elab_korrekt`, `elab_vollstaendig`, `bezeichnet_deterministisch`, `Quellform.realisiert`) and unfold
  definitions; nothing here is new mathematics.
-/
module

public import Core.Ast.Semantik.Quellform
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- PRINTING AND PARSING ROUND-TRIP, in both directions, for every category: parsing what was printed gives the
tree back, and whatever parses prints to a text canonically equivalent to the source (trivia and canonical
spelling aside). Feeds: `Ast.parse_print`, `Ast.print_parse`, the per-form `printReads` lemmas. -/
def ParseDruckAussage : Prop :=
    (∀ (c : Ast.Category) (t : c.Tree), Ast.Parse (category := c) (Ast.print t) t)
  ∧ (∀ (c : Ast.Category) (text : Text.RawText) (t : c.Tree), Ast.Parse text t →
      Ast.Canonicalisation c text (Ast.print t))

theorem parse_druck : ParseDruckAussage :=
  ⟨fun _ t => Ast.parse_print t, fun _ _ _ parsed => Ast.print_parse parsed⟩

/-- THE PARSER IS UNAMBIGUOUS: a text has at most one tree. Feeds: `Ast.parse_deterministic`. -/
def ParseEindeutigAussage : Prop :=
  ∀ (c : Ast.Category) (text : Text.RawText) (a b : c.Tree),
    Ast.Parse text a → Ast.Parse text b → a = b

theorem parse_eindeutig : ParseEindeutigAussage :=
  fun _ _ _ _ left right => Ast.parse_deterministic left right

/-- ELABORATION IS A FUNCTION AND IS SOUND AND COMPLETE AGAINST ITS RELATION (`elab_korrekt`,
`elab_vollstaendig`): a tree means exactly the unit `elaborieren` computes on the selected platform. -/
def ElabKorrektAussage (P : Katalog.Plattform) : Prop :=
  ∀ (c : Ast.Category) (t : c.Tree) (E : Ast.Semantik.Einheit),
    Ast.Semantik.Elaboriert P t E ↔ E = Ast.Semantik.elaborieren P t

theorem elab_korrekt_vollstaendig (P : Katalog.Plattform) : ElabKorrektAussage P :=
  fun _ _ _ => Iff.rfl

/-- THE DENOTATION OF RAW TEXT IS FUNCTIONAL: a text denotes at most one unit (`bezeichnet_deterministisch`).
This is the second conjunct of `NichtLeer`. -/
def BezeichnetFunktionalAussage (P : Katalog.Plattform) : Prop :=
  ∀ (c : Ast.Category) (a : Text.RawText) (E E' : Ast.Semantik.Einheit),
    Ast.Semantik.Bezeichnet P c a E → Ast.Semantik.Bezeichnet P c a E' → E = E'

theorem bezeichnet_funktional (P : Katalog.Plattform) : BezeichnetFunktionalAussage P :=
  fun _ _ _ _ left right => Ast.Semantik.bezeichnet_deterministisch left right

/-- THE DOMAIN OF THE DENOTATION IS THE INDEPENDENTLY DEFINED WELL-FORMED TEXT: text is well formed (grammar and
platform admission, defined from the token grammar alone, without `Bezeichnet`) exactly when it denotes a unit.
This is the first conjunct of `NichtLeer`, for source units. -/
def TextWohlgeformtAussage (P : Katalog.Plattform) : Prop :=
  ∀ a : Text.RawText,
    Text.WohlgeformterText (Text.tokenGrammar (Ast.Category.reads Ast.Category.unit))
      (fun t => Ast.Semantik.zugelassen P Ast.Category.unit t) a ↔
    ∃ E, Ast.Semantik.Bezeichnet P Ast.Category.unit a E

theorem text_wohlgeformt (P : Katalog.Plattform) : TextWohlgeformtAussage P := by
  intro a
  constructor
  · rintro ⟨tree, pieces, root, lexed, derives, typing⟩
    exact ⟨Ast.Semantik.elaborieren P tree, tree, ⟨root, pieces, lexed, derives⟩, rfl, typing⟩
  · rintro ⟨E, tree, ⟨root, pieces, lexed, derives⟩, _, typing⟩
    exact ⟨tree, pieces, root, lexed, derives, typing⟩

/-- ELABORATION REALISES THE MEANING OF EVERY FORM: for every source form whose instruction sits at its
declared position in the elaborated code, a context that reaches that position runs the instruction in both
machines (`Quellform.realisiert`). This is the generic half of `Rahmen.realisiert`; the registry supplies the
form list (`FormBeleg`, `Instanz.lean`). -/
def RealisiertAlleFormenAussage : Prop :=
  ∀ (category : Ast.Category) (Arguments : Type) (form : Ast.Semantik.Quellform category Arguments),
    form.RegelAmOrt → form.RealisiertAussage

theorem realisiert_alle_formen : RealisiertAlleFormenAussage := by
  intro category Arguments form position platform args s running active live atPc
  exact form.realisiert position platform args s running active live atPc

/-- A parser as a total function from raw text to at most one source unit. The deployed parser (Stage 0 and
later the compiler) is such a function; `ParserKorrektAussage` ties it to the reference relation. -/
structure Parser where
  parse : Text.RawText → Option Ast.Unit

/-- THE DEPLOYED PARSER AGREES WITH THE REFERENCE PARSE RELATION, in both directions: it returns a tree exactly
when the reference relation derives it from every semantic token of the text (`print 1; print 2` is never read as
`print 1`), and it returns nothing for text the relation does not derive. Feeds: `Text.Parse.accounts`,
`Ast.parse_deterministic` (so `none` is the complement). Open: Stage 0's parser (Designer: interface;
Prover: the proof against the pinned relation, after the parser exists). -/
def ParserKorrektAussage (π : Parser) : Prop :=
  ∀ (a : Text.RawText) (t : Ast.Unit), π.parse a = some t ↔ Ast.Parse (category := Ast.Category.unit) a t

end Gabbro.Core.Ziel.Korrektheit
