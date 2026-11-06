module
public import Grammatik.Parser.Elab.Modules.Witness.Data
import all Grammatik.Parser.Elab.Modules.Witness.Scanning
import all Grammatik.Parser.Elab.Modules.Expansion
import all Grammatik.Parser.Elab.Modules.Shape
import all Grammatik.Parser.Elab.Modules.Substitution
import all Grammatik.Parser.Elab.Generic.Arguments
import all Grammatik.Parser.Elab.Generic.Substitution
import all Grammatik.Parser.Elab.Generic.Rewrite
import all Grammatik.Parser.Elab.Generic.Body
import all Grammatik.Parser.Elab.Generic.Expansion
import all Grammatik.Parser.Elab.Generic.Bounds
import all Grammatik.Parser.Elab.Generic.Literals
import all Grammatik.Parser.Namen.Aufloesung.Teil1a
import all Grammatik.Parser.Namen.Aufloesung.Teil1
import all Grammatik.Parser.Namen.Aufloesung.Teil2
import all Grammatik.Parser.Item.ElementTief.Defs1
import all Grammatik.Parser.Item.ElementTief.Defs2
import all Grammatik.Parser.Item.ElementTief.Defs6a
import all Grammatik.Parser.Item.ElementTief.Defs7
import all Grammatik.Parser.Item.ElementTief.GenericParams
import all Grammatik.Parser.Item.ElementTief.Kopf.Teil1a
import all Grammatik.Parser.Item.ElementTief.Kopf.Teil2
import all Grammatik.Parser.Stmt.Anweisung.Defs1
import all Grammatik.Parser.Stmt.Anweisung.Defs2a
import all Grammatik.Parser.Expr.Ausdruck.Teil1
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Ausdruck.Teil3
import all Grammatik.Parser.Expr.Typ
import all Grammatik.Parser.Print.Item.Teil1
import all Grammatik.Parser.Print.Item.Teil2
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Folds.ConstEvaluation
import Init.Data.String.Lemmas.Intercalate
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

namespace Gabbro.Grammatik.Parser.Modules.WitnessPhases
open Gabbro.Grammatik.Parser.UebersetzeProben11.Phases (Input)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Select canonical recursion equations at actual nodes, retaining the original fuels.
attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe parseModulTief parseItemsTief parseItemTief parseItemKopfTief
  visitItem visitList locateItem locateList templatesItem templatesList ordinaryItem ordinaryList
  occupiedItem occupiedList syntaxItem syntaxList Generic.rewriteExpression
  Generic.rewriteQuantifierOperands Generic.rewriteType Generic.rewriteBody Generic.rewriteStatements
  Uebersetze.uFloatLimit
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def parseModulTief.eq_def
  parseItemsTief.eq_def parseItemTief.eq_def parseItemKopfTief.eq_def visitItem.eq_def visitList.eq_def
  locateItem.eq_def locateList.eq_def templatesItem.eq_def templatesList.eq_def
  ordinaryItem.eq_def ordinaryList.eq_def occupiedItem.eq_def occupiedList.eq_def
  syntaxItem.eq_def syntaxList.eq_def Generic.rewriteExpression.eq_def
  Generic.rewriteQuantifierOperands.eq_def Generic.rewriteType.eq_def Generic.rewriteBody.eq_def
  Generic.rewriteStatements.eq_def Generic.sourceSize_eq String.intercalate_singleton

-- This composition is generic in the entire input, so no concrete String decoder
-- or parsed-source getter appears in a later instantiation certificate.
private theorem parsed_from_input {source : String} (input : Input source)
    (result : { actual : List SItemTief // parseTopTief input.tokens = .ok actual }) :
    parsedSource source = .ok result.val := by
  have lexed : lex source = .ok input.tokens :=
    (congrArg lex input.text).trans ((lex_ofList input.characters).trans input.lexed)
  unfold parsedSource Generic.tokens
  rw [lexed]
  simpa only [bind, Except.bind] using result.property

private def templateParsed : { actual : List SItemTief //
    parsedSource stackTemplateSource = .ok actual } := by
  let parsed : { actual : List SItemTief // parseTopTief templateInput.tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact ⟨parsed.val, parsed_from_input templateInput parsed⟩
private def useParsed : { actual : List SItemTief //
    parsedSource "pub use Jobs = stack::[index into Tasks, 64];" = .ok actual } := by
  let parsed : { actual : List SItemTief // parseTopTief publicUseInput.tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact ⟨parsed.val, parsed_from_input publicUseInput parsed⟩
private def stackParsed : { actual : List SItemTief // parsedSource stackSource = .ok actual } := by
  let parsed : { actual : List SItemTief // parseTopTief stackInput.tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact ⟨parsed.val, parsed_from_input stackInput parsed⟩
private def twoParsed : { actual : List SItemTief // parsedSource twoUsesSource = .ok actual } := by
  let parsed : { actual : List SItemTief // parseTopTief twoUsesInput.tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact ⟨parsed.val, parsed_from_input twoUsesInput parsed⟩
private def recursiveParsed : { actual : List SItemTief //
    parsedSource ("module loop[T] { use Again = loop::[T]; } " ++
      "use Start = loop::[u8];") = .ok actual } := by
  let parsed : { actual : List SItemTief // parseTopTief recursiveInput.tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact ⟨parsed.val, parsed_from_input recursiveInput parsed⟩
private def collisionParsed : { actual : List SItemTief //
    parsedSource "module empty[T] { } use A = empty::[u8]; use A = empty::[u8];" =
      .ok actual } := by
  let parsed : { actual : List SItemTief // parseTopTief collisionInput.tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact ⟨parsed.val, parsed_from_input collisionInput parsed⟩
private def badParsed : { actual : List SItemTief //
    parsedSource (stackPreamble ++ stackTemplateSource ++
      "use Bad = stack::[index into Tasks, 0];") = .ok actual } := by
  let parsed : { actual : List SItemTief // parseTopTief badInput.tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
  exact ⟨parsed.val, parsed_from_input badInput parsed⟩

private def printedUse : { actual : List Token //
    druckItem (.moduleUseT "Jobs" ["containers", "stack"] ["index into Tasks", "64"]) =
      actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def printedUseParsed : { actual : List SItemTief //
    parseTopTief (printedUse.val ++ [.ende]) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private theorem roundtrip_use :
    rundlaufItem (.moduleUseT "Jobs" ["containers", "stack"] ["index into Tasks", "64"]) = true := by
  simp only [rundlaufItem, printedUse.property, printedUseParsed.property]
  cbv

-- This is a proposition abbreviating the exact call and initial state already
-- present in expandRaw. It neither computes an alternative expansion nor supplies output data.
private abbrev VisitResult (items : List SItemTief)
    (answer : Except String (Unit × Work)) : Prop :=
  let root : Located := { origin := [], destination := [], item := .useT [] }
  (visitList (templatesList [] items) (Aufloesung.quelle (ordinaryList items)) [] root
    (Generic.sourceSize items + 1) items).run
      { locations := locateList root items, occupied := occupiedList [] items,
        remaining := Generic.sourceSize items + 1 } = answer

private def stackVisits : { actual : Unit × Work // VisitResult stackParsed.val (.ok actual) } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def stackEnvironment : { actual : Generic.Environment //
    argumentEnvironment (Aufloesung.quelle (ordinaryList stackParsed.val)) stackVisits.val.2 =
      .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def stackResolved : { actual : List SItemTief //
    stackVisits.val.2.locations.mapM (resolve stackEnvironment.val
      (Aufloesung.quelle (ordinaryList stackParsed.val)) stackVisits.val.2.locations) =
        .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def stackRaw : { actual : Expansion // expandRaw stackParsed.val = .ok actual } := by
  refine ⟨?_, ?origin⟩
  case origin =>
    unfold expandRaw
    simp only [stackVisits.property, stackEnvironment.property, stackResolved.property,
      bind, Except.bind, pure, Except.pure]
    cbv <;> exact Eq.refl _

private def twoVisits : { actual : Unit × Work // VisitResult twoParsed.val (.ok actual) } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def twoEnvironment : { actual : Generic.Environment //
    argumentEnvironment (Aufloesung.quelle (ordinaryList twoParsed.val)) twoVisits.val.2 =
      .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def twoResolved : { actual : List SItemTief //
    twoVisits.val.2.locations.mapM (resolve twoEnvironment.val
      (Aufloesung.quelle (ordinaryList twoParsed.val)) twoVisits.val.2.locations) =
        .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def twoRaw : { actual : Expansion // expandRaw twoParsed.val = .ok actual } := by
  refine ⟨?_, ?origin⟩
  case origin =>
    unfold expandRaw
    simp only [twoVisits.property, twoEnvironment.property, twoResolved.property,
      bind, Except.bind, pure, Except.pure]
    cbv <;> exact Eq.refl _

private def collisionItems : List SItemTief :=
  [.constT (memberName ["A", "v"]) (.atom "u8") (.one (.lit 0)),
    .moduleTemplateT "m" [.type "T" []]
      [.globT false "v" (.atom "T") (.one (.lit 0)) none none false],
    .moduleUseT "A" ["m"] ["u8"]]
private def nameVisits : { actual : Unit × Work // VisitResult collisionItems (.ok actual) } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def nameEnvironment : { actual : Generic.Environment //
    argumentEnvironment (Aufloesung.quelle (ordinaryList collisionItems)) nameVisits.val.2 =
      .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def nameResolved : { actual : List SItemTief //
    nameVisits.val.2.locations.mapM (resolve nameEnvironment.val
      (Aufloesung.quelle (ordinaryList collisionItems)) nameVisits.val.2.locations) =
        .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private theorem name_raw_refused : expandRaw collisionItems =
    .error "parametric-module-name-collision: generated name is already declared" := by
  unfold expandRaw
  simp only [nameVisits.property, nameEnvironment.property, nameResolved.property,
    bind, Except.bind, pure, Except.pure]
  cbv

private theorem recursive_visit_refused : VisitResult recursiveParsed.val
    (.error "parametric-module-recursion: loop") := by cbv
private theorem alias_visit_refused : VisitResult collisionParsed.val
    (.error "parametric-module-alias-collision: A") := by cbv
private theorem bad_visit_refused : VisitResult badParsed.val
    (.error "generic constant argument: C17 evaluation failed or exceeded its bound") := by cbv

private theorem recursive_raw_refused : expandRaw recursiveParsed.val =
    .error "parametric-module-recursion: loop" := by
  unfold expandRaw
  simp only [recursive_visit_refused, bind, Except.bind]
  cbv
private theorem alias_raw_refused : expandRaw collisionParsed.val =
    .error "parametric-module-alias-collision: A" := by
  unfold expandRaw
  simp only [alias_visit_refused, bind, Except.bind]
  cbv
private theorem bad_raw_refused : expandRaw badParsed.val =
    .error "generic constant argument: C17 evaluation failed or exceeded its bound" := by
  unfold expandRaw
  simp only [bad_visit_refused, bind, Except.bind]
  cbv

-- Retain the real final ordinary-output gate of expand (not prepare).
private theorem expanded_of_raw {items : List SItemTief}
    (packet : { actual : Expansion // expandRaw items = .ok actual })
    (checked : ordinary packet.val.items = true) : expand items = .ok packet.val.items := by
  simp only [expand, expandWithRequirements, packet.property, checked,
    ite_true, bind, Except.bind, pure, Except.pure, Except.map]

private theorem refused_of_raw {items : List SItemTief} {error : String}
    (refused : expandRaw items = .error error) : expand items = .error error := by
  simp only [expand, expandWithRequirements, refused, bind, Except.bind, Except.map]

private theorem stackExpanded : expandedSource stackSource = .ok stackRaw.val.items := by
  simp only [expandedSource, stackParsed.property, bind, Except.bind]
  exact expanded_of_raw stackRaw (by cbv)
private theorem twoExpanded : expandedSource twoUsesSource = .ok twoRaw.val.items := by
  simp only [expandedSource, twoParsed.property, bind, Except.bind]
  exact expanded_of_raw twoRaw (by cbv)
private theorem recursiveRefused :
    expandedSource ("module loop[T] { use Again = loop::[T]; } " ++
      "use Start = loop::[u8];") = .error "parametric-module-recursion: loop" := by
  simp only [expandedSource, recursiveParsed.property, bind, Except.bind]
  exact refused_of_raw recursive_raw_refused
private theorem aliasRefused :
    expandedSource "module empty[T] { } use A = empty::[u8]; use A = empty::[u8];" =
      .error "parametric-module-alias-collision: A" := by
  simp only [expandedSource, collisionParsed.property, bind, Except.bind]
  exact refused_of_raw alias_raw_refused
private theorem badRefused :
    expandedSource (stackPreamble ++ stackTemplateSource ++
      "use Bad = stack::[index into Tasks, 0];") =
        .error "generic constant argument: C17 evaluation failed or exceeded its bound" := by
  simp only [expandedSource, badParsed.property, bind, Except.bind]
  exact refused_of_raw bad_raw_refused
private theorem nameRefused : expand collisionItems =
    .error "parametric-module-name-collision: generated name is already declared" :=
  refused_of_raw name_raw_refused

end Gabbro.Grammatik.Parser.Modules.WitnessPhases
