/-
  File:      Grammatik/Uebersetzung.lean
  Subject:   C02 source-bound translation certificates. Output typing is one component;
             the certificate also proves the exact declared translator's result in the
             existing call semantics. No additional translator evaluator is introduced.

  The three definition lines below (`sumPayloadVals`, `sumPayloadOk`,
  `sumPayload_zert`) stand verbatim in the checker's printer
  (`crates/gabbro-check/src/uebersetzung.rs`, `payload_certificate`);
  `tests/uebersetzung.rs` holds the two against each other.
-/

module

public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Stmt.LibrarySource
public import Grammatik.Logik.Terminierung.Mass

@[expose] public section

namespace Gabbro.Grammatik.Uebersetzung

/-- Payload certificate predicate (encoding N of the certificate
    measurement): every entry of the payload table lies in the field
    range `lo .. hi`. The range proofs stay attached to the entries --
    the measurement's recommendation -- and `decide` walks them entry
    by entry, never as one definitional table comparison. -/
def nutzlastZert (t : List Nat) (lo hi : Nat) : Bool :=
  t.all fun v => decide (lo ≤ v ∧ v ≤ hi)

/-- Generic certificate lemma: a closed certificate yields every
    entry's range. Every premise is used: `h` supplies the closed
    `List.all`, `hm` locates the entry. -/
theorem nutzlastZert_mem {t : List Nat} {lo hi j v : Nat}
    (h : nutzlastZert t lo hi = true)
    (hm : t[j]? = some v) : lo ≤ v ∧ v ≤ hi := by
  unfold nutzlastZert at h
  rw [List.all_eq_true] at h
  have hmem : v ∈ t := List.mem_of_getElem? hm
  have hdec := h v hmem
  exact of_decide_eq_true hdec

/-- The example payload of `beispiele/106`: the region `{ 10 20 30 40 }`
    as a table of four integers. -/
def sumPayloadVals : List Nat := [10, 20, 30, 40]

/-- The payload's typing as a certificate over that table. -/
def sumPayloadOk : Bool := nutzlastZert sumPayloadVals 0 100

/-- The certificate closes by `decide`: every entry is in `0 .. 100`. -/
theorem sumPayload_zert : sumPayloadOk = true := by decide

/-- Joint witness for `nutzlastZert_mem`: the closed certificate, the
    entry lookup, and the concluded range, all at entry 3 (`40`). -/
theorem nutzlastZert_mem_zeuge :
    nutzlastZert sumPayloadVals 0 100 = true ∧
    sumPayloadVals[3]? = some 40 ∧ (0 ≤ 40 ∧ 40 ≤ 100) :=
  ⟨by decide, rfl, by decide, by decide⟩

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Types that can be copied into an immutable translation payload. Capabilities, references,
    function pointers and ownership-bearing values have no constructor here. Products require C01. -/
inductive ImmutablePayload : Ty → Prop
  | int (lo hi : Int) : ImmutablePayload (.int lo hi)
  | bool : ImmutablePayload .bool
  | arr (ty : Ty) (count : Nat) : ImmutablePayload ty → ImmutablePayload (.arr ty count)
  | str (count : Nat) : ImmutablePayload (.str count)

/-- The first closed input schema: a fixed number of integer rows, by value. In particular this
    is an array value, never a capability to an unrelated mutable runtime table. -/
structure IntegerSchema where
  lo : Int
  hi : Int
  count : Nat
  deriving DecidableEq, Repr

def IntegerSchema.ty (schema : IntegerSchema) : Ty := .arr (.int schema.lo schema.hi) schema.count

/-- A finite token decoder. It recognizes integer rows only; nested/custom token grammars refuse.
    The range proof is attached to each decoded value, including negative integers. -/
def integerRows (lo hi : Int) : List Token → Option (List (Zahl lo hi))
  | [] => some []
  | .num value :: rest => do
      if h : lo ≤ (value : Int) ∧ (value : Int) ≤ hi then
        let tail ← integerRows lo hi rest
        pure (⟨value, h.1, h.2⟩ :: tail)
      else none
  | .zeichen "-" :: .num value :: rest => do
      if h : lo ≤ -(value : Int) ∧ -(value : Int) ≤ hi then
        let tail ← integerRows lo hi rest
        pure (⟨-(value : Int), h.1, h.2⟩ :: tail)
      else none
  | _ => none

/-- Schema admission checks both the complete row count and every field's range. -/
def decodeIntegerRows (D : Deklaration) (schema : IntegerSchema) (tokens : List Token) :
    Option (Wert D schema.ty) := do
  let rows ← integerRows schema.lo schema.hi tokens
  if h : rows.length = schema.count then
    pure (fun index => rows.get ⟨index.val, by rw [h]; exact index.isLt⟩)
  else none

/-- An exact source occurrence, pinned to characters, parsed items and a statement-tree path.
    The full resolver is used even for a one-module unit: a wrong library qualifier must refuse. -/
structure LibrarySource where
  characters : List Char
  tokens : List Token
  items : List SItemTief
  lexed : lexL characters = .ok tokens
  parsed : parseTopTief tokens = .ok items
  callerIndex : Nat
  caller : FnSig
  callerBody : SAnw
  atCaller : (Aufloesung.loeseL (Aufloesung.quelle items) [] items)[callerIndex]? =
    some (.fnT caller callerBody)
  path : List Nat
  call : SLibraryCall
  atCall : libraryCallAt path callerBody = some call

/-- An ordinary translator unit contains the exact retained body and clauses, changing only its
    declaration kind to `impl`. Dependencies retain their source definitions. No clause is dropped.
    Table-to-value schema adaptation and general C17 instantiation remain refused by this stage. -/
def translatorItems (members : List SItemTief) (library : ULibrary) : List SItemTief :=
  members.filter (fun
    | .typeT .. | .constT .. | .tableT .. => true
    | _ => false) ++
    [.fnT { library.translator with art := "impl" } library.translatorBody]

/-- A source-bound declared map. The existing elaborator and typed lowering, rather than an
    independent evaluator or a same-name body, determine the program whose execution is certified.
    This first stage admits call-free bounded translators; recursive/general maps require C17. -/
structure TranslationDecl (source : LibrarySource) (u : UProg) where
  library : ULibrary
  resolved : libraryDecl (Aufloesung.loeseL (Aufloesung.quelle source.items) [] source.items)
    source.call = .ok library
  elaborated : elabU (pre108 (translatorItems
    (Aufloesung.loeseL (Aufloesung.quelle source.items) [] source.items) library)) = .ok u
  program : Programm (declOf u)
  functions : List (declOf u).Fn
  lowered : lowerAllg u = .ok (program, functions)
  translator : (declOf u).Fn
  translatorName : (fnAt u translator).name = library.translator.name
  schema : IntegerSchema
  parameters : (declOf u).params translator = [schema.ty]
  outputType : Ty
  result : (declOf u).erg translator = some outputType
  immutable : ImmutablePayload outputType
  noCalls : (befund program translator).rufe = []
  noIndirectCalls : (befund program translator).sigs = []
  bounded : (befund program translator).ewig = false
  noCycle : ∀ callee, zykS program functions translator callee = false

/-- The translator receives exactly its decoded by-value input. -/
def TranslationDecl.arguments {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) (input : Wert (declOf u) decl.schema.ty) :
    Env (declOf u) ((declOf u).params decl.translator) :=
  decl.parameters.symm ▸ Env.cons input Env.nil

/-- Output values travel through the declared result type, retaining all range/shape proofs. -/
def TranslationDecl.answer {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) (output : Wert (declOf u) decl.outputType) :
    ErgVal (declOf u) ((declOf u).erg decl.translator) :=
  decl.result.symm ▸ output

/-- The stronger C02 promise: exact execution of the source-selected body on the decoded input.
    The finite kernel proof is supplied by an untrusted candidate producer. It covers every
    oracle, world and loop budget with the same output and unchanged world: there can be no
    hidden runtime input, carrier/foreign/atomic/lock effect, reason, logic or hardware stop.
    Compilation effort is not charged to the runtime program's `ZeitAb`. -/
structure TranslationCertificate {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) where
  input : Wert (declOf u) decl.schema.ty
  decoded : decodeIntegerRows (declOf u) decl.schema source.call.region = some input
  output : Wert (declOf u) decl.outputType
  fuel : Nat
  execution : ∀ (oracle : Orakel (declOf u)) (passes : Nat) (world : World (declOf u)),
    rufAt decl.program oracle passes fuel decl.translator world (decl.arguments input) =
      .ok world (decl.answer output)

/-- A well-typed wrong result cannot reuse a certificate for a different execution result. -/
theorem translation_result_unique {source : LibrarySource} {u : UProg}
    {decl : TranslationDecl source u} (certificate : TranslationCertificate decl)
    (oracle : Orakel (declOf u)) (passes : Nat) (world : World (declOf u))
    (other : ErgVal (declOf u) ((declOf u).erg decl.translator))
    (execution : rufAt decl.program oracle passes certificate.fuel decl.translator world
      (decl.arguments certificate.input) = .ok world other) :
    other = decl.answer certificate.output := by
  have equality := (execution.symm.trans (certificate.execution oracle passes world))
  cases equality
  rfl

/-- The source-selected bounded translator has no recursive obligation hidden behind a token
    `decreases` claim: the typed body has no direct or indirect callees at all. -/
theorem translation_no_direct_call {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) (callee : (declOf u).Fn) :
    direkt decl.program decl.translator callee = false := by
  simp only [direkt, decl.noCalls, decl.noIndirectCalls, List.contains_nil, List.any_nil,
    Bool.false_or]

/-- The actual source-derived typed call graph discharges the existing measure duty, with no
    trusted termination flag and no new hardware premise. General recursive maps remain refused. -/
theorem translation_measure {source : LibrarySource} {u : UProg}
    (decl : TranslationDecl source u) (passes : Nat) (Q : AxEns (declOf u))
    (S : SperrInv (declOf u)) (T : (declOf u).Tab ⊕ (declOf u).Glob → Prop) :
    MassPflicht decl.program passes Q S T Mass.leer (zykS decl.program decl.functions) decl.translator :=
  massPflicht_ohne_zyklus decl.program decl.functions passes Q S T Mass.leer decl.translator decl.noCycle

/-!
Open C02 boundaries: immutable payload initialization/disjointness and ordinary library-call
expansion are not yet represented in `Akzeptiert(X)`. Consequently `elabU` still refuses library
bodies and source library calls. A `TranslationCertificate` alone cannot admit a runtime program.
Table-shaped translator parameters need the C01 schema-to-row-value export; general maps need
C17; selected layout/image and call/reason closure need C14/C08 and the Stage-0 owner. No new
language case is claimed complete by this module, and the Rust output-only scalar printer has
not been promoted to an exact translation certificate.
-/

#print axioms nutzlastZert_mem
#print axioms sumPayload_zert
#print axioms nutzlastZert_mem_zeuge
