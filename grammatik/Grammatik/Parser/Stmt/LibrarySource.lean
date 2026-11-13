module

public import Grammatik.Parser.Item.ElementTief

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Children in source order. An index path is a stable coordinate in the retained statement tree;
    library arguments and region tokens belong to the selected node, never to a name-only lookup. -/
def libraryChildren : SAnw → List SAnw
  | .block statements _ | .cases _ statements => statements
  | .cond _ yes branches no => yes :: (branches ++ no.toList)
  | .bindElse _ _ _ _ body | .bindAxiomOptElse _ _ _ _ body | .elsif _ body | .arm _ _ body |
    .each _ _ _ _ _ _ _ body | .boundedLoop _ body | .retry _ body | .loop _ body |
    .waive _ body | .trim _ _ body | .locks _ _ body | .watch _ body |
    .grow _ _ body | .child body | .callIndElse _ _ _ body | .callElse _ _ _ body => [body]
  | .alloc _ _ _ _ _ no => no.toList
  | _ => []

/-- Look up an exact source call, including its ordered arguments and unmodified region. -/
def libraryCallAt : List Nat → SAnw → Option SLibraryCall
  | [], .lcall call | [], .bindLib _ _ _ call => some call
  | [], _ => none
  | index :: path, body => do
      let child ← (libraryChildren body)[index]?
      libraryCallAt path child

/-- Complete declarations of one resolved library binding. Bodies, clauses, result/reason channels
    and parameter order remain available to the ordinary exporter. This is metadata, not admission. -/
structure ULibrary where
  function : FnSig
  body : SAnw
  translator : FnSig
  translatorBody : SAnw
  payload : List String
  functionIndex : Nat
  translatorIndex : Nat
  deriving Repr

/-- Resolve exactly one library function and exactly one translator. Never choose the first
    matching declaration or reconstruct an argument from its position. The call carries resolved
    paths: after `loeseL` the function path is the singleton item key, so the qualifier that
    disambiguated it is compared whole. Empty paths (unproducible by the reader) refuse by name.
    Payload typing and execution still require a certificate; this operation alone cannot enable
    a source export. -/
def libraryDecl (members : List SItemTief) (call : SLibraryCall) : Except String ULibrary := do
  if call.library.isEmpty then throw "C02: library call without library path"
  if call.function.isEmpty then throw "C02: library call without function path"
  let wanted := "::".intercalate call.function
  let functions := members.zipIdx |>.filterMap fun (item, index) => match item with
    | .fnT sig body =>
      if strEq sig.art "library" && strEq sig.name wanted then some (sig, body, index) else none
    | _ => none
  let (sig, body, functionIndex) ← match functions with
    | [entry] => .ok entry
    | [] => .error "C02: library function is unresolved"
    | _ => .error "C02: library function is ambiguous"
  let translators := members.zipIdx |>.filterMap fun (item, index) => match item with
    | .transT target translator body =>
      if strEq target wanted then some (translator, body, index) else none
    | _ => none
  let (translator, translatorBody, translatorIndex) ← match translators with
    | [entry] => .ok entry
    | [] => .error "C02: library function has no translator"
    | _ => .error "C02: library function has multiple translators"
  let payloads := sig.klauseln.filterMap fun | .load path => some path | _ => none
  let payload ← match payloads with
    | [path] => .ok path
    | _ => .error "C02: library function needs exactly one payload declaration"
  if sig.params.length != call.args.length + 1 then
    throw "C02: caller must omit exactly the final payload parameter"
  match sig.params.getLast? with
  | some (_, .ptr "normal" "r" target) =>
    let targetName := match target with
      | .atom name => some name
      | .path path => some ("::".intercalate path)
      | _ => none
    if targetName != some ("::".intercalate payload) then
      throw "C02: final read-only parameter does not name the declared payload"
  | _ => throw "C02: payload parameter must be a read-only table capability"
  pure ⟨sig, body, translator, translatorBody, payload, functionIndex, translatorIndex⟩

/-! ## C02 source-level expansion vocabulary.

    The certified expansion of a library call into an ordinary call runs here, at source level, so
    the export (`Parser/Elab/Uebersetze`, via `exportLibraryUnit` in `elabU`) and the certificate
    (`Logik/Vertraege/Uebersetzung`, via `LibraryExpansion`) share one gate and one shape. The
    cleanliness predicate (`ohneBibliothekAnw`) documents the correspondence: the elaborator's C02
    guard matches exactly the two false constructors, so expansion output takes the existing
    lowering (`uAnw1`, `uRuf`). -/

/- Whether a source statement still contains a library call: the elaborator's C02 guard matches
    exactly the two false constructors (`uAnwReihe`). Lists ride in their own helpers, like
    `beqSAnw`/`beqSAnwList`. -/
mutual
def ohneBibliothekAnw : SAnw → Bool
  | .bindLib .. | .lcall .. => false
  | .bindElse _ _ _ _ body | .elsif _ body | .arm _ _ body | .boundedLoop _ body | .retry _ body | .loop _ body |
    .waive _ body | .trim _ _ body | .locks _ _ body | .watch _ body | .grow _ _ body |
    .child body | .each _ _ _ _ _ _ _ body | .callIndElse _ _ _ body | .callElse _ _ _ body => ohneBibliothekAnw body
  | .cond _ yes branches no =>
    ohneBibliothekAnw yes && ohneBibliothekAnwListe branches && ohneBibliothekAnwOpt no
  | .cases _ arms => ohneBibliothekAnwListe arms
  | .block statements _ => ohneBibliothekAnwListe statements
  | .alloc _ _ _ _ _ no => ohneBibliothekAnwOpt no
  | _ => true
def ohneBibliothekAnwListe : List SAnw → Bool
  | [] => true
  | s :: ss => ohneBibliothekAnw s && ohneBibliothekAnwListe ss
def ohneBibliothekAnwOpt : Option SAnw → Bool
  | none => true
  | some s => ohneBibliothekAnw s
end

/-- Product payload rows need the C01 schema export; they are refused here by name. No product
    schema exists yet: `IntegerSchema` is the only decoder and `ImmutablePayload` admits no
    product. -/
def produktZeilenVerweigert : String := "C01: product payload rows need the C01 schema export"

/-- Recursive and general translator maps need C17 instantiation and control rules; they are
    refused here by name. A translator with callees cannot satisfy `TranslationDecl.noCalls`,
    `noIndirectCalls` or `noCycle`, so no certificate path exists for it. -/
def allgemeineAbbildungVerweigert : String :=
  "C17: recursive and general translator maps need C17 control rules"

/-- Pre-expansion gate: admit only integer-row, call-free translators into the certificate path.
    The export supplies the two evidence bits from the resolved declaration; products refuse
    under the C01 name, callees under the C17 name. Kernel-checked certificate correctness stays
    a separate proof, never a trusted flag. -/
def torZurErweiterung (schemaOk ruffrei : Bool) : Except String Unit :=
  if !schemaOk then .error produktZeilenVerweigert
  else if !ruffrei then .error allgemeineAbbildungVerweigert
  else .ok ()

/- Whether a surface expression calls anything. Stage 1 certifies only call-free bounded maps
    (`TranslationDecl.noCalls`), so a translator body holding a call needs the C17 control rules.
    `Some`/`None` data constructors are values, not calls. -/
mutual
def callFreeExpr : SExpr → Bool
  | .call "None" [] => true
  | .call "Some" [a] => callFreeExpr a
  | .call _ _ => false
  | .built _ _ => false
  | .ext .call _ _ | .ext .instantiate _ _ => false
  | .ext _ _ xs => callFreeExprs xs
  | .field a _ => callFreeExpr a
  | .index a i => callFreeExpr a && callFreeExpr i
  | .arrow a _ => callFreeExpr a
  | .un _ a => callFreeExpr a
  | .bin _ a b => callFreeExpr a && callFreeExpr b
  | .old a => callFreeExpr a
  | _ => true
def callFreeExprs : List SExpr → Bool
  | [] => true
  | e :: rest => callFreeExpr e && callFreeExprs rest
end

/- Whether a translator body is stage-1 certifiable: no call, no control needing C17
    instantiation rules (`each`/`loop`/`retry`), and no memory, thread, atomic or device effect.
    Pure data flow (`bind`, `set`, conditions, matches, narrowing) rides through; anything the
    ordinary elaborator refuses (`waive`, `other`, `leave`, `next`) keeps its own precise refusal
    there instead of a misleading gate name. -/
mutual
def callFreeStmt : SAnw → Bool
  | .call _ _ | .callElse .. | .callIndElse .. | .lcall _ | .bindLib _ _ _ _ => false
  | .each _ _ _ _ _ _ _ _ | .loop _ _ | .boundedLoop _ _ | .retry _ _ => false
  | .emit _ _ _ | .await _ _ _ _ | .swap _ _ _ _ => false
  | .alloc _ _ _ _ _ _ | .allocVon _ _ _ _ | .reset _ _ | .grow _ _ _ | .free _ | .genericCall _ _ _ => false
  | .child _ | .start _ | .step _ _ | .shift _ _ _ | .locks _ _ _ | .watch _ _ | .retires _ => false
  | .bind _ _ _ e => callFreeExpr e
  | .bindElse _ _ e _ body => callFreeExpr e && callFreeStmt body
  | .bindQ _ _ _ e => callFreeExpr e
  | .callQ _ _ => false
  | .set l _ r => callFreeExpr l && callFreeExpr r
  | .cond c yes branches no =>
    callFreeExpr c && callFreeStmt yes && callFreeStmts branches && callFreeOpt no
  | .elsif c body => callFreeExpr c && callFreeStmt body
  | .cases e arms => callFreeExpr e && callFreeStmts arms
  | .arm _ _ body => callFreeStmt body
  | .trim e _ body => callFreeExpr e && callFreeStmt body
  | .ret e => e.all callFreeExpr
  | .block statements ende => callFreeStmts statements && callFreeEnder ende
  | _ => true
def callFreeStmts : List SAnw → Bool
  | [] => true
  | s :: ss => callFreeStmt s && callFreeStmts ss
def callFreeOpt : Option SAnw → Bool
  | none => true
  | some s => callFreeStmt s
def callFreeEnder : Option SEnde → Bool
  | none => true
  | some (.ret e) => e.all callFreeExpr
  | some _ => true
end

/-- The payload place of an export expansion: the declared payload table as a fresh read-only
    capability (`&T`), which `uArg` elaborates into the final parameter the caller omits. The name
    is the payload the resolution verified (`libraryDecl` checks it against the final parameter),
    never a guessed table. -/
def libraryPayloadArg (lib : ULibrary) : SExpr := .fnref ("::".intercalate lib.payload)

/-- Expand one source library call into its ordinary call: the resolved library function key,
    the ordinary arguments once in source order, and the per-site payload appended last. -/
def exportLibraryCall (lib : ULibrary) (c : SLibraryCall) : SAnw :=
  .call lib.function.name (c.args ++ [libraryPayloadArg lib])

/-- The `let`-bound form of the export expansion: the ordinary call value bound as usual. -/
def exportLibraryBind (bind : Bool) (x : String) (ty : Option STyp) (lib : ULibrary)
    (c : SLibraryCall) : SAnw :=
  .bind bind x ty (.call lib.function.name (c.args ++ [libraryPayloadArg lib]))

/-- Expanded statements contain no library construct, so the existing lowering applies to them. -/
theorem ohneBibliothekAnw_export (lib : ULibrary) (c : SLibraryCall) :
    ohneBibliothekAnw (exportLibraryCall lib c) = true := rfl

/-- Expanded `let`-bound statements contain no library construct either. -/
theorem ohneBibliothekAnw_exportBind (bind : Bool) (x : String) (ty : Option STyp)
    (lib : ULibrary) (c : SLibraryCall) :
    ohneBibliothekAnw (exportLibraryBind bind x ty lib c) = true := rfl

/- Rewrite one statement: library calls expand against the resolved members through the shared
    gate, every other constructor keeps its shape with rewritten children. Surface expressions
    ride through unchanged: the payload is appended, never substituted. -/
mutual
def exportLibraryStmt (members : List SItemTief) : SAnw → Except String SAnw
  | .lcall c =>
    match libraryDecl members c with
    | .error e => .error e
    | .ok lib =>
      match torZurErweiterung true (callFreeStmt lib.translatorBody) with
      | .error e => .error e
      | .ok _ => .ok (exportLibraryCall lib c)
  | .bindLib m x ty c =>
    match libraryDecl members c with
    | .error e => .error e
    | .ok lib =>
      match torZurErweiterung true (callFreeStmt lib.translatorBody) with
      | .error e => .error e
      | .ok _ => .ok (exportLibraryBind m x ty lib c)
  | .callElse name args reason body =>
    (exportLibraryStmt members body).map (.callElse name args reason)
  | .callIndElse pointer args reason body =>
    (exportLibraryStmt members body).map (.callIndElse pointer args reason)
  | .bindElse y t e g b =>
    match exportLibraryStmt members b with
    | .error e => .error e
    | .ok b' => .ok (.bindElse y t e g b')
  | .cond c yes branches no =>
    match exportLibraryStmt members yes with
    | .error e => .error e
    | .ok yes' =>
      match exportLibraryStmts members branches with
      | .error e => .error e
      | .ok branches' =>
        match exportLibraryOpt members no with
        | .error e => .error e
        | .ok no' => .ok (.cond c yes' branches' no')
  | .elsif c body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.elsif c body')
  | .cases e arms =>
    match exportLibraryStmts members arms with
    | .error e => .error e
    | .ok arms' => .ok (.cases e arms')
  | .arm n bnd body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.arm n bnd body')
  | .each bnd o k s m raw inv body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.each bnd o k s m raw inv body')
  | .boundedLoop h body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.boundedLoop h body')
  | .retry h body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.retry h body')
  | .loop h body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.loop h body')
  | .trim e g body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.trim e g body')
  | .locks sh p body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.locks sh p body')
  | .watch d body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.watch d body')
  | .grow an e body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.grow an e body')
  | .child body =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' => .ok (.child body')
  | .alloc mu x t an v no =>
    match exportLibraryOpt members no with
    | .error e => .error e
    | .ok no' => .ok (.alloc mu x t an v no')
  | .block ss ende =>
    match exportLibraryStmts members ss with
    | .error e => .error e
    | .ok ss' => .ok (.block ss' ende)
  | s => .ok s
def exportLibraryStmts (members : List SItemTief) : List SAnw → Except String (List SAnw)
  | [] => .ok []
  | s :: ss =>
    match exportLibraryStmt members s with
    | .error e => .error e
    | .ok s' =>
      match exportLibraryStmts members ss with
      | .error e => .error e
      | .ok ss' => .ok (s' :: ss')
def exportLibraryOpt (members : List SItemTief) : Option SAnw → Except String (Option SAnw)
  | none => .ok none
  | some s =>
    match exportLibraryStmt members s with
    | .error e => .error e
    | .ok s' => .ok (some s')
end

/-- Normalize one function head for the export: a `library fn` is an ordinary implemented function,
    so its body elaborates like `impl`. Its payload clause is consumed into the call-site expansions
    above (each site passes `&Payload`), hence stripped here rather than dropped silently. -/
def exportLibraryKopf (sig : FnSig) : FnSig :=
  if strEq sig.art "library" then { sig with art := "impl", klauseln := sig.klauseln.filter fun | .load _ => false | _ => true } else sig

/-- The certified-expansion pre-pass of the export: every function body expands, `library` heads
    normalize, and translators are consumed (they are certificate input, never runtime items).
    Units without library forms pass through with identical elaboration. -/
def exportLibraryUnitAux (members : List SItemTief) :
    List SItemTief → Except String (List SItemTief)
  | [] => .ok []
  | .transT _ _ _ :: rest => exportLibraryUnitAux members rest
  | .fnT sig body :: rest =>
    match exportLibraryStmt members body with
    | .error e => .error e
    | .ok body' =>
      match exportLibraryUnitAux members rest with
      | .error e => .error e
      | .ok rest' => .ok (.fnT (exportLibraryKopf sig) body' :: rest')
  | it :: rest =>
    match exportLibraryUnitAux members rest with
    | .error e => .error e
    | .ok rest' => .ok (it :: rest')

/-- Run the pre-pass over the resolved members: `elabU` calls this before the item check, so a
    source program with a library call exports to an ordinary unit. -/
def exportLibraryUnit (members : List SItemTief) : Except String (List SItemTief) :=
  exportLibraryUnitAux members members

end Gabbro.Grammatik.Parser
