module

public import Grammatik.Parser.Item.ElementTief

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Children in source order. An index path is a stable coordinate in the retained statement tree;
    library arguments and region tokens belong to the selected node, never to a name-only lookup. -/
def libraryChildren : SAnw → List SAnw
  | .block statements _ | .cases _ statements => statements
  | .cond _ yes branches no => yes :: (branches ++ no.toList)
  | .bindElse _ _ _ _ body | .elsif _ body | .arm _ _ body |
    .each _ _ _ _ _ _ _ body | .retry _ body | .loop _ body |
    .waive _ body | .trim _ _ body | .locks _ _ body | .watch _ body |
    .grow _ _ body | .child body => [body]
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

end Gabbro.Grammatik.Parser
