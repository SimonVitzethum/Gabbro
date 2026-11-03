module
public import Grammatik.Parser.Elab.Instantiation.Surface
@[expose] public section
namespace Gabbro.Grammatik.Parser.Instantiation

def ending (scope : Scope) : SEnde → SurfaceFacts
  | .ret value => optional (expression scope) value
  | .leave _ | .next _ => {}

/-- A library invocation names a declared library function. Its raw macro region is expanded by
    the subsequent existing elaborator; its expression arguments already satisfy both conditions. -/
def libraryCall (scope : Scope) (call : SLibraryCall) : SurfaceFacts :=
  merge (globalReference (String.intercalate "::" call.function)) (expressions scope call.args)

mutual
/-- Exhaustive over statements, including branch bodies, type annotations and block enders.
    The block traversal follows lexical binding order; a later local cannot hide an earlier call. -/
def statement (scope : Scope) : SAnw → SurfaceFacts
  | .bind _ _ ty value | .bindAxiomOpt _ ty value | .await _ ty value _ | .swap _ ty value _ =>
    merge (optional (inspectType scope) ty) (expression scope value)
  | .bindElse _ ty value _ body | .bindAxiomOptElse _ ty value _ body => gather [optional (inspectType scope) ty,
      expression scope value, statement scope body]
  | .bindLib _ _ ty call => merge (optional (inspectType scope) ty) (libraryCall scope call)
  | .set place _ value | .emit place value _ => merge (expression scope place) (expression scope value)
  | .shift place _ _ | .free place | .trimReq place _ => expression scope place
  | .callIndElse pointer args reason body => gather [expression scope pointer, expressions scope args,
      statement (scope.bind [reason]) body]
  | .callElse name args reason body => gather [reference scope name, expressions scope args,
      statement (scope.bind [reason]) body]
  | .call name args => merge (reference scope name) (expressions scope args)
  | .genericCall _ _ args => merge ⟨false, []⟩ (expressions scope args)
  | .bindQ _ _ ty value => gather [⟨false, []⟩, optional (inspectType scope) ty, expression scope value]
  | .callQ name args => gather [⟨false, []⟩, reference scope name, expressions scope args]
  | .lcall call => libraryCall scope call
  | .cond value yes branches no => gather [expression scope value, statement scope yes,
      statementsIndependent scope branches, optional (statement scope) no]
  | .elsif value body | .trim value _ body | .locks _ value body =>
    merge (expression scope value) (statement scope body)
  | .cases value arms => merge (expression scope value) (statementsIndependent scope arms)
  | .arm _ binder body => statement (scope.bind binder.toList) body
  | .each binder start _ subject _ _ inv body => gather [optional (expression scope) start,
      expression scope subject, optional (expression (scope.bind [binder])) inv,
      statement (scope.bind [binder]) body]
  | .retry _ body | .loop _ body | .waive _ body | .watch _ body | .child body => statement scope body
  | .leave _ | .next _ | .step _ _ | .other _ => {}
  | .ret value => optional (expression scope) value
  | .alloc _ _ ty _ count no => gather [optional (inspectType scope) ty, expression scope count,
      optional (statement scope) no]
  | .reset _ span => optional (fun (a, b) => merge (expression scope a) (expression scope b)) span
  | .grow _ count body => merge (expression scope count) (statement scope body)
  | .start names => gather (names.map globalReference)
  | .block body ender => statements scope body ender
  | .allocVon _ _ ty _ => optional (inspectType scope) ty

def statementsIndependent (scope : Scope) : List SAnw → SurfaceFacts
  | [] => {}
  | body :: rest => merge (statement scope body) (statementsIndependent scope rest)

def statements (scope : Scope) : List SAnw → Option SEnde → SurfaceFacts
  | [], ender => optional (ending scope) ender
  | body :: rest, ender => merge (statement scope body)
      (statements (scope.bind (Aufloesung.gebunden body)) rest ender)
end

end Gabbro.Grammatik.Parser.Instantiation
