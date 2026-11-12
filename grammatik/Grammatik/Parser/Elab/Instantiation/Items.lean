module
public import Std.Data.HashSet.Lemmas
public import Grammatik.Parser.Elab.Instantiation.Statements
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Schema
@[expose] public section
namespace Gabbro.Grammatik.Parser.Instantiation

def tablePart (scope : Scope) : STabTeil → SurfaceFacts
  | .tConst _ ty value => merge (inspectType scope ty) (constant scope value)
  | .tSlot fields => gather (fields.map (field scope))
  | .tInv inv => invariant scope inv
  | .tOps _ | .tTree _ | .tBusy _ => {}

def devicePart (scope : Scope) : SGerTeil → SurfaceFacts
  | .copy a b => merge (expression scope a) (expression scope b)
  | .reg reg => gather [inspectType scope reg.rtyp, expression scope reg.addr,
      optional (expression scope) reg.voraus]
  | .bank _ => {}
  | .trans trans => transition scope trans

def binding (scope : Scope) (b : SBind) : SurfaceFacts :=
  merge (expression scope b.id) (gather (b.codes.map fun (_, value, _) =>
    optional (expression scope) value))

def syscall (scope : Scope) (call : SSyscall) : SurfaceFacts :=
  let scope := scope.bind (call.params.map Prod.fst)
  let way := match call.way with
    | .lit _ _ bind _ => binding scope bind
    | .via _ => ({} : SurfaceFacts)
  gather [gather (call.params.map (fun p => inspectType scope p.2)),
    optional (inspectType scope) call.res, way, expressions scope call.gate.pre,
    expressions scope call.gate.post, gather (call.gate.uses.map (effect scope)),
    optional (expression scope) call.gate.cost]

def bootStep (scope : Scope) : SBootSchritt → SurfaceFacts
  | .call path args => merge (globalReference (String.intercalate "::" path))
      (expressions scope args)
  | .set _ value => expression scope value

mutual
/-- Every surface item constructor is listed explicitly. In particular, the test is recursive
    through ordinary modules, public wrappers, gates and all nested executable/check bodies. -/
def item (scope : Scope) : SItemTief → SurfaceFacts
  | .modT _ body => items scope body
  | .pubT body | .gateT body => item scope body
  | .moduleTemplateT _ _ _ | .moduleUseT _ _ _ | .adaptT _ _ _ _ => ⟨false, []⟩
  | .taggedByT decl _ => merge ⟨false, []⟩ (item scope decl)
  | .specGroupT _ _ _ functions => merge ⟨false, []⟩ (gather (functions.map (signature scope)))
  | .implGroupT _ types effects body => gather [⟨false, []⟩,
      gather (types.map (inspectType scope)), gather (effects.flatten.map (effect scope)), items scope body]
  | .useT _ | .assumT _ _ _ _ | .varT _ | .profT _ _ => {}
  -- The entrusted region is a carrier, never a function reference.
  | .trustT _ code _ _ _ _ service =>
    merge (if scope.carriers.contains code then {} else globalReference code)
      (optional globalReference service)
  | .typeT _ _ args _ result => merge (gather (args.map (inspectType scope)))
      (optional (inspectType scope) result)
  | .constT _ ty value => merge (inspectType scope ty) (constant scope value)
  | .globT _ _ ty value aligned _ _ => gather [inspectType scope ty, constant scope value,
      optional (expression scope) aligned]
  | .fnT sig body => merge (signature scope sig)
      (statement (scope.bind (sig.params.map Prod.fst)) body)
  | .transT target sig body => gather [globalReference target, signature scope sig,
      statement (scope.bind (sig.params.map Prod.fst)) body]
  | .protoT sig | .asmT sig _ => signature scope sig
  | .specT sig pred => merge (signature scope sig)
      (expression (scope.bind (sig.params.map Prod.fst)) pred)
  | .formatT _ aligned _ fields => merge (optional (expression scope) aligned)
      (gather (fields.map (field scope)))
  | .tableT _ provider count _ _ _ parts _ => gather [optional globalReference provider,
      optional (expression scope) count, gather (parts.map (tablePart scope))]
  | .arenaT _ lo hi maximum ty provider => gather [expression scope lo, expression scope hi,
      optional (expression scope) maximum, inspectType scope ty,
      optional (fun (_, value) => expression scope value) provider]
  | .whyT _ cases _ => gather (cases.map (fun (_, value, _) => expression scope value))
  | .stateT _ transitions => gather (transitions.map (transition scope))
  | .devT _ params _ parts =>
    let scope := scope.bind (params.map Prod.fst)
    merge (gather (params.map (fun p => inspectType scope p.2)))
      (gather (parts.map (devicePart scope)))
  | .axiomT _ params result pred effects _ =>
    let scope := scope.bind (params.map Prod.fst)
    gather [gather (params.map (fun p => inspectType scope p.2)), optional (inspectType scope) result,
      optional (expression scope) pred, gather (effects.map (effect scope))]
  | .checkT check => gather [expressions scope check.misst, statement scope check.canFail,
      expressions scope check.boden, gather (check.gates.map globalReference)]
  | .atomT _ ty values _ _ => merge (inspectType scope ty)
      (optional (expressions scope) values)
  | .lockT _ places rank held shared _ inv => gather [expressions scope places,
      expression scope rank, optional (expression scope) held, optional (expression scope) shared,
      optional (expression scope) inv]
  | .rcuT _ places epoch => merge (expressions scope places) (optional (expression scope) epoch)
  | .groupT _ _ invs => gather (invs.map (invariant scope))
  -- A root path selects its last segment, as the root reader of the elaborator does.
  | .concT roots => gather (roots.map fun (path, args) =>
      merge (optional globalReference path.getLast?) (expressions scope args))
  | .accT _ ty _ value _ => merge (inspectType scope ty) (optional (expression scope) value)
  | .walkT walk => gather [expression scope walk.stufen, inspectType scope walk.node,
      expression scope walk.dwhen, expression scope walk.blatt,
      gather (walk.invarianten.map (invariant scope))]
  -- Entry root and handler collection select this one resolved dispatch target.
  | .entryT entry => gather [optional (expression scope) entry.vektor,
      optional (expression scope) entry.ist, optional globalReference entry.dispatch.getLast?]
  | .bootT _ _ steps _ => gather (steps.map (bootStep scope))
  | .callT call => syscall scope call
  | .goalT _ binds => optional (fun (_, _, entries) => gather (entries.map fun (_, b, _) =>
      binding scope b)) binds

def items (scope : Scope) : List SItemTief → SurfaceFacts
  | [] => {}
  | head :: rest => merge (item scope head) (items scope rest)
end

/-- Type names are constructor/conversion heads. Tagged case names come from the existing
    schema reader, not a second parser or a whitelist inferred from successful call lookup. -/
def constructorNames (source : List SItemTief) : List String :=
  let names := source.filterMap fun
    | .typeT _ name _ _ _ => some name
    | _ => none
  let cases := match Uebersetze.uSumSchemas source with
    | .ok schemas => schemas.flatMap (fun schema => schema.cases.map Prod.fst)
    | .error _ => []
  names ++ cases

def carrierNames (source : List SItemTief) : List String :=
  source.filterMap fun
    | .tableT name _ _ _ _ _ _ _ | .arenaT name _ _ _ _ _ => some name
    | _ => none

/-- No generic headers, explicit applications, parametric modules or literal-bearing generic
    arguments remain anywhere in the structured surface AST. Raw strings keep their existing
    parser/checker obligations; this is not a claim of acceptance or of executable correctness. -/
def ohneGenerik (source : List SItemTief) : Bool := (items {} source).ordinary

/-- Direct global references in every structured AST field, including addresses, contracts,
    nested arguments and concurrent/boot roots. Builtins, nominal constructors and calls through
    lexically bound local function pointers are excluded and retain their ordinary rules.
    Function addresses always count, including under local shadowing; `&Table` is a carrier
    address, not a function reference. Generated call targets always count under local shadowing.
    Library macro regions and opaque raw strings are checked by their subsequent elaborators. -/
def directReferences (source : List SItemTief) : List String :=
  (items { constructors := constructorNames source, carriers := carrierNames source } source).references

def functionName : SItemTief → Option String
  | .fnT sig _ | .protoT sig | .specT sig _ | .asmT sig _ | .transT _ sig _ => some sig.name
  | .axiomT name _ _ _ _ _ => some name
  | .callT call => some call.name
  | .trustT name _ _ _ _ _ _ => some name
  | _ => none

/-- Every callable declaration of the output: functions, foreign items, the wrapper an
    `entrust` item generates, and the function each declared transition generates. -/
def functionNames (source : List SItemTief) : List String :=
  source.filterMap functionName ++ source.flatMap fun
    | .stateT _ transitions => transitions.map (·.tname)
    | _ => []

/-- Unknown direct global references fail this check as well as missing generated targets. -/
def closed (source : List SItemTief) : Bool :=
  (directReferences source).all ((functionNames source).contains)

/-- `closed` against a set of the declared names (a list scan per reference was n² for n functions). -/
def closedSchnell (source : List SItemTief) : Bool :=
  let names := Std.HashSet.ofList (functionNames source)
  (directReferences source).all fun name => names.contains name

/-- **The set decides the same closedness.** -/
@[csimp] theorem closed_eq_schnell : @closed = @closedSchnell := by
  funext source
  unfold closed closedSchnell
  simp only [Std.HashSet.contains_ofList]

/-- Boolean closedness is exactly membership in the output's declaration list. -/
theorem closed_sound (source : List SItemTief) (h : closed source = true) :
    ∀ name ∈ directReferences source, name ∈ functionNames source := by
  intro name member
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h name member)

end Gabbro.Grammatik.Parser.Instantiation
