module
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ItemKind
public import Grammatik.Parser.Elab.Export.TraversalHeader
public import Grammatik.Kern.Syntax.Typen.DataRights
public import Grammatik.Parser.Elab.Uebersetze.MeasureSource
public import Grammatik.Parser.Profil.Auswahl
public import Grammatik.Parser.Profil.Platzierung
import all Init.Data.String.Basic
import all Init.Data.String.Defs
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- Read the complete existing consuming header. The contextual exporter checks the
    measure and declared domain/edge; the structured lowerer checks the retained touches.
    The original-source gate reuses this reader, so unsupported clauses cannot disappear. -/
def consumingHeader (raw : String) : Except String (SExpr × String) := do
  let tokens ← match lex raw with
    | .ok ts => pure ts
    | .error _ => throw "consuming traversal header does not lex"
  let rest ← match tokens with
    | .wort "decreases" :: rest => pure rest
    | _ => throw "consuming traversal requires decreases"
  let (expression, rest) ← parseOr 10000 rest
  let touchTokens ← match rest with
    | .wort "touches" :: rest => pure rest
    | _ => throw "consuming traversal requires touches consumes"
  let (_, rest) ← parseEffektListe 10000 touchTokens
  match rest with
  | [.ende] => pure (expression, String.intercalate " " (touchTokens.filterMap fun token =>
      match token with | .ende => none | _ => some (zeigeTok token)))
  | _ => throw "consuming traversal has an unsupported or duplicate header clause"

def typeMetadata : STyp → Bool
  | .raw _ | .entry .. | .wrap _ | .embed .. => true
  | .ptr _ rights (.atom target) =>
      (match Gabbro.Grammatik.DataRights.decode (fun _ => none) rights with
        | some r => r.owner.isSome
        | none => true) || target == "u8"
  | .ptr .. => true
  | .range ty _ _ _ | .array ty _ => typeMetadata ty
  | _ => false

/-- The type of a table field: a wrapping integer is bound, the elaborator records its modulus
    (`UTab.wraps`) and every store reduces the value (`uWrap`). -/
def fieldTypeMetadata : STyp → Bool
  | .wrap (.atom _) => false
  | t => typeMetadata t

/-- A written function-pointer type is bound at a parameter and at a `let`, the positions the
    elaborator collects pointer types from: it reads the head, the effects and the contract
    (`elabZeigerTyp`, an unreadable text refuses the unit), conformance is decided per function
    (`passtAt`), and a declared cost is checked (`CostBinding.ptrHolds`). -/
def pointerOrMetadata : STyp → Bool
  | .raw r => !r.startsWith "fn ("
  | t => typeMetadata t

/-- A conservative unit domain where no cost, scheduling, proof or reservation duty can disappear.
    Invariants are refused (no cost/runs/by binding); local annotations and nested continuations are inspected. -/
def bodyMetadata : Nat → SAnw → Bool
  | 0, _ => true
  | n + 1, .block ss _ => ss.any (bodyMetadata n)
  | n + 1, .bindElse _ ty _ _ b | n + 1, .bindAxiomOptElse _ ty _ _ b => ty.any typeMetadata || bodyMetadata n b
  | n + 1, .bindQ _ _ ty _ => ty.any typeMetadata
  | n + 1, .callQ .. => false
  | n + 1, .callIndElse _ _ _ body | n + 1, .callElse _ _ _ body => bodyMetadata n body
  | n + 1, .waive _ b | n + 1, .locks _ _ b | n + 1, .watch _ b |
    n + 1, .trim _ _ b => bodyMetadata n b
  | n + 1, .cond _ a bs b => bodyMetadata n a || bs.any (bodyMetadata n) || b.any (bodyMetadata n)
  | n + 1, .elsif _ b | n + 1, .arm _ _ b => bodyMetadata n b
  | n + 1, .cases _ arms => arms.any (bodyMetadata n)
  | _ + 1, .bind _ _ ty _ | _ + 1, .bindAxiomOpt _ ty _ => ty.any pointerOrMetadata
  | n + 1, .each _ _ _ _ mode raw _ body =>
    if mode == "consuming" then (consumingHeader raw).toOption.isNone || bodyMetadata n body
    else mode != "unvisited" || raw != "" || bodyMetadata n body
  /- A required allocation binds a plain index and runs no continuation: the
      counter narrowing is required, so a full arena is `Logik.kapazitaet` under
      the caller's `KoerperGutS/SA` duty -- no provider, storage-availability or
      failure-continuation duty can disappear. An explicit failure continuation
      uses the existing arena lowering and is recursively checked here. Mutable
      and type-annotated binders still elaborate to no G form. -/
  | _ + 1, .alloc false _ none _ _ none => false
  | n + 1, .alloc false _ none _ _ (some body) => bodyMetadata n body
  | n + 1, .retry header body => !retryHeaderBound header || bodyMetadata n body
  /- An atomic exchange and an atomic await are read completely by the elaborator: the static must be
      a declared atomic, the payload the declared one, the binder's written type the atomic's
      (`uBinderTyp`), and the update text parses or the unit is refused (`uTauschSchwanz`). -/
  | _ + 1, .swap _ ty _ _ | _ + 1, .await _ ty _ _ => ty.any typeMetadata
  /- A `forever` whose header is the plain one (label and `progress`) is read completely by the
      elaborator. A header with a pass bound and effects reaches this point only in its plain form:
      `eraseCovered` verified its effects, and the compiler checks its pass bound (`ForeverBinding`). -/
  | n + 1, .loop header body => !foreverPlain header || bodyMetadata n body
  | _ + 1, .alloc .. | _ + 1, .allocVon .. | _ + 1, .grow .. |
    _ + 1, .free .. | _ + 1, .child .. | _ + 1, .other .. => true
  | _ + 1, .genericCall .. => true
  | _ + 1, .set .. | _ + 1, .shift .. | _ + 1, .call .. |
    _ + 1, .leave .. | _ + 1, .next .. | _ + 1, .emit .. | _ + 1, .step .. |
    _ + 1, .ret .. | _ + 1, .start .. | _ + 1, .retires .. |
    _ + 1, .reset .. | _ + 1, .trimReq .. |
    _ + 1, .bindLib .. | _ + 1, .lcall .. => false

def clausesMetadata (clauses : List SKlausel) : Bool := clauses.any fun
  | .effs effects => effects.any (fun | .mints _ => true | _ => false)
  | .drops e => (Gabbro.Grammatik.Parser.Uebersetze.uMeasureSource e).toOption.isNone
  | .cost _ | .limit _ | .induc _ | .load _ | .moves .. | .quits _ | .keeps _ | .part _ | .arch _ | .refs _ => true
  | _ => false

/-- Payload clauses are consumed by the certified C02 expansion, so they do not refuse a library head. Every other cost/scheduling/proof clause still refuses. -/
def clausesMetadataWithoutLoad (clauses : List SKlausel) : Bool := clauses.any fun
  | .load _ => false
  | .effs effects => effects.any (fun | .mints _ => true | _ => false)
  | .drops e => (Gabbro.Grammatik.Parser.Uebersetze.uMeasureSource e).toOption.isNone
  | .cost _ | .limit _ | .induc _ | .moves .. | .quits _ | .keeps _ | .part _ | .arch _ | .refs _ => true
  | _ => false

/-- Whether an expression has the shape of a constant cost: literals, names, `+`, `*`, `-`, `/`. -/
def costShape : SExpr → Bool
  | .lit _ | .variable _ => true
  | .bin op a b =>
    (strEq op "+" || strEq op "*" || strEq op "-" || strEq op "/") && costShape a && costShape b
  | _ => false

/-- Whether a cost clause has no binding: a constant cost expression is bound. The compiler refuses
    one without a value (`CostBinding.unvalued`) and checks the K001 Bool `kostenPasst` over every
    function that declares one (`CostBinding.holds`), so the duty stays. -/
def costUnbound : SKlausel → Bool
  | .cost e => !costShape e
  | _ => false

/-- The clauses of an ordinary function: as `clausesMetadata`, with a constant cost expression bound. -/
def clausesMetadataFn (clauses : List SKlausel) : Bool :=
  clausesMetadata (clauses.filter fun | .cost _ => false | _ => true) || clauses.any costUnbound

/-- The clauses of a foreign prototype: as `clausesMetadata`, with a LITERAL cost only. Nothing values a
    prototype's cost (`CostBinding.unvalued` reads ordinary functions), so a cost expression stays refused. -/
def clausesMetadataProto (clauses : List SKlausel) : Bool :=
  clausesMetadata (clauses.filter fun | .cost _ => false | _ => true) ||
    clauses.any fun | .cost (.lit _) => false | .cost _ => true | _ => false

/-- The closed C15 merge operators: storage expansion only binds these five. -/
def accOperatorBound (m : String) : Bool :=
  strEq m "max" || strEq m "min" || strEq m "add" || strEq m "or" || strEq m "and"

def itemMetadata : SItemTief → Bool
  | .fnT sig body =>
    if sig.art == "library" then
      clausesMetadataWithoutLoad sig.klauseln || bodyMetadata 10000 body ||
        sig.params.any (fun p => typeMetadata p.2) || sig.res.any typeMetadata
    else (sig.art != "" && sig.art != "impl") ||
      clausesMetadataFn sig.klauseln || bodyMetadata 10000 (eraseCovered (touchesAdmitted sig.klauseln) (sig.params.map (·.1)) 10000 body) ||
      sig.params.any (fun p => pointerOrMetadata p.2) || sig.res.any typeMetadata
  /- Tagged groups expand to ordinary functions before elaboration. Inspect every original
      header and implementation body, so expansion cannot erase cost/proof/type duties. -/
  | .specGroupT _ _ _ functions => functions.any fun sig =>
      sig.art != "spec" || clausesMetadata sig.klauseln ||
        sig.params.any (fun p => typeMetadata p.2) || sig.res.any typeMetadata
  | .implGroupT _ receivers _ functions => receivers.any typeMetadata || functions.any fun
      | .fnT sig body =>
        sig.art != "impl" || clausesMetadata sig.klauseln || bodyMetadata 10000 body ||
          sig.params.any (fun p => typeMetadata p.2) || sig.res.any typeMetadata
      | _ => true
  | .taggedByT declaration _ => itemMetadata declaration
  | .moduleTemplateT .. | .moduleUseT .. => true
  | .transT _ translator _ => clausesMetadata translator.klauseln ||
      translator.params.any (fun p => typeMetadata p.2) || translator.res.any typeMetadata
  /- A Boolean `spec fn` is bound: `uSpecArgs` checks scalar arguments against their declared
      parameter types before `uSpecEin` substitutes them. The resulting predicate is elaborated
      in the contract's scope, with no erased type/proof metadata. -/
  | .specT sig _ => sig.params.any (fun p => typeMetadata p.2) || !sig.generics.isEmpty || sig.fehler.isSome ||
      !(match sig.res with | some (.atom "bool") => true | _ => false) ||
      sig.klauseln.any fun | .effs [.pure] => false | _ => true
  | .callT sc => sc.params.any (fun p => typeMetadata p.2) || sc.res.any typeMetadata
  /- A foreign prototype's literal cost is an assumption about the foreign body, like a gate's: a
      foreign call is one own step of machine G whatever the body takes. -/
  | .protoT sig => clausesMetadataProto sig.klauseln || sig.params.any (fun p => typeMetadata p.2) ||
      sig.res.any typeMetadata
  | .tableT _ provider _ place _ _ parts _ => provider.isSome || place.isSome ||
      parts.any fun
        | .tSlot fields => fields.any (fun field => fieldTypeMetadata field.ftyp || field.pos.isSome ||
            field.bezug.isSome || field.wo.isSome || field.reserviert || field.byOps)
        | .tTree _ => false
        | _ => true
  /- A literal hold bound is bound: the compiler checks K002 over every section of the lock
      (`HeldBinding.holds`). Reservation, mask and invariant stay refused. -/
  | .lockT _ _ _ held reserve mask inv =>
    (match held with | none | some (.lit _) => false | some _ => true) || reserve.isSome || mask.isSome || inv.isSome
  /- A static arena declaration carries no unbound metadata: literal reservation
      and bound, no dynamic ceiling, a checked element type and no
      provider/proof binding (`uArenen` refuses the dynamic and placed shapes;
      the static arena commits all its slots, so the required allocation's only
      duty is the counter bound under `KoerperGutS/SA`). -/
  | .arenaT _ (.lit _) (.lit _) none ty none => typeMetadata ty
  | .groupT .. => true
  /- Alignment is read and validated by the existing profile/uGlobs path. Names
      need its real constant environment; sections remain an unbound duty here. -/
  | .globT _ _ ty _ alignment sectionName _ => typeMetadata ty || alignment.any (fun e =>
      match e with
      | .variable _ => false
      | _ => (ProfilBindung.ausrichtungWert [] e).isNone) || sectionName.isSome
  | .adaptT s ps adapter b => (s.art != "" && s.art != "impl") ||
    clausesMetadata s.klauseln || (b.map (bodyMetadata 10000)).getD false ||
    adapter.vorspiel.any (bodyMetadata 10000) || adapter.sonst.any (fun (_, body) => bodyMetadata 10000 body) ||
    ps.any (fun | .neu _ t => typeMetadata t | _ => false) || s.res.any typeMetadata
  | .typeT ["tagged"] _ [] [] (some (.raw _)) => false
  -- A record schema resolves through the checked record collector, not metadata.
  | .typeT [] _ [] [] (some (.raw text)) => !text.startsWith "{"
  | .typeT flags _ args order body =>
    if flags.any (· == "linear") then
      -- Nominal resources carry checked order metadata, never a copyable value body.
      !args.isEmpty || body.isSome ||
        flags.any (fun flag => flag != "linear" && flag != "ghost" && flag != "pub" && flag != "export")
    else !args.isEmpty || !order.isEmpty || body.any typeMetadata ||
      flags.any (fun flag => flag != "pub" && flag != "export")
  | .constT _ ty _ => typeMetadata ty
  | .trustT _ _ _ regs stack assumption service =>
    !regs.isEmpty || !stack.isEmpty || !assumption.isEmpty || service.isNone
  | .whyT .. => false
  | .stateT .. => false
  | .checkT c => c.sonde.isSome || bodyMetadata 10000 c.canFail
  | .accT _ _ m p _ => p.isNone || !accOperatorBound m
  | .assumT .. => false -- the unit keeps the name (`UProg.annahmen`); the assumption stays owed
  | .varT .. | .goalT .. | .concT .. => false -- backend data and roots: the image builder binds or refuses
  /- An atomic static: the elaborator binds its type and its payload (`uGlobs`; a table payload and
      `observed by` are refused there). The ordering word is no duty of the model: the atomic rely
      holds for every value a shared atomic read may return, whatever the ordering. A payload
      published through a `relaxed` atomic has no rule and stays refused. -/
  | .atomT _ ty payload ordering _ => typeMetadata ty ||
      (ordering == some "relaxed" && !(payload.getD []).isEmpty)
  | .modT .. | .useT .. | .asmT .. | .formatT .. | .devT .. | .axiomT .. | .rcuT ..
  | .walkT .. | .entryT .. | .bootT .. | .profT .. | .gateT .. | .pubT .. | .arenaT .. => true


/-- Scalar predicate parameters no longer refuse admission; erased type metadata still does. -/
theorem spec_parameter_metadata_zeuge :
    let sig : STyp → FnSig := fun typ =>
      { art := "spec", name := "small", params := [("x", typ)], res := some (.atom "bool"), fehler := none, klauseln := [] }
    itemMetadata (.specT (sig (.range (.atom "u32") (.lit 0) (.lit 100) false)) .tru) = false ∧
      itemMetadata (.specT (sig (.wrap (.atom "u32"))) .tru) = true := by
  exact ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.ExportMetadata
