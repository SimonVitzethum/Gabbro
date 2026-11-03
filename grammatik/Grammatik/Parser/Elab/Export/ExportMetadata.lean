module
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Kern.Syntax.Typen.DataRights
public import Grammatik.Parser.Elab.Uebersetze.MeasureSource
public import Grammatik.Parser.Profil.Auswahl
import all Init.Data.String.Basic
import all Init.Data.String.Defs
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- Read the complete existing consuming header. The contextual exporter checks the
    measure and declared domain/edge; the structured lowerer checks the retained touches.
    The original-source gate reuses this reader, so unsupported clauses cannot disappear. -/
def consumingHeader (raw : String) : Except String (SExpr × String) := do
  let tokens ← lex raw
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

/-- A conservative unit domain where no cost, scheduling, proof or reservation duty can disappear.
    Invariants are deliberately refused: their mandatory cost/runs/by binding is still absent.
    Local annotations and every nested continuation are inspected as well as function headers. -/
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
  | _ + 1, .bind _ _ ty _ | _ + 1, .bindAxiomOpt _ ty _ => ty.any typeMetadata
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
  | _ + 1, .retry .. | _ + 1, .loop .. | _ + 1, .swap .. | _ + 1, .await .. |
    _ + 1, .alloc .. | _ + 1, .allocVon .. | _ + 1, .grow .. |
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

/-- The closed C15 merge operators: storage expansion only binds these five. -/
def accOperatorBound (m : String) : Bool :=
  strEq m "max" || strEq m "min" || strEq m "add" || strEq m "or" || strEq m "and"

def itemMetadata : SItemTief → Bool
  | .fnT sig body =>
    if sig.art == "library" then
      clausesMetadataWithoutLoad sig.klauseln || bodyMetadata 10000 body ||
        sig.params.any (fun p => typeMetadata p.2) || sig.res.any typeMetadata
    else (sig.art != "" && sig.art != "impl") ||
      clausesMetadata sig.klauseln || bodyMetadata 10000 body ||
      sig.params.any (fun p => typeMetadata p.2) || sig.res.any typeMetadata
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
  | .specT .. => true -- Typed macro/proof admission is not supplied by predicate inlining alone.
  | .callT sc => sc.gate.cost.isSome || sc.params.any (fun p => typeMetadata p.2) ||
    sc.res.any typeMetadata
  | .protoT sig => clausesMetadata sig.klauseln || sig.params.any (fun p => typeMetadata p.2) ||
      sig.res.any typeMetadata
  | .tableT _ provider _ place _ _ parts => provider.isSome || place.isSome ||
      parts.any fun
        | .tSlot fields => fields.any (fun field => typeMetadata field.ftyp || field.pos.isSome ||
            field.bezug.isSome || field.wo.isSome || field.reserviert || field.byOps)
        | .tTree _ => false
        | _ => true
  | .lockT _ _ _ held reserve mask inv => held.isSome || reserve.isSome || mask.isSome || inv.isSome
  /- A static arena declaration carries no unbound metadata: literal reservation
      and bound, no dynamic ceiling, a checked element type and no
      provider/proof binding (`uArenen` refuses the dynamic and placed shapes;
      the static arena commits all its slots, so the required allocation's only
      duty is the counter bound under `KoerperGutS/SA`). -/
  | .arenaT _ (.lit _) (.lit _) none ty none => typeMetadata ty
  | .groupT .. => true
  | .globT _ _ ty _ bound proof _ => typeMetadata ty || bound.isSome || proof.isSome
  | .adaptT s ps adapter b => (s.art != "" && s.art != "impl") ||
    clausesMetadata s.klauseln || (b.map (bodyMetadata 10000)).getD false ||
    adapter.vorspiel.any (bodyMetadata 10000) || adapter.sonst.any (fun (_, body) => bodyMetadata 10000 body) ||
    ps.any (fun | .neu _ t => typeMetadata t | _ => false) || s.res.any typeMetadata
  -- A bare linear declaration introduces only a nominal resource, resolved
  -- by markFin and checked by the dependent G inventory; it has no value body.
  | .typeT ["linear"] _ [] [] none => false
  | .typeT ["tagged"] _ [] [] (some (.raw _)) => false
  -- A record schema resolves through the checked record collector, not metadata.
  | .typeT [] _ [] [] (some (.raw text)) => !text.startsWith "{"
  | .typeT flags _ args order body => !args.isEmpty || !order.isEmpty || body.any typeMetadata ||
      flags.any (fun flag => flag != "pub" && flag != "export")
  | .constT _ ty _ => typeMetadata ty
  | .trustT _ _ _ regs stack assumption service =>
    !regs.isEmpty || !stack.isEmpty || !assumption.isEmpty || service.isNone
  | .whyT .. => false
  | .stateT .. => false
  | .checkT c => c.sonde.isSome || bodyMetadata 10000 c.canFail
  | .accT _ _ m p _ => p.isNone || !accOperatorBound m
  | _ => true

def metadataReason : SItemTief → String
  | .tableT _ provider _ _ _ _ parts =>
    if parts.any (fun | .tInv _ => true | _ => false) then
      "invariant cost/runs/by duties lack a checked source binding"
    else if provider.isSome then "table provider duties lack a checked source binding"
    else "table field/type/placement duties lack a checked source binding"
  | .groupT .. => "invariant cost/runs/by duties lack a checked source binding"
  | .lockT _ _ _ held reserve _ inv =>
    if held.isSome || reserve.isSome then "held-time/reservation/proof duties lack a checked source binding"
    else if inv.isSome then "lock invariant duties lack a checked source binding"
    else "lock mask duties lack a checked source binding"
  | .specT .. => "spec signature/proof admission lacks a checked source binding"
  | .checkT c =>
    if c.sonde.isSome then "check counterprobe duties lack a checked source binding"
    else "check body duties lack a checked source binding"
  | .accT _ _ m p _ =>
    if !accOperatorBound m then "accumulator operator without G form"
    else "accumulator without per cpu count without G form"
  | .fnT sig _ =>
    if sig.art == "const" then
      "const function requires certified call-site substitution before runtime export: " ++ sig.name
    else if sig.klauseln.any (fun | .cost _ => true | _ => false) then
      "declared costs lack a checked source-to-kostenPasst binding: " ++ sig.name
    else "function type/proof/header duties lack a checked source binding: " ++ sig.name
  | .adaptT s _ _ _ => "adapter without expanded form: " ++ s.name
  | _ => "type/provider/proof duties lack a checked source binding"

def check (items : List SItemTief) : Except String Unit :=
  if items.any itemMetadata then
    .error ("source export: " ++ ((items.find? itemMetadata).map metadataReason).getD "unsupported metadata")
  else .ok ()

/-- Only the newly evaluable header/initializer positions need the new original-source gate. -/
def constantExpansion : SItemTief → Bool
  | .tableT _ _ (some count) _ _ _ _ | .arenaT _ _ count _ _ _ =>
      match count with | .lit _ | .variable _ => false | _ => true
  | .lockT _ _ rank _ _ _ _ => match rank with | .lit _ => false | _ => true
  | .globT _ _ _ (.one expression) _ _ _ =>
      match expression with
      | .lit _ | .un "-" (.lit _) | .variable _ | .tru | .fls | .ext .text _ _ | .call "None" [] => false
      | _ => true
  | _ => false

def checkConstants (items : List SItemTief) : Except String Unit :=
  if items.any constantExpansion then check items else .ok ()

/-- Successful new exports have no ignored metadata in the admitted source domain. -/
theorem check_sound (items : List SItemTief) (h : check items = .ok ()) : items.any itemMetadata = false := by
  unfold check at h
  cases hm : items.any itemMetadata <;> simp_all

/-- A unit without unsupported duties admits every guarded lowering. -/
theorem check_clear (items : List SItemTief) (h : items.any itemMetadata = false) :
    check items = .ok () := by simp [check, h]

theorem check_sound_zeuge :
    let body := SAnw.block [] (some (.ret (some (.lit 42))))
    let sig : FnSig := ⟨"impl", "sample", [], some (.atom "u8"), none,
      [.gives (.ext .imp [] [.tru, .tru])], []⟩
    check [.fnT sig body] = .ok () ∧
    check [.fnT {sig with klauseln := .cost (.lit 0) :: sig.klauseln} body] =
      .error "source export: declared costs lack a checked source-to-kostenPasst binding: sample" := by
  exact ⟨rfl, rfl⟩

/-- Every newly evaluable count/rank/initializer preserves the original unit's metadata duties. -/
theorem checkConstants_sound (items : List SItemTief)
    (used : items.any constantExpansion = true) (accepted : checkConstants items = .ok ()) :
    items.any itemMetadata = false :=
  check_sound items (by simpa only [checkConstants, used, ↓reduceIte] using accepted)

set_option maxRecDepth 100000 in
/-- Invariant duties stay unsupported regardless of where the guarded lowering occurs. -/
theorem invariant_refused_zeuge :
    check [.tableT "T" none (some (.lit 1)) none none false
      [.tInv ⟨"valid", .lit 1, true, none, .ext .imp [] [.tru, .tru]⟩]] =
      .error "source export: invariant cost/runs/by duties lack a checked source binding" := by rfl

set_option maxRecDepth 100000 in
/-- New forms cannot hide in an allocation failure continuation, child or local type annotation. -/
theorem nested_duties_refused_zeuge :
    let held := SAnw.bind false "held" none (.call "Held" [.variable "L"])
    let body := SAnw.block [held] (some (.ret (some (.lit 42))))
    let sig : FnSig := ⟨"impl", "sample", [], some (.atom "u8"), none, [.cost (.lit 0)], []⟩
    check [.fnT sig (.child body)] =
      .error "source export: declared costs lack a checked source-to-kostenPasst binding: sample" ∧
    bodyMetadata 10000 (.alloc false "cell" none "A" (.lit 0)
      (some (.bind false "value" (some (.wrap (.atom "bool"))) .tru))) = true ∧
    bodyMetadata 10000 (.grow "A" (.lit 1) body) = true ∧
    bodyMetadata 10000 (.bind false "value" (some (.wrap (.atom "bool"))) .tru) = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- C04 state transitions are bound by the exporter and the generic lowering. Every place resolves in the declaration scope (`uTransitionPlace`), every effect becomes an ordinary permission (`uEffekte`, pure/store conflict refused), atomic contracts are refused (`uTransitionAtomicFree`), aliasing needs agreement (`uTransitionDisjoint`), and every generated function is certified (`TransitionExpansion` via `lowerAllg_transition_certified`). A primitive edge keeps the constant `Stmt.shift` rule. -/
theorem stateT_bound (n : String) (ts : List STrans) : itemMetadata (.stateT n ts) = false := by rfl

set_option maxRecDepth 100000 in
theorem stateT_zeuge :
    let tr : STrans := ⟨"a", [(.variable "s", .variable "Idle", .variable "Busy")], none, []⟩
    let body := SAnw.block [] (some (.ret (some (.lit 42))))
    check [.stateT "S" [tr]] = .ok () ∧ check [.stateT "S" [tr], .fnT ⟨"impl", "sample", [], some (.atom "u8"), none, [.cost (.lit 0)], []⟩ body] = .error "source export: declared costs lack a checked source-to-kostenPasst binding: sample" := by
  exact ⟨rfl, rfl⟩

/-- C02 library calls are bound by the certified expansion. The payload clause is consumed (`exportLibraryKopf` strips `.load`), the call resolves to exactly one library function plus exactly one translator with exactly one payload (`libraryDecl`), and the translator body must be call-free (`callFreeStmt`, otherwise C17). Unexpanded calls never reach ordinary lowering (`ohneBibliothekAnw`, `uAnwReihe`). Costs and other clauses still refuse via `clausesMetadataWithoutLoad`. -/
theorem libraryFn_bound (sig : FnSig) (body : SAnw) (h : sig.art = "library") (c : clausesMetadataWithoutLoad sig.klauseln = false) (b : bodyMetadata 10000 body = false) (p : sig.params.any (fun p => typeMetadata p.2) = false) (r : sig.res.any typeMetadata = false) : itemMetadata (.fnT sig body) = false := by
  simp only [itemMetadata, h, beq_self_eq_true, ↓reduceIte, c, b, p, r, Bool.or_false]

theorem transT_bound (target : String) (translator : FnSig) (body : SAnw) (c : clausesMetadata translator.klauseln = false) (p : translator.params.any (fun p => typeMetadata p.2) = false) (r : translator.res.any typeMetadata = false) : itemMetadata (.transT target translator body) = false := by
  simp only [itemMetadata, c, p, r, Bool.or_false]

set_option maxRecDepth 100000 in
theorem library_zeuge :
    let lib : FnSig := ⟨"library", "f", [], none, none, [.load ["P"]], []⟩
    let trans : FnSig := ⟨"impl", "build", [], none, none, [], []⟩
    let caller : FnSig := ⟨"impl", "caller", [], some (.atom "u8"), none, [], []⟩
    let cbody := SAnw.block [.lcall ⟨["m"], ["f"], [], []⟩] (some (.ret (some (.lit 1))))
    check [.transT "f" trans (SAnw.block [] none), .fnT lib (SAnw.block [] none), .fnT caller cbody] = .ok () ∧ check [.fnT ⟨"library", "f", [], none, none, [.load ["P"], .cost (.lit 0)], []⟩ (SAnw.block [] none)] = .error "source export: declared costs lack a checked source-to-kostenPasst binding: f" := by
  exact ⟨rfl, rfl⟩

/-- C16 declared checks are bound by probe, wrapper and admission. Measures resolve by shape (`uMessOrt`), gates must name unit functions (`uCheck`, unknown gates refused), floors lower with the ordinary predicate reader (`uSichert`), probe bodies elaborate as ordinary Boolean producers (`uProbeFn`, non-block refused), generated names must be fresh (`uProbeNeu`, duplicates refused), wrappers consume exactly one Duty (`uTorHuelle`, parameterised or reason-carrying gates refused, sibling-check gates wait for C14), marks are checked (`uMarkenPruef`), and the checker decides read-only Duty threading with call-graph closure (`checkOkB`/`CheckAdmission`). Counterprobes (`sonde`) stay refused: no binding exists. -/
theorem checkT_bound (c : SCheck) (s : c.sonde = none) (b : bodyMetadata 10000 c.canFail = false) : itemMetadata (.checkT c) = false := by
  simp [itemMetadata, s, b]

set_option maxRecDepth 100000 in
theorem checkT_zeuge :
    let good : SCheck := ⟨"p", "c", [.variable "x"], ["g"], SAnw.block [] (some (.ret (some .tru))), [.tru], none⟩
    let bad : SCheck := ⟨"p", "c", [.variable "x"], ["g"], SAnw.block [] (some (.ret (some .tru))), [.tru], some ("probe", "expects")⟩
    check [.checkT good] = .ok () ∧ check [.checkT bad] = .error "source export: check counterprobe duties lack a checked source binding" := by
  exact ⟨rfl, rfl⟩

/-- C15 accumulators are bound by storage expansion. Admitted operators and per-cpu counts expand to
    private cells plus guarding locks (`uAkkuItem`, `uAkkuErweiterung` with neutral, range and count
    checked by name); uses expand to the generated query, update and reduction (`Akku.Expand`),
    and unsupported positions keep their narrow refusals there.
    Bad operators and missing counts keep the exact downstream refusals. -/
theorem accT_bound (n : String) (t : STyp) (m : String) (p : Option SExpr) (q : Option String) (o : accOperatorBound m = true) (e : p.isSome = true) : itemMetadata (.accT n t m p q) = false := by
  cases p with
  | none => simp at e
  | some _ => simp [itemMetadata, o]

set_option maxRecDepth 100000 in
theorem accT_zeuge :
    check [.accT "c" (.atom "u32") "add" (some (.lit 2)) none] = .ok () ∧ check [.accT "c" (.atom "u32") "xor" (some (.lit 2)) none] = .error "source export: accumulator operator without G form" ∧ check [.accT "c" (.atom "u32") "add" none none] = .error "source export: accumulator without per cpu count without G form" := by
  exact ⟨rfl, rfl, rfl⟩

/-- C18 resets are bound by checked range-store expansion. Arena resets elaborate to the used-counter store (`uAnw1`, unknown arenas refused); static-array ranges elaborate operands as body values and travel as `UStmt.resetRange` metadata (`uAnw1`, unknown statics and non-array statics refused), whose range validity and zero observation are discharged by the generic lowering (`lowResetRangeL`, `uReset_lower`). -/
theorem reset_bound (n : Nat) (a : String) (r : Option (SExpr × SExpr)) : bodyMetadata (n + 1) (.reset a r) = false := by rfl

set_option maxRecDepth 100000 in
theorem reset_zeuge :
    let body := SAnw.block [.reset "A" (some (.lit 1, .lit 2))] (some (.ret (some (.lit 23))))
    let sig : FnSig := ⟨"impl", "main", [], some (.atom "u64"), none, [], []⟩
    check [.fnT sig body] = .ok () ∧ check [.fnT ⟨"impl", "main", [], some (.atom "u64"), none, [.cost (.lit 0)], []⟩ body] = .error "source export: declared costs lack a checked source-to-kostenPasst binding: main" := by
  exact ⟨rfl, rfl⟩

/-- C05 group and table invariants stay refused: every invariant carries mandatory cost, runs and by duties (`SGruppenInv.kosten/online/proof`), but the exporter only reads the predicate over the declared carriers (`uInv`), ignoring all three. No other checked binding exists, so admitting any shape would silently drop them. -/
theorem groupT_still_refused (g : String) (ts : List String) (vs : List SGruppenInv) : itemMetadata (.groupT g ts vs) = true := by rfl

set_option maxRecDepth 100000 in
theorem groupT_zeuge :
    check [.groupT "G" ["T"] [⟨"valid", .lit 1, true, none, .ext .imp [] [.tru, .tru]⟩]] = .error "source export: invariant cost/runs/by duties lack a checked source binding" ∧ check [.tableT "T" none (some (.lit 1)) none none false [.tInv ⟨"valid", .lit 1, true, none, .ext .imp [] [.tru, .tru]⟩]] = .error "source export: invariant cost/runs/by duties lack a checked source binding" := by
  exact ⟨rfl, rfl⟩

/-- C12 supports named table spaces;
    owner rights require C09 flow, live bytes require C01/C08/C09, and entry
    handles require C08/C14 binding plus C09 forwarding. Do not erase these
    duties merely because table capability descriptors exist in the model. -/
theorem capability_unbound_zeuge :
    typeMetadata (.ptr "guest" "own@holder" (.atom "T")) = true ∧
    typeMetadata (.entry "main" none) = true := by
  exact ⟨rfl, rfl⟩
/-- Required allocation is admitted at the gate: the binder is a plain index
    (mutable and type-annotated bindings elaborate to no G form) and the value
    is an ordinary body expression. The elaborator lowers it through
    `UStmt.allocReqBeg` to `Block.arenaAllocRequired`, whose full-arena outcome
    is `Logik.kapazitaet` under the caller's `KoerperGutS/SA` duty; Stage 0
    lowers that like `narrowRequired` (success path plus `stopC 107`). -/
theorem allocRequired_bound (x an : String) (v : SExpr) (n : Nat) :
    bodyMetadata (n + 1) (.alloc false x none an v none) = false := by rfl

/-- Explicit failure branches retain their complete metadata check. The canonical
    exporter still checks the arena, element value, effects and ending branch;
    this gate only admits the immutable, unannotated binder it can lower. -/
theorem allocElse_bound (x an : String) (v : SExpr) (body : SAnw) (n : Nat) :
    bodyMetadata (n + 1) (.alloc false x none an v (some body)) =
      bodyMetadata n body := by rfl

theorem allocRequired_zeuge :
    bodyMetadata 1 (.alloc false "i" none "A" (.lit 0) none) = false ∧
    bodyMetadata 2 (.alloc false "i" none "A" (.lit 0) (some (.block [] none))) = false ∧
    bodyMetadata 1 (.alloc true "i" none "A" (.lit 0) none) = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Static arena declarations are admitted at the gate exactly in their
    elaborated shape: anything dynamic, placed, non-literal or provider-bound
    stays refused. -/
theorem arenaT_bound (n : String) (lo hi : Nat) (ty : STyp) :
    itemMetadata (.arenaT n (.lit lo) (.lit hi) none ty none) = typeMetadata ty := by rfl

theorem arenaT_zeuge :
    itemMetadata (.arenaT "A" (.lit 1) (.lit 2) none (.atom "u32") none) = false ∧
    itemMetadata (.arenaT "A" (.lit 1) (.lit 2) (some (.lit 8)) (.atom "u32") none) = true ∧
    itemMetadata (.arenaT "A" (.lit 1) (.lit 2) none (.atom "u32") (some (["P"], (.lit 1)))) = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Ghost owner values still lack a checked source binding. Nominal marks
    travel only as resources; mint effects retain their metadata refusal
    until their C08 software-call and root-once admission are connected. -/
theorem owner_mint_type_refused_zeuge :
    itemMetadata (.typeT ["linear", "ghost"] "Mark" [] [] none) = true := by rfl

end Gabbro.Grammatik.Parser.ExportMetadata


namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- C17 retains the exact source tree. Unit alias checks, duplicate-clause refusal and
    certified measure lowering remain mandatory in `uMeasureClause` and Stage 0. -/
theorem drops_bound (e : SExpr)
    (h : (Gabbro.Grammatik.Parser.Uebersetze.uMeasureSource e).toOption.isNone = false) :
    clausesMetadata [.drops e] = false := by
  simp [clausesMetadata, h]

theorem drops_zeuge :
    clausesMetadata [.drops (.variable "n")] = false ∧
    clausesMetadata [.drops (.old (.variable "n"))] = true := by
  exact ⟨rfl, rfl⟩

/-- A consuming header is bound only through the same complete parser used by uLoopExport;
    metadata in every nested continuation is still checked. -/
theorem consuming_bound (fuel : Nat) (binder kind raw touches : String) (origin : Option SExpr)
    (subject measure : SExpr) (invariant : Option SExpr) (body : SAnw)
    (parsed : consumingHeader raw = .ok (measure, touches)) :
    bodyMetadata (fuel + 1) (.each binder origin kind subject "consuming" raw invariant body) =
      bodyMetadata fuel body := by
  simp only [bodyMetadata, BEq.rfl, ↓reduceIte, parsed, Except.toOption,
    Option.isNone_some, Bool.false_or]

theorem consuming_bound_zeuge :
    bodyMetadata 3 (.each "k" none "slots" (.variable "T") "consuming"
      "decreases 1 touches consumes T.slots" none (.block [] none)) = false ∧
    bodyMetadata 3 (.each "k" none "slots" (.variable "T") "consuming"
      "touches consumes T.slots" none (.block [] none)) = true := by
  exact ⟨rfl, rfl⟩
/-- C14 gates are consumed only by canonical build selection, before metadata checking.
    Raw wrappers remain refused; selection never suppresses the retained item's duties. -/
theorem gateT_bound (m : Auswahl.BauModus) (items selected : List SItemTief)
    (selection : selected = Auswahl.waehleL m items)
    (clear : selected.any itemMetadata = false) :
    check (Auswahl.waehleL m items) = .ok () := by
  rw [← selection]
  exact check_clear selected clear

theorem gateT_zeuge :
    check [.gateT (.constT "sample" (.atom "u8") (.one (.lit 1)))] =
      .error "source export: type/provider/proof duties lack a checked source binding" ∧
    check (Auswahl.waehleL .auslieferung
      [.gateT (.constT "sample" (.atom "u8") (.one (.lit 1)))]) = .ok () ∧
    check (Auswahl.waehleL .pruefbau
      [.gateT (.constT "sample" (.atom "u8") (.one (.lit 1)))]) = .ok () ∧
    check (Auswahl.waehleL .pruefbau [.gateT (.groupT "G" [] [])]) =
      .error "source export: invariant cost/runs/by duties lack a checked source binding" := by
  exact ⟨rfl, rfl, rfl, rfl⟩
/-- Named table spaces are registered by the unit elaborator; providers and placement remain gated. -/
theorem tableSpace_bound (name space : String) (count : Option SExpr) (shared : Bool) :
    itemMetadata (.tableT name none count none (some space) shared []) = false := by rfl

theorem tableSpace_zeuge :
    check [.tableT "T" none (some (.lit 2)) none (some "Data") false []] = .ok () ∧
    itemMetadata (.tableT "T" (some "provider") (some (.lit 2)) none (some "Data") false []) = true ∧
    itemMetadata (.tableT "T" none (some (.lit 2)) (some "place") (some "Data") false []) = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem namedPointer_bound (space target : String) :
    typeMetadata (.ptr space "r" (.atom target)) = (target == "u8") := by
  have hd : (match Gabbro.Grammatik.DataRights.decode (fun _ => none) "r" with
      | some r => r.owner.isSome
      | none => true) = false := rfl
  show ((match Gabbro.Grammatik.DataRights.decode (fun _ => none) "r" with
      | some r => r.owner.isSome
      | none => true) || target == "u8") = (target == "u8")
  rw [hd, Bool.false_or]

theorem namedPointer_zeuge :
    typeMetadata (.ptr "sharedData" "r" (.atom "T")) = false ∧
    typeMetadata (.ptr "sharedData" "x" (.atom "T")) = true ∧
    typeMetadata (.ptr "sharedData" "rw" (.atom "u8")) = true ∧
    typeMetadata (.ptr "sharedData" "r" (.raw "T")) = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩
/-- A nonempty reset range carries no unbound metadata. -/
theorem reset_bound_zeuge :
    bodyMetadata 3 (.reset "A" (some (.lit 1, .lit 2))) = false :=
  reset_bound 2 "A" (some (.lit 1, .lit 2))

/-- Mint output admission still needs the root-once and software-call bridge. -/
theorem mint_effect_metadata_refused :
    clausesMetadata [.effs [.mints "Mark"]] = true ∧
    clausesMetadataWithoutLoad [.effs [.mints "Mark"]] = true := by
  exact ⟨rfl, rfl⟩

/-- Plain marks carry no erased body or proof metadata; ghost value types still refuse. -/
theorem linear_mark_metadata_zeuge :
    itemMetadata (.typeT ["linear"] "Mark" [] [] none) = false ∧
    bodyMetadata 1 (.retires "Mark") = false := by
  exact ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.ExportMetadata
