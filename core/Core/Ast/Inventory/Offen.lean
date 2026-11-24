module

public import Core.Ast.Inventory.All

/-
  Open forms of the source inventory. Generated from the five inventory modules;
  a form is open when no constructor of `core/` realises it. Grammar nonterminals
  (`syntax.*`) are productions, not language forms, and are not listed here.

  Method: every inventory entry is compared with the constructors of
  `Core.Ast.Tree` (Expr, Stmt, Decl, WrittenType), `Core.Ast.Ty`, and the
  `Core.Ast.LowLevel` trees (Tree, MemTree, ExecTree, DeviceSyntax). Entries are
  grouped by what blocks them:

  * `sofort`   - a constructor of an existing inductive can be added now;
  * `substrat`  - table/pointer access (`&T`, `p->f`, `p[i]`, table slots): waits for
                 the table substrate of the other agent, do not create here;
  * `pegel`    - `secret`/`public`/`release` levels: waits for the owner;
  * `entwurf`  - async/await/join/Executor, probability (M9P), persistence (M9),
                 predicates, contracts and declaration families: waits for a design.

  Counts over the 546 inventory entries: 84 covered, 205 productions, 257 open
  (117 sofort, 9 substrat, 1 pegel, 130 entwurf). The five L4 forms marked
  `skeleton` below have rejected constructors in `Core.Ast.LowLevel.Exec.Syntax`.
  No form here has a grammar or parser production in `grammatik/`; enabling a
  form adds its spelling, meaning and duties in separate modules.
-/

@[expose] public section

namespace Gabbro.Core.Inventory

/-- Why a form is still open. -/
inductive OffenKategorie where
  | sofort | substrat | pegel | entwurf

/-- An inventory key with the inductive it belongs to and its blocker. -/
structure OffeneForm where
  key : String
  name : String
  ziel : String
  kategorie : OffenKategorie
  grund : String

/-- 117 entries. -/
def offenSofort : List OffeneForm :=
  [
    ⟨"surface.SExpr.float", "Float", "Expr", .sofort, "A floating-point literal, retaining its spelling."⟩,
    ⟨"surface.SExpr.call", "Call", "Expr", .sofort, "A call to a named function, constructor or builtin with ordered arguments."⟩,
    ⟨"surface.SExpr.built", "Built", "Expr", .sofort, "A built-in operation selected by its source head."⟩,
    ⟨"surface.SExpr.old", "Old", "Expr", .sofort, "Refer to an expression's value at entry to a contract."⟩,
    ⟨"surface.SExpr.res", "Res", "Expr", .sofort, "Refer to the result bound by a postcondition."⟩,
    ⟨"surface.SExpr.ext", "Ext", "Expr", .sofort, "Extended forms, including ordered arrays (layout at `XKind`). The token printer spells them separate"⟩,
    ⟨"surface.STyp.wrap", "Wrap", "WrittenType / Ty", .sofort, "A wrapping integer representation."⟩,
    ⟨"surface.STyp.embed", "Embed", "WrittenType / Ty", .sofort, "A type embedded at a named bit range, with optional scaling."⟩,
    ⟨"surface.STyp.raw", "Raw", "WrittenType / Ty", .sofort, "A balanced spelling of a structural or function-pointer type to be interpreted by the type elaborato"⟩,
    ⟨"surface.STyp.entry", "Entry", "WrittenType / Ty", .sofort, "`entry fn(params) [-> T]` (`entryfn`): the parameter words raw, the result type read."⟩,
    ⟨"surface.STyp.dyn", "Dyn", "WrittenType / Ty", .sofort, "Link-time closed spec sum; effect tokens are interpreted after group resolution."⟩,
    ⟨"surface.SEnde.leave", "Leave", "Stmt", .sofort, "Leave the labelled enclosing traversal."⟩,
    ⟨"surface.SEnde.next", "Next", "Stmt", .sofort, "Continue at the labelled enclosing traversal."⟩,
    ⟨"surface.SAnw.bindElse", "BindElse", "Stmt", .sofort, "Bind a fallible expression on success or run its reason handler."⟩,
    ⟨"surface.SAnw.bindLib", "BindLib", "Stmt", .sofort, "Bind the result of a library translator call."⟩,
    ⟨"surface.SAnw.shift", "Shift", "Stmt", .sofort, "Transition a place from a named state to another named state."⟩,
    ⟨"surface.SAnw.lcall", "Lcall", "Stmt", .sofort, "Call a library translator in statement position."⟩,
    ⟨"surface.SAnw.elsif", "Elsif", "Stmt", .sofort, "One ordered else-if arm of a conditional."⟩,
    ⟨"surface.SAnw.each", "Each", "Stmt", .sofort, "`traverse b [of e] over KIND of S by MODE [decreases …] [touches …] [invariant p] { … }`: binder, `o"⟩,
    ⟨"surface.SAnw.loop", "Loop", "Stmt", .sofort, "A forever loop with its written header and body."⟩,
    ⟨"surface.SAnw.waive", "Waive", "Stmt", .sofort, "An assertion-check block with a list of named checks."⟩,
    ⟨"surface.SAnw.trim", "Trim", "Stmt", .sofort, "Narrow a value with an explicit failure body."⟩,
    ⟨"surface.SAnw.locks", "Locks", "Stmt", .sofort, "Execute a block holding the written lock, optionally shared."⟩,
    ⟨"surface.SAnw.watch", "Watch", "Stmt", .sofort, "Execute an observes block over a named group."⟩,
    ⟨"surface.SAnw.leave", "Leave", "Stmt", .sofort, "Leave the indicated traversal."⟩,
    ⟨"surface.SAnw.next", "Next", "Stmt", .sofort, "Continue the indicated traversal."⟩,
    ⟨"surface.SAnw.await", "Await", "Stmt", .sofort, "Bind the value acquired from an atomic, with its payload."⟩,
    ⟨"surface.SAnw.swap", "Swap", "Stmt", .sofort, "Bind the result of an atomic exchange or a guarded update."⟩,
    ⟨"surface.SAnw.step", "Step", "Stmt", .sofort, "Advance a named progress stage to its successor."⟩,
    ⟨"surface.SAnw.alloc", "Alloc", "Stmt", .sofort, "Allocate in an arena with an optional failure block."⟩,
    ⟨"surface.SAnw.reset", "Reset", "Stmt", .sofort, "`reset A [at i count n];`"⟩,
    ⟨"surface.SAnw.grow", "Grow", "Stmt", .sofort, "`grow A by e else { … };`"⟩,
    ⟨"surface.SAnw.free", "Free", "Stmt", .sofort, "`free A[i];`"⟩,
    ⟨"surface.SAnw.child", "Child", "Stmt", .sofort, "`child { … }`"⟩,
    ⟨"surface.SAnw.start", "Start", "Stmt", .sofort, "`start { f, g };`"⟩,
    ⟨"surface.SAnw.bindQ", "BindQ", "Stmt", .sofort, "`let [mut] x [: T] = f(args) ?;` -- the reason propagation of §4.3: the call must carry a reason cha"⟩,
    ⟨"surface.SAnw.callQ", "CallQ", "Stmt", .sofort, "`f(args) ?;` -- `?` in statement position: the call's value is discarded, its reason re-raised."⟩,
    ⟨"surface.SAnw.callElse", "CallElse", "Stmt", .sofort, "Fallible foreign statement call; an empty reason name discards the reason."⟩,
    ⟨"surface.SAnw.retires", "Retires", "Stmt", .sofort, "`retires m;`: consume the held linear mark, without a runtime value."⟩,
    ⟨"surface.SAnw.callIndElse", "CallIndElse", "Stmt", .sofort, "Fallible statement call through a parenthesized function-pointer expression."⟩,
    ⟨"surface.SEffekt.reads", "Reads", "CarrierEffect", .sofort, "Read the indicated place."⟩,
    ⟨"surface.SEffekt.writes", "Writes", "CarrierEffect", .sofort, "Write the indicated place."⟩,
    ⟨"surface.SEffekt.locks", "Locks", "CarrierEffect", .sofort, "Acquire the indicated lock, optionally in shared mode."⟩,
    ⟨"surface.SEffekt.masks", "Masks", "CarrierEffect", .sofort, "Run with the indicated interrupt mask."⟩,
    ⟨"surface.SEffekt.allocs", "Allocs", "CarrierEffect", .sofort, "Allocate in the indicated region."⟩,
    ⟨"surface.SEffekt.takes", "Takes", "CarrierEffect", .sofort, "Acquire authority from the indicated place."⟩,
    ⟨"surface.SEffekt.posts", "Posts", "CarrierEffect", .sofort, "Publish a value at the indicated place."⟩,
    ⟨"surface.SEffekt.loops", "Loops", "CarrierEffect", .sofort, "Declare the ability to loop."⟩,
    ⟨"surface.SEffekt.pure", "Pure", "CarrierEffect", .sofort, "Declare the absence of effects."⟩,
    ⟨"surface.SEffekt.param", "Param", "CarrierEffect", .sofort, "Refer to a named effect parameter or group."⟩,
    ⟨"surface.SEffekt.instanceEffects", "InstanceEffects", "CarrierEffect", .sofort, "Refer to the effects of a named specification instance at concrete types."⟩,
    ⟨"surface.SEffekt.borrows", "Borrows", "CarrierEffect", .sofort, "`borrows m` (C12): a call-scoped loan of the owner mark `m` -- the callee holds it during the call, "⟩,
    ⟨"surface.SEffekt.moves", "Moves", "CarrierEffect", .sofort, "`moves m` (C09): a linear handoff of the owner mark `m` -- the callee receives the same nominal iden"⟩,
    ⟨"surface.SEffekt.mints", "Mints", "CarrierEffect", .sofort, "`mints m` (C09): the checked mint of the owner mark `m` -- the minter holds the fresh owner from its"⟩,
    ⟨"surface.FnSig.mk", "Mk", "Ast", .sofort, "The written function header, arguments, result, reasons, clauses and generic parameters."⟩,
    ⟨"surface.SGerTeil.copy", "Copy", "Decl (device/register)", .sofort, "A declared copy between two device places."⟩,
    ⟨"surface.SGerTeil.reg", "Reg", "Decl (device/register)", .sofort, "A register declaration in the device layout."⟩,
    ⟨"surface.SGerTeil.bank", "Bank", "Decl (device/register)", .sofort, "A register bank with its written range."⟩,
    ⟨"surface.SGerTeil.trans", "Trans", "Decl (device/register)", .sofort, "A transition of the device protocol."⟩,
    ⟨"surface.SWeg.mk", "Mk", "Decl (device/register)", .sofort, "A `walk` declaration: SYNTAX.md section 9 `walkdecl`."⟩,
    ⟨"low.L2.2", "2", "Device / DeviceSyntax", .sofort, "device at a discovery window as a layout"⟩,
    ⟨"low.L2.6", "6", "Device / DeviceSyntax", .sofort, "copy from or to a shared device slot"⟩,
    ⟨"low.L4.7", "7", "ExecTree / ExecForm", .sofort, "cpu.caps and cpu.has"⟩, -- skeleton (rejected)
    ⟨"low.L4.8", "8", "ExecTree / ExecForm", .sofort, "cpu.cycles"⟩, -- skeleton (rejected)
    ⟨"low.L4.9", "9", "ExecTree / ExecForm", .sofort, "suspend system"⟩, -- skeleton (rejected)
    ⟨"low.L4.10", "10", "ExecTree / ExecForm", .sofort, "suspend core"⟩, -- skeleton (rejected)
    ⟨"low.L4.11", "11", "ExecTree / ExecForm", .sofort, "Resume arrival"⟩, -- skeleton (rejected)
    ⟨"low.L5.7", "7", "ExecTree / Device", .sofort, "switch to a thread"⟩,
    ⟨"low.L5.8", "8", "ExecTree / Device", .sofort, "backtrace"⟩,
    ⟨"low.L7.4", "4", "ExecTree / ExecForm", .sofort, "interrupts off"⟩,
    ⟨"low.L7.5", "5", "ExecTree / ExecForm", .sofort, "priority at least"⟩,
    ⟨"low.L7.6", "6", "ExecTree / ExecForm", .sofort, "send interrupt"⟩,
    ⟨"low.L7.7", "7", "ExecTree / ExecForm", .sofort, "route line"⟩,
    ⟨"low.L7.8", "8", "ExecTree / ExecForm", .sofort, "timer.at and timer.after"⟩,
    ⟨"low.L7.9", "9", "ExecTree / ExecForm", .sofort, "watch"⟩,
    ⟨"low.L7.10", "10", "ExecTree / ExecForm", .sofort, "Watchpoint and breakpoint entries"⟩,
    ⟨"low.L7.11", "11", "ExecTree / ExecForm", .sofort, "step a thread, guest or virtual core"⟩,
    ⟨"low.L7.12", "12", "ExecTree / ExecForm", .sofort, "counter.start"⟩,
    ⟨"low.L7.13", "13", "ExecTree / ExecForm", .sofort, "Performance overflow entry"⟩,
    ⟨"low.L8.1", "1", "ExecTree / Device", .sofort, "enter guest"⟩,
    ⟨"low.L8.2", "2", "ExecTree / Device", .sofort, "System-call entry"⟩,
    ⟨"low.L8.3", "3", "ExecTree / Device", .sofort, "copy from guest"⟩,
    ⟨"low.L8.4", "4", "ExecTree / Device", .sofort, "copy to guest"⟩,
    ⟨"low.L8.5", "5", "ExecTree / Device", .sofort, "grant ports"⟩,
    ⟨"low.L8.6", "6", "ExecTree / Device", .sofort, "grant device"⟩,
    ⟨"low.L8.7", "7", "ExecTree / Device", .sofort, "grant cycles"⟩,
    ⟨"low.L8.8", "8", "ExecTree / Device", .sofort, "grant register"⟩,
    ⟨"low.L9.1", "1", "ExecTree / ExecForm", .sofort, "start core with its arrival frame"⟩,
    ⟨"low.L13.1", "1", "Decl / ExecTree", .sofort, "Image declaration"⟩,
    ⟨"low.L13.2", "2", "Decl / ExecTree", .sofort, "place a code item"⟩,
    ⟨"low.L13.3", "3", "Decl / ExecTree", .sofort, "make executable"⟩,
    ⟨"low.L14.1", "1", "Decl / ExecTree", .sofort, "Flag declaration"⟩,
    ⟨"low.L14.2", "2", "Decl / ExecTree", .sofort, "Configuration declaration"⟩,
    ⟨"low.L14.3", "3", "Decl / ExecTree", .sofort, "Compile-time selection of items or statements"⟩,
    ⟨"low.L14.4", "4", "Decl / ExecTree", .sofort, "Compile-time selection of an expression"⟩,
    ⟨"low.L15.1", "1", "ExecTree / Device", .sofort, "space.new_guest"⟩,
    ⟨"low.L15.2", "2", "ExecTree / Device", .sofort, "vm.new with mandatory isolation controls and optional intercepts"⟩,
    ⟨"low.L15.3", "3", "ExecTree / Device", .sofort, "Create a virtual CPU with named registers"⟩,
    ⟨"low.L15.4", "4", "ExecTree / Device", .sofort, "enter vm"⟩,
    ⟨"low.L15.5", "5", "ExecTree / Device", .sofort, "Neutral VM exit value"⟩,
    ⟨"low.L15.6", "6", "ExecTree / Device", .sofort, "inject interrupt"⟩,
    ⟨"low.L15.7", "7", "ExecTree / Device", .sofort, "copy from or to VM memory"⟩,
    ⟨"low.L15.8", "8", "ExecTree / Device", .sofort, "assign device to VM"⟩,
    ⟨"low.L15.9", "9", "ExecTree / Device", .sofort, "Nested hypervisor virtual CPU"⟩,
    ⟨"low.L16.1", "1", "ExecTree / Device", .sofort, "io.space.new"⟩,
    ⟨"low.L16.2", "2", "ExecTree / Device", .sofort, "Discover an isolation group with group_of"⟩,
    ⟨"low.L16.3", "3", "ExecTree / Device", .sofort, "attach group with PASID and ATS policy"⟩,
    ⟨"low.L16.4", "4", "ExecTree / Device", .sofort, "DMA fault entry"⟩,
    ⟨"low.L17.1", "1", "ExecTree / Device", .sofort, "Monitor execution state with worlds"⟩,
    ⟨"low.L17.2", "2", "ExecTree / Device", .sofort, "Monitor call entry"⟩,
    ⟨"low.L17.3", "3", "ExecTree / Device", .sofort, "return to world"⟩,
    ⟨"low.L17.4", "4", "ExecTree / Device", .sofort, "resume world"⟩,
    ⟨"low.L17.5", "5", "ExecTree / Device", .sofort, "protect physical memory for a world"⟩,
    ⟨"low.L17.6", "6", "ExecTree / Device", .sofort, "Provide an environment in the verified image"⟩,
    ⟨"low.L18.1", "1", "ExecTree / ExecForm", .sofort, "wait at least"⟩,
    ⟨"low.L18.2", "2", "ExecTree / ExecForm", .sofort, "wait until"⟩,
    ⟨"low.L18.3", "3", "ExecTree / ExecForm", .sofort, "timed core within a deadline with a late exit"⟩
  ]
/-- 9 entries. -/
def offenSubstrat : List OffeneForm :=
  [
    ⟨"surface.SExpr.arrow", "Arrow", "Expr", .substrat, "Reach a field through a pointer place."⟩,
    ⟨"surface.SExpr.fnref", "Fnref", "Expr", .substrat, "Take a named function or carrier reference with the ampersand form."⟩,
    ⟨"surface.SAnw.allocVon", "AllocVon", "Stmt", .substrat, "`let [mut] x [: T] = alloc T;` -- the call of the provider of the open table `T` (`table T from p`)."⟩,
    ⟨"surface.STabTeil.tConst", "TConst", "Ast", .substrat, "A named typed table constant."⟩,
    ⟨"surface.STabTeil.tSlot", "TSlot", "Ast", .substrat, "The slot layout of the table."⟩,
    ⟨"surface.STabTeil.tInv", "TInv", "Ast", .substrat, "An invariant of the table's slots."⟩,
    ⟨"surface.STabTeil.tOps", "TOps", "Ast", .substrat, "The declared operations of the table."⟩,
    ⟨"surface.STabTeil.tTree", "TTree", "Ast", .substrat, "The parent-child field associations of a tree."⟩,
    ⟨"surface.STabTeil.tBusy", "TBusy", "Ast", .substrat, "The field marking a slot busy."⟩
  ]
/-- 1 entries. -/
def offenPegel : List OffeneForm :=
  [
    ⟨"surface.SAnw.emit", "Emit", "Stmt", .pegel, "Assign an atomic value with a written publication payload."⟩
  ]
/-- 130 entries. -/
def offenEntwurf : List OffeneForm :=
  [
    ⟨"surface.XKind.all", "All", "Predicate (new)", .entwurf, "Universal quantification over the named domain."⟩,
    ⟨"surface.XKind.any", "Any", "Predicate (new)", .entwurf, "Existential quantification over the named domain."⟩,
    ⟨"surface.XKind.count", "Count", "Predicate (new)", .entwurf, "Count domain elements satisfying a predicate."⟩,
    ⟨"surface.XKind.mem", "Mem", "Predicate (new)", .entwurf, "Membership in a finite domain."⟩,
    ⟨"surface.XKind.reach", "Reach", "Predicate (new)", .entwurf, "Reachability through the indicated name of a link field."⟩,
    ⟨"surface.XKind.imp", "Imp", "Predicate (new)", .entwurf, "Implication from the first predicate to the second."⟩,
    ⟨"surface.XKind.text", "Text", "Predicate (new)", .entwurf, "A string literal, with its exact contents."⟩,
    ⟨"surface.XKind.call", "Call", "Predicate (new)", .entwurf, "A call through a place, followed by its argument expressions."⟩,
    ⟨"surface.XKind.label", "Label", "Predicate (new)", .entwurf, "One labelled call argument: `names = [label]`, `subs = [value]`."⟩,
    ⟨"surface.XKind.dyn", "Dyn", "Predicate (new)", .entwurf, "Producer: names = [spec], subs = [payload]."⟩,
    ⟨"surface.XKind.instantiate", "Instantiate", "Predicate (new)", .entwurf, "Explicit instantiation: `names = callee :: argument spellings`, `subs = call arguments`. Argument sp"⟩,
    ⟨"surface.XKind.foldAdd", "FoldAdd", "Predicate (new)", .entwurf, "Folds: binder/domain names; domain operands, filter, value, optional empty value."⟩,
    ⟨"surface.XKind.foldMin", "FoldMin", "Predicate (new)", .entwurf, "A filtered minimum, with an optional result for an empty selection."⟩,
    ⟨"surface.XKind.foldMax", "FoldMax", "Predicate (new)", .entwurf, "A filtered maximum, with an optional result for an empty selection."⟩,
    ⟨"surface.XKind.foldAnd", "FoldAnd", "Predicate (new)", .entwurf, "A filtered conjunction over the named domain."⟩,
    ⟨"surface.XKind.foldOr", "FoldOr", "Predicate (new)", .entwurf, "A filtered disjunction over the named domain."⟩,
    ⟨"surface.XKind.array", "Array", "Predicate (new)", .entwurf, "Ordered array literal elements; names are empty."⟩,
    ⟨"surface.SExpr.why", "Why", "Expr", .entwurf, "A named reason case or an unresolved two-segment path."⟩,
    ⟨"surface.SAnw.genericCall", "GenericCall", "Stmt", .entwurf, "Explicit generic call statement, consumed before ordinary export."⟩,
    ⟨"surface.SKlausel.needs", "Needs", "Ast", .entwurf, "A precondition the caller establishes."⟩,
    ⟨"surface.SKlausel.gives", "Gives", "Ast", .entwurf, "A postcondition on normal return."⟩,
    ⟨"surface.SKlausel.keeps", "Keeps", "Ast", .entwurf, "The named values retained by the function."⟩,
    ⟨"surface.SKlausel.refs", "Refs", "Ast", .entwurf, "The named resources refined by the function."⟩,
    ⟨"surface.SKlausel.cost", "Cost", "Ast", .entwurf, "A bound on the cost of the function."⟩,
    ⟨"surface.SKlausel.drops", "Drops", "Ast", .entwurf, "The decreases expression for recursive calls."⟩,
    ⟨"surface.SKlausel.induc", "Induc", "Ast", .entwurf, "The written induction annotation."⟩,
    ⟨"surface.SKlausel.load", "Load", "Ast", .entwurf, "A list of written load bindings."⟩,
    ⟨"surface.SKlausel.part", "Part", "Ast", .entwurf, "A named placement section."⟩,
    ⟨"surface.SKlausel.arch", "Arch", "Ast", .entwurf, "An architecture constraint."⟩,
    ⟨"surface.SKlausel.moves", "Moves", "Ast", .entwurf, "A move clause for named authority and destination."⟩,
    ⟨"surface.SKlausel.quits", "Quits", "Ast", .entwurf, "The written exit clause."⟩,
    ⟨"surface.SKlausel.limit", "Limit", "Ast", .entwurf, "The written limit clause."⟩,
    ⟨"surface.SKlausel.effs", "Effs", "Ast", .entwurf, "The function's declared effects."⟩,
    ⟨"surface.SGenericParam.type", "Type", "Ast", .entwurf, "A type parameter with its declared specification bounds."⟩,
    ⟨"surface.SGenericParam.constant", "Constant", "Ast", .entwurf, "A compile-time parameter at a written type."⟩,
    ⟨"surface.SGenericParam.function", "Function", "Ast", .entwurf, "A static function parameter with its written type."⟩,
    ⟨"surface.SAdaptParam.alle", "Alle", "Ast", .entwurf, "Forward all source parameters."⟩,
    ⟨"surface.SAdaptParam.ohne", "Ohne", "Ast", .entwurf, "Exclude the named source parameter."⟩,
    ⟨"surface.SAdaptParam.neu", "Neu", "Ast", .entwurf, "Introduce a new parameter with a written type."⟩,
    ⟨"surface.SAdapt.mk", "Mk", "Ast", .entwurf, "The source adapter's target call, result binder, reason arm and prelude."⟩,
    ⟨"surface.SFeld.mk", "Mk", "Ast", .entwurf, "A typed field with its position, association and layout constraints."⟩,
    ⟨"surface.SRegFeld.mk", "Mk", "Decl (device/register)", .entwurf, "One register bit field: SYNTAX.md section 10 `regfeld`."⟩,
    ⟨"surface.SReg.mk", "Mk", "Decl (device/register)", .entwurf, "A typed register with its address, access policy, fields and dependencies."⟩,
    ⟨"surface.STrans.mk", "Mk", "Decl (device/register)", .entwurf, "A state transition with its steps, precondition and effects."⟩,
    ⟨"surface.SGruppenInv.mk", "Mk", "Decl (device/register)", .entwurf, "A named table or group invariant with its predicate."⟩,
    ⟨"surface.SKonstWert.one", "One", "Ast", .entwurf, "A scalar initializer expression."⟩,
    ⟨"surface.SKonstWert.rows", "Rows", "Ast", .entwurf, "A nested list of initializer rows."⟩,
    ⟨"surface.SRegBind.binds", "Binds", "Decl (device/register)", .entwurf, "Bind a source carrier to a named machine register."⟩,
    ⟨"surface.SRegBind.reg", "Reg", "Decl (device/register)", .entwurf, "Name a register without a source binding."⟩,
    ⟨"surface.SBootSchritt.call", "Call", "Ast", .entwurf, "Call a named function with boot arguments."⟩,
    ⟨"surface.SBootSchritt.set", "Set", "Ast", .entwurf, "Set a named boot input to an expression."⟩,
    ⟨"surface.SEingang.mk", "Mk", "Ast", .entwurf, "The complete source entry signature and its dispatch and register binding."⟩,
    ⟨"surface.SCheck.mk", "Mk", "Ast", .entwurf, "A source check and its measurement clauses, refusal block and optional counterprobe."⟩,
    ⟨"surface.SHerkunft.core", "Core", "Ast", .entwurf, "Binding to a function in the verified image."⟩,
    ⟨"surface.SBind.mk", "Mk", "Ast", .entwurf, "A syscall binding with its register, stack, dirty-register and reason specifications."⟩,
    ⟨"surface.SWay.lit", "Lit", "Ast", .entwurf, "An inline gate binding with ABI, architecture and provenance."⟩,
    ⟨"surface.SWay.via", "Via", "Ast", .entwurf, "A gate binding selected through a named variable."⟩,
    ⟨"surface.SSyscall.mk", "Mk", "Ast", .entwurf, "A `syscall` gate: SYNTAX.md section 12.1 `syscalldecl`."⟩,
    ⟨"surface.SItemTief.modT", "ModT", "Decl", .entwurf, "A module path with its nested declarations."⟩,
    ⟨"surface.SItemTief.useT", "UseT", "Decl", .entwurf, "Import a named declaration or module path."⟩,
    ⟨"surface.SItemTief.typeT", "TypeT", "Decl", .entwurf, "Declare a named type with its modifiers, members, order and optional definition."⟩,
    ⟨"surface.SItemTief.globT", "GlobT", "Decl", .entwurf, "Declare a static value with mutability, type, initializer, alignment, section and sharing."⟩,
    ⟨"surface.SItemTief.protoT", "ProtoT", "Decl", .entwurf, "Declare a function signature ending in a semicolon."⟩,
    ⟨"surface.SItemTief.specT", "SpecT", "Decl", .entwurf, "Define a specification predicate using its signature and expression."⟩,
    ⟨"surface.SItemTief.formatT", "FormatT", "Decl", .entwurf, "Declare a data format with alignment, byte order and fields."⟩,
    ⟨"surface.SItemTief.arenaT", "ArenaT", "Decl", .entwurf, "Declare an arena with an extent, capacity, element type and optional backing place."⟩,
    ⟨"surface.SItemTief.whyT", "WhyT", "Decl", .entwurf, "Declare a reason family and its cases."⟩,
    ⟨"surface.SItemTief.stateT", "StateT", "Decl", .entwurf, "Declare the transitions of a carrier state protocol."⟩,
    ⟨"surface.SItemTief.devT", "DevT", "Decl", .entwurf, "Declare a device family with parameters, a space and register parts."⟩,
    ⟨"surface.SItemTief.checkT", "CheckT", "Decl", .entwurf, "Declare a check with its claim, measurements, gates and refusal block."⟩,
    ⟨"surface.SItemTief.atomT", "AtomT", "Decl", .entwurf, "Declare an atomic carrier with its type and optional publication metadata."⟩,
    ⟨"surface.SItemTief.lockT", "LockT", "Decl", .entwurf, "Declare a lock with parameters, rank, sharing and guard metadata."⟩,
    ⟨"surface.SItemTief.rcuT", "RcuT", "Decl", .entwurf, "Declare a read-copy-update family with optional bound."⟩,
    ⟨"surface.SItemTief.groupT", "GroupT", "Decl", .entwurf, "Group named carriers with invariants."⟩,
    ⟨"surface.SItemTief.concT", "ConcT", "Decl", .entwurf, "`concurrent { m::f, m::g(a, b) }`: each start's path and its arguments (none: a function without par"⟩,
    ⟨"surface.SItemTief.accT", "AccT", "Decl", .entwurf, "Declare a per-core accumulator with its operator and storage bounds."⟩,
    ⟨"surface.SItemTief.walkT", "WalkT", "Decl", .entwurf, "Declare a table walk with its descriptor, leaf predicate and invariants."⟩,
    ⟨"surface.SItemTief.entryT", "EntryT", "Decl", .entwurf, "Declare an entry with its architecture binding and dispatch list."⟩,
    ⟨"surface.SItemTief.bootT", "BootT", "Decl", .entwurf, "Declare a boot sequence with its architecture, steps and retained resources."⟩,
    ⟨"surface.SItemTief.callT", "CallT", "Decl", .entwurf, "Declare a syscall gate with its signature, ABI binding and clauses."⟩,
    ⟨"surface.SItemTief.varT", "VarT", "Decl", .entwurf, "`syscall V;`: a system call as a named variable (SYNTAX.md 12.3)."⟩,
    ⟨"surface.SItemTief.goalT", "GoalT", "Decl", .entwurf, "`target T;` (the selection) or `target T abi A arch X { V = … }` (the bindings)."⟩,
    ⟨"surface.SItemTief.transT", "TransT", "Decl", .entwurf, "Define a library translator with its signature and body."⟩,
    ⟨"surface.SItemTief.gateT", "GateT", "Decl", .entwurf, "Enable a nested item only in a test build."⟩,
    ⟨"surface.SItemTief.pubT", "PubT", "Decl", .entwurf, "`pub item`: the item crosses the boundary of its project (its name is visible to a dependent project"⟩,
    ⟨"surface.SItemTief.adaptT", "AdaptT", "Decl", .entwurf, "An adapter `fn g(adaptparams) [-> T] [or R] from f [=> a [else (e) block]] clauses [prelude] body` ("⟩,
    ⟨"surface.SItemTief.specGroupT", "SpecGroupT", "Decl", .entwurf, "Check model A: type and effect parameters, followed by abstract function heads."⟩,
    ⟨"surface.SItemTief.implGroupT", "ImplGroupT", "Decl", .entwurf, "A concrete type tuple, effect arguments and ordinary implementation functions."⟩,
    ⟨"surface.SItemTief.moduleTemplateT", "ModuleTemplateT", "Decl", .entwurf, "A parametric module template; instantiated before ordinary name resolution."⟩,
    ⟨"surface.SItemTief.moduleUseT", "ModuleUseT", "Decl", .entwurf, "A generative module application: each written alias owns fresh declarations."⟩,
    ⟨"surface.SLibraryCall.mk", "Mk", "Ast", .entwurf, "The written library and function paths, ordinary arguments and balanced region tokens."⟩,
    ⟨"surface.SBoundedHeader.whileLoop", "WhileLoop", "Ast", .entwurf, "A while condition, operation bound and exceeded-handler path."⟩,
    ⟨"surface.SBoundedHeader.forRange", "ForRange", "Ast", .entwurf, "A loop binder, lower and exclusive upper bound, and optional label."⟩,
    ⟨"surface.SFunctionArgument.path", "Path", "Ast", .entwurf, "Refer to an existing static function by path."⟩,
    ⟨"surface.SFunctionArgument.literal", "Literal", "Ast", .entwurf, "Supply a capture-free function literal with its full signature and body."⟩,
    ⟨"further.async.function", "Function", "Stmt / Decl (executor)", .entwurf, "An async function with its ordinary contract and explicit suspension points"⟩,
    ⟨"further.async.await", "Await", "Stmt / Decl (executor)", .entwurf, "Await a child call or a stored future"⟩,
    ⟨"further.async.join", "Join", "Stmt / Decl (executor)", .entwurf, "Join futures, including heterogeneous child results"⟩,
    ⟨"further.async.select", "Select", "Stmt / Decl (executor)", .entwurf, "Select a ready future and cancel the losers"⟩,
    ⟨"further.async.cancel", "Cancel", "Stmt / Decl (executor)", .entwurf, "Cancel explicitly and release the saved state under its contract"⟩,
    ⟨"further.async.spawn", "Spawn", "Stmt / Decl (executor)", .entwurf, "Spawn a task by transferring ownership of a future"⟩,
    ⟨"further.async.blockOn", "BlockOn", "Stmt / Decl (executor)", .entwurf, "Run a future to completion through the executor"⟩,
    ⟨"further.async.executor", "Executor", "Stmt / Decl (executor)", .entwurf, "Task queues, worker threads, wakeups, timers and readiness bindings"⟩,
    ⟨"further.internal.index", "Index", "Stmt", .entwurf, "Statically checked internal index, slot, length and range access"⟩,
    ⟨"further.internal.boundary", "Boundary", "Stmt", .entwurf, "Validate an outside value before putting it into internal state"⟩,
    ⟨"further.internal.narrow", "Narrow", "Stmt", .entwurf, "Explicit failure path for validation or capacity exhaustion"⟩,
    ⟨"further.internal.exit", "Exit", "Stmt", .entwurf, "Maintain representation guarantees on success, reason and publishing exits"⟩,
    ⟨"further.region.scope", "Scope", "Stmt", .entwurf, "Declare a region whose authority ends at the enclosing block"⟩,
    ⟨"further.region.allocate", "Allocate", "Stmt", .entwurf, "Allocate in a scope region with a declared capacity and failure channel"⟩,
    ⟨"further.region.exit", "Exit", "Stmt", .entwurf, "Release the region on normal, loop, return and reason exits"⟩,
    ⟨"further.payload.publish", "Publish", "Stmt / Decl", .entwurf, "Publish a plain payload through an atomic release"⟩,
    ⟨"further.payload.await", "Await", "Stmt / Decl", .entwurf, "Acquire a plain payload through the confirming atomic observation"⟩,
    ⟨"further.writer.invariant", "Invariant", "Stmt / Decl", .entwurf, "Declare an intermediate invariant inside a running writer"⟩,
    ⟨"further.writer.mask", "Mask", "Stmt / Decl", .entwurf, "Exclude handler observation of a writer's broken state by a checked mask"⟩,
    ⟨"further.domain.declaration", "Declaration", "Stmt / Decl", .entwurf, "Declare a guest, process or compartment isolation domain"⟩,
    ⟨"further.domain.channel", "Channel", "Stmt / Decl", .entwurf, "Declare an authority-tracked channel between domains"⟩,
    ⟨"planned.persistence.table", "Table", "Decl / Klausel (new)", .entwurf, "Declare a persistent table"⟩,
    ⟨"planned.persistence.static", "Static", "Decl / Klausel (new)", .entwurf, "Declare a persistent static place"⟩,
    ⟨"planned.persistence.flush", "Flush", "Decl / Klausel (new)", .entwurf, "Flush a persistent place under the selected persistence envelope"⟩,
    ⟨"planned.persistence.fence", "Fence", "Decl / Klausel (new)", .entwurf, "Order durability steps under the selected persistence envelope"⟩,
    ⟨"planned.persistence.invariant", "Invariant", "Decl / Klausel (new)", .entwurf, "State a crash invariant over ghost durable state"⟩,
    ⟨"planned.persistence.cut", "Cut", "Decl / Klausel (new)", .entwurf, "State a persistent-state predicate for interruption at a named point"⟩,
    ⟨"planned.persistence.envelope", "Envelope", "Decl / Klausel (new)", .entwurf, "Select a pinned persistence envelope for the durable medium"⟩,
    ⟨"planned.probability.event", "Event", "Decl / Klausel (new)", .entwurf, "Bound the probability of a run event"⟩,
    ⟨"planned.probability.cost", "Cost", "Decl / Klausel (new)", .entwurf, "Bound expected cost"⟩,
    ⟨"planned.probability.termination", "Termination", "Decl / Klausel (new)", .entwurf, "State almost-sure termination of a randomized loop"⟩,
    ⟨"planned.probability.progress", "Progress", "Decl / Klausel (new)", .entwurf, "State almost-sure progress of a randomized operation"⟩,
    ⟨"planned.probability.informationTheoretic", "InformationTheoretic", "Decl / Klausel (new)", .entwurf, "Bound advantage for every adversary with a given query budget"⟩,
    ⟨"planned.probability.reduction", "Reduction", "Decl / Klausel (new)", .entwurf, "Bound advantage by reduction to a primitive with named hardness"⟩,
    ⟨"planned.probability.draw", "Draw", "Decl / Klausel (new)", .entwurf, "Call a random binding whose draw law comes from a named catalogue row"⟩
  ]
def offen : List OffeneForm := offenSofort ++ offenSubstrat ++ offenPegel ++ offenEntwurf
end Gabbro.Core.Inventory
