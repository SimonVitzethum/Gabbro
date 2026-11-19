module
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ItemKind
public import Grammatik.Parser.Elab.Export.Traversal.TraversalHeader
public import Grammatik.Kern.Syntax.Typen.DataRights
public import Grammatik.Parser.Elab.Uebersetze.MeasureSource
public import Grammatik.Parser.Profil.Auswahl
public import Grammatik.Parser.Profil.Platzierung
import all Init.Data.String.Basic
import all Init.Data.String.Defs
public import Grammatik.Parser.Elab.Export.MetadataDomain
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- Reader-supported alignment erases no duty: type and section checks remain.
    Actual value/name validity still belongs to profile placement and uGlobs. -/
theorem globT_alignment_bound (constants : List (String × Nat)) (writable : Bool)
    (name : String) (ty : STyp) (initial : SKonstWert) (expression : SExpr)
    (alignment : Nat) (sectionName : Option String) (shared : Bool)
    (read : ProfilBindung.ausrichtungWert constants expression = some alignment) :
    itemMetadata (.globT writable name ty initial (some expression) sectionName shared) =
      (typeMetadata ty || sectionName.isSome) := by
  cases expression <;> simp_all [ProfilBindung.ausrichtungWert, itemMetadata]

def metadataReason : SItemTief → String
  | .tableT _ provider _ _ _ _ _ _ =>
    if provider.isSome then "table provider duties lack a checked source binding"
    else "table field/type/placement duties lack a checked source binding"
  | .lockT _ _ _ held reserve _ inv =>
    if (match held with | none | some (.lit _) => false | some _ => true) || reserve.isSome then
      "held-time/reservation/proof duties lack a checked source binding"
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
    else if sig.klauseln.any (fun k => if sig.art == "library" then (match k with | .cost _ => true | _ => false) else costUnbound k) then
      "declared costs lack a checked source-to-kostenPasst binding: " ++ sig.name
    else "function type/proof/header duties lack a checked source binding: " ++ sig.name
  | .adaptT s _ _ _ => "adapter without expanded form: " ++ s.name
  | item => itemKind item ++ ": type/provider/proof duties lack a checked source binding"

def check (items : List SItemTief) : Except String Unit :=
  if unitMetadata items then
    .error ("source export: " ++ ((items.find? (unitItemMetadata items)).map metadataReason).getD "unsupported metadata")
  else .ok ()

/-- Only the newly evaluable header/initializer positions need the new original-source gate. -/
def constantExpansion : SItemTief → Bool
  | .tableT _ _ (some count) _ _ _ _ _ | .arenaT _ _ count _ _ _ =>
      match count with | .lit _ | .variable _ => false | _ => true
  | .lockT _ _ rank _ _ _ _ => match rank with | .lit _ => false | _ => true
  | .globT _ _ _ (.one expression) _ _ _ =>
      match expression with
      | .lit _ | .un "-" (.lit _) | .variable _ | .tru | .fls | .ext .text _ _ | .call "None" [] => false
      | _ => true
  | _ => false

def checkConstants (items : List SItemTief) : Except String Unit :=
  if items.any constantExpansion then check items else .ok ()

/-- A successful export holds no item the gate refuses. The gate ADMITS declared costs, hold bounds and pass
    bounds; that they hold is not part of this statement but of the compiler's checks (`CostBinding.holds`,
    `CostBinding.unvalued`, `HeldBinding.holds`, `ForeverBinding.holds`, the fields of `Stage0.Compiled`). -/
theorem check_sound (items : List SItemTief) (h : check items = .ok ()) : unitMetadata items = false := by
  unfold check at h
  cases hm : unitMetadata items <;> simp_all

/-- A unit without unsupported duties admits every guarded lowering. -/
theorem check_clear (items : List SItemTief) (h : unitMetadata items = false) :
    check items = .ok () := by simp [check, h]

/-- Every newly evaluable count/rank/initializer preserves the original unit's metadata duties. -/
theorem checkConstants_sound (items : List SItemTief)
    (used : items.any constantExpansion = true) (accepted : checkConstants items = .ok ()) :
    unitMetadata items = false :=
  check_sound items (by simpa only [checkConstants, used, ↓reduceIte] using accepted)

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
/-- C04 state transitions are bound by the exporter and the generic lowering. Every place resolves in the declaration scope (`uTransitionPlace`), every effect becomes an ordinary permission (`uEffekte`, pure/store conflict refused), atomic contracts are refused (`uTransitionAtomicFree`), aliasing needs agreement (`uTransitionDisjoint`), and every generated function is certified (`TransitionExpansion` via `lowerAllg_transition_certified`). A primitive edge keeps the constant `Stmt.shift` rule. -/
theorem stateT_bound (n : String) (ts : List STrans) : itemMetadata (.stateT n ts) = false := by rfl

/-- C02 library calls are bound by the certified expansion. The payload clause is consumed (`exportLibraryKopf` strips `.load`), the call resolves to exactly one library function plus exactly one translator with exactly one payload (`libraryDecl`), and the translator body must be call-free (`callFreeStmt`, otherwise C17). Unexpanded calls never reach ordinary lowering (`ohneBibliothekAnw`, `uAnwReihe`). Costs and other clauses still refuse via `clausesMetadataWithoutLoad`. -/
theorem libraryFn_bound (sig : FnSig) (body : SAnw) (h : sig.art = "library") (c : clausesMetadataWithoutLoad sig.klauseln = false) (b : bodyMetadata 10000 body = false) (p : sig.params.any (fun p => typeMetadata p.2) = false) (r : sig.res.any typeMetadata = false) : itemMetadata (.fnT sig body) = false := by
  simp only [itemMetadata, h, beq_self_eq_true, ↓reduceIte, c, b, p, r, Bool.or_false]

theorem transT_bound (target : String) (translator : FnSig) (body : SAnw) (c : clausesMetadata translator.klauseln = false) (p : translator.params.any (fun p => typeMetadata p.2) = false) (r : translator.res.any typeMetadata = false) : itemMetadata (.transT target translator body) = false := by
  simp only [itemMetadata, c, p, r, Bool.or_false]

/-- C16 declared checks are bound by probe, wrapper and admission. Measures resolve by shape (`uMessOrt`), gates must name unit functions (`uCheck`, unknown gates refused), floors lower with the ordinary predicate reader (`uSichert`), probe bodies elaborate as ordinary Boolean producers (`uProbeFn`, non-block refused), generated names must be fresh (`uProbeNeu`, duplicates refused), wrappers consume exactly one Duty (`uTorHuelle`, parameterised or reason-carrying gates refused, sibling-check gates wait for C14), marks are checked (`uMarkenPruef`), and the checker decides read-only Duty threading with call-graph closure (`checkOkB`/`CheckAdmission`). Counterprobes (`sonde`) stay refused: no binding exists. -/
theorem checkT_bound (c : SCheck) (s : c.sonde = none) (b : bodyMetadata 10000 c.canFail = false) : itemMetadata (.checkT c) = false := by
  simp [itemMetadata, s, b]

/-- C15 accumulators are bound by storage expansion. Admitted operators and per-cpu counts expand to
    private cells plus guarding locks (`uAkkuItem`, `uAkkuErweiterung` with neutral, range and count
    checked by name); uses expand to the generated query, update and reduction (`Akku.Expand`),
    and unsupported positions keep their narrow refusals there.
    Bad operators and missing counts keep the exact downstream refusals. -/
theorem accT_bound (n : String) (t : STyp) (m : String) (p : Option SExpr) (q : Option String) (o : accOperatorBound m = true) (e : p.isSome = true) : itemMetadata (.accT n t m p q) = false := by
  cases p with
  | none => simp at e
  | some _ => simp [itemMetadata, o]

/-- C18 resets are bound by checked range-store expansion. Arena resets elaborate to the used-counter store (`uAnw1`, unknown arenas refused); static-array ranges elaborate operands as body values and travel as `UStmt.resetRange` metadata (`uAnw1`, unknown statics and non-array statics refused), whose range validity and zero observation are discharged by the generic lowering (`lowResetRangeL`, `uReset_lower`). -/
theorem reset_bound (n : Nat) (a : String) (r : Option (SExpr × SExpr)) : bodyMetadata (n + 1) (.reset a r) = false := by rfl

/-- C05 predicates are read by `uInv`; carrier resolution, reads and writer locks remain
    checked there and at lowering. The writer's costs cover the return phase. -/
theorem groupT_bound (g : String) (ts : List String) (vs : List SGruppenInv) :
    itemMetadata (.groupT g ts vs) = false := by rfl

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

/-- Static arena declarations are admitted at the gate exactly in their
    elaborated shape: anything dynamic, placed, non-literal or provider-bound
    stays refused. -/
theorem arenaT_bound (n : String) (lo hi : Nat) (ty : STyp) :
    itemMetadata (.arenaT n (.lit lo) (.lit hi) none ty none) = typeMetadata ty := by rfl

end Gabbro.Grammatik.Parser.ExportMetadata
