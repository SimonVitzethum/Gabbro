module
public import Grammatik.Parser.Item.ElementTief
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

def typeMetadata : STyp → Bool
  | .raw _ | .entry .. | .wrap _ | .embed .. => true
  | .ptr space _ ty => space != "normal" || typeMetadata ty
  | .range ty _ _ _ | .array ty _ => typeMetadata ty
  | _ => false

/-- A conservative unit domain where no cost, scheduling, proof or reservation duty can disappear.
    Invariants are deliberately refused: their mandatory cost/runs/by binding is still absent.
    Local annotations and every nested continuation are inspected as well as function headers. -/
def bodyMetadata : Nat → SAnw → Bool
  | 0, _ => true
  | n + 1, .block ss _ => ss.any (bodyMetadata n)
  | n + 1, .bindElse _ ty _ _ b => ty.any typeMetadata || bodyMetadata n b
  | n + 1, .waive _ b | n + 1, .locks _ _ b | n + 1, .watch _ b |
    n + 1, .trim _ _ b => bodyMetadata n b
  | n + 1, .cond _ a bs b => bodyMetadata n a || bs.any (bodyMetadata n) || b.any (bodyMetadata n)
  | n + 1, .elsif _ b | n + 1, .arm _ _ b => bodyMetadata n b
  | n + 1, .cases _ arms => arms.any (bodyMetadata n)
  | _ + 1, .bind _ _ ty _ => ty.any typeMetadata
  | n + 1, .each _ _ _ _ mode raw _ body => mode != "unvisited" || raw != "" || bodyMetadata n body
  | _ + 1, .retry .. | _ + 1, .loop .. | _ + 1, .swap .. | _ + 1, .await .. |
    _ + 1, .alloc .. | _ + 1, .allocVon .. | _ + 1, .grow .. | _ + 1, .reset .. |
    _ + 1, .free .. | _ + 1, .child .. | _ + 1, .other .. |
    _ + 1, .bindLib .. | _ + 1, .lcall .. => true
  | _ + 1, .set .. | _ + 1, .shift .. | _ + 1, .call .. |
    _ + 1, .leave .. | _ + 1, .next .. | _ + 1, .emit .. | _ + 1, .step .. |
    _ + 1, .ret .. | _ + 1, .start .. => false

def clausesMetadata (clauses : List SKlausel) : Bool := clauses.any fun
  | .cost _ | .limit _ | .induc _ | .load _ | .moves .. | .quits _ | .drops _ | .keeps _ | .part _ | .arch _ | .refs _ => true
  | _ => false

def itemMetadata : SItemTief → Bool
  | .fnT sig body => (sig.art != "" && sig.art != "impl") ||
      clausesMetadata sig.klauseln || bodyMetadata 10000 body ||
      sig.params.any (fun p => typeMetadata p.2) || sig.res.any typeMetadata
  | .specT .. => true -- Typed macro/proof admission is not supplied by predicate inlining alone.
  | .protoT sig => clausesMetadata sig.klauseln || sig.params.any (fun p => typeMetadata p.2) ||
      sig.res.any typeMetadata
  | .tableT _ provider _ place space _ parts => provider.isSome || place.isSome || space.isSome ||
      parts.any fun
        | .tSlot fields => fields.any (fun field => typeMetadata field.ftyp || field.pos.isSome ||
            field.bezug.isSome || field.wo.isSome || field.reserviert || field.byOps)
        | .tTree _ => false
        | _ => true
  | .lockT _ _ _ held reserve mask inv => held.isSome || reserve.isSome || mask.isSome || inv.isSome
  | .groupT .. => true
  | .globT _ _ ty _ bound proof _ => typeMetadata ty || bound.isSome || proof.isSome
  | .typeT ["tagged"] _ [] [] (some (.raw _)) => false
  | .typeT flags _ args order body => !args.isEmpty || !order.isEmpty || body.any typeMetadata ||
      flags.any (fun flag => flag != "pub" && flag != "export")
  | .constT _ ty _ => typeMetadata ty
  | .whyT .. => false
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
  | .fnT sig _ =>
    if sig.klauseln.any (fun | .cost _ => true | _ => false) then
      "declared costs lack a checked source-to-kostenPasst binding: " ++ sig.name
    else "function type/proof/header duties lack a checked source binding: " ++ sig.name
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
      [.gives (.ext .imp [] [.tru, .tru])]⟩
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
    let sig : FnSig := ⟨"impl", "sample", [], some (.atom "u8"), none, [.cost (.lit 0)]⟩
    check [.fnT sig (.child body)] =
      .error "source export: declared costs lack a checked source-to-kostenPasst binding: sample" ∧
    bodyMetadata 10000 (.alloc false "cell" none "A" (.lit 0) (some body)) = true ∧
    bodyMetadata 10000 (.grow "A" (.lit 1) body) = true ∧
    bodyMetadata 10000 (.bind false "value" (some (.wrap (.atom "bool"))) .tru) = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Gabbro.Grammatik.Parser.ExportMetadata
