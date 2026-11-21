module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Follow projections to the local aggregate being assigned. The reserved
    slot subscript stays with the guarded place exporter. -/
def uRecordLocal (ctx : UCtx) : SExpr → Option String
  | .variable name => do
    let position ← ctx.names.findIdx? (strEq · name)
    match ctx.types[position]? with
    | some (.prod ..) => some name
    | some (.arr ..) => if ctx.muts.any (strEq · name) then some name else none
    | _ => none
  | .index (.field (.variable _) "slots") _ => none
  | .field base _ | .index base _ => uRecordLocal ctx base
  | _ => none

/-- Rebuild the containing value from the selected leaf outwards. Typed lowering
    resolves each field and checks each array index before constructing the update. -/
def uRecordReplacement (ctx : UCtx) (root : SExpr → Bool) :
    SExpr → USide → Except String (SExpr × USide)
  | path, value =>
    if root path then .ok (path, value)
    else match path with
    | .field base field => do
      let original ← uWertBody ctx base
      uRecordReplacement ctx root base (.replace original field value)
    | .index base index => do
      let original ← uWertBody ctx base
      let offset ← uWertBody ctx index
      uRecordReplacement ctx root base (.upd original offset value)
    | _ => .error "source export: record update requires a field or element path"

theorem uRecordReplacement_root (ctx : UCtx) (root : SExpr → Bool)
    (place : SExpr) (value : USide) (found : root place = true) :
    uRecordReplacement ctx root place value = .ok (place, value) := by
  rw [uRecordReplacement.eq_def]
  dsimp only
  split
  · rfl
  · next denied => exact False.elim (denied found)

/-- Each selected field is replaced in the value read from its parent. -/
theorem uRecordReplacement_step (ctx : UCtx) (root : SExpr → Bool) (base : SExpr)
    (field : String) (original value : USide)
    (nested : root (.field base field) = false)
    (read : uWertBody ctx base = .ok original) :
    uRecordReplacement ctx root (.field base field) value =
      uRecordReplacement ctx root base (.replace original field value) := by
  simp only [uRecordReplacement, nested, Bool.false_eq_true, ↓reduceIte,
    read, bind, Except.bind]

/-- A subscript below the store root rebuilds the array at the ordinary checked index. -/
theorem uRecordReplacement_index (ctx : UCtx) (root : SExpr → Bool) (base index : SExpr)
    (original offset value : USide)
    (nested : root (.index base index) = false)
    (read : uWertBody ctx base = .ok original)
    (readIndex : uWertBody ctx index = .ok offset) :
    uRecordReplacement ctx root (.index base index) value =
      uRecordReplacement ctx root base (.upd original offset value) := by
  simp only [uRecordReplacement, nested, Bool.false_eq_true, ↓reduceIte,
    read, readIndex, bind, Except.bind]

/-- Store the rebuilt aggregate in the mutable local at the root of the place. -/
def uSetzeAggregateLocal (ctx : UCtx) (name : String) (target value : SExpr) : Except String UStmt := do
  if !ctx.muts.any (strEq · name) then throw "source export: aggregate update requires a mutable local"
  let side ← uRecordSide ctx value (fun source _ => uWertBody ctx source)
  let (_, rebuilt) ← uRecordReplacement ctx (fun
    | .variable _ => true
    | _ => false) target side
  pure (.setVar name rebuilt)

/-- A complete field of a table slot, before any record projection. -/
def uRecordSlotRoot : SExpr → Bool
  | .field (.index (.field (.variable _) "slots") _) _ => true
  | _ => false

def uRecordSlotPath : SExpr → Bool
  | target@(.field base _) => uRecordSlotRoot target || uRecordSlotPath base
  | .index (.field (.variable _) "slots") _ => false
  | .index base _ => uRecordSlotPath base
  | _ => false

/-- Both whole-slot and nested stores need the ordinary write capability. -/
def uSlotWriteRight (ctx : UCtx) (name : String) : Except String Unit := do
  let position ← uStelle ctx.names name
  match uArtBei ctx.kinds position with
  | .ok (.ptr ⟨0, ⟨_, true, _⟩, .table _⟩) => pure ()
  | _ => throw "write through a read pointer"

/-- A nested update is one ordinary store of the rebuilt aggregate. The
    base read and the store both pass the typed slot checks. -/
def uSetzeRecordSlot (ctx : UCtx) (target value : SExpr) : Except String UStmt := do
  let value ← uRecordSide ctx value (fun source _ => uWertBody ctx source)
  let (place, rebuilt) ← uRecordReplacement ctx uRecordSlotRoot target value
  match ← uZugriff ctx place with
  | (.tabelle name, _, field, index) => pure (.assignTab name field index rebuilt)
  | (.thru name, _, field, index) => do
    uSlotWriteRight ctx name
    pure (.assign name field index rebuilt)

/-- At a named slot, a single nested field update emits the ordinary
    aggregate store with exactly the model's record replacement. -/
theorem uSetzeRecordSlot_named (ctx : UCtx) (place value : SExpr)
    (selected table column : String) (index : UIdx) (original replacement : USide)
    (root : uRecordSlotRoot place = true)
    (nested : uRecordSlotRoot (.field place selected) = false)
    (access : uZugriff ctx place = .ok (.tabelle table, table, column, index))
    (read : uWertBody ctx place = .ok original)
    (readValue : uRecordSide ctx value (fun source _ => uWertBody ctx source) = .ok replacement) :
    uSetzeRecordSlot ctx (.field place selected) value =
      .ok (.assignTab table column index (.replace original selected replacement)) := by
  simp only [uSetzeRecordSlot, readValue, bind, Except.bind,
    uRecordReplacement_step ctx uRecordSlotRoot place selected original replacement nested read,
    uRecordReplacement_root ctx uRecordSlotRoot place _ root, access, pure, Except.pure]

/-- An element of a named slot field becomes a checked array replacement in the ordinary store. -/
theorem uSetzeRecordSlot_index (ctx : UCtx) (place index value : SExpr)
    (table column : String) (slot : UIdx) (original offset replacement : USide)
    (root : uRecordSlotRoot place = true)
    (access : uZugriff ctx place = .ok (.tabelle table, table, column, slot))
    (read : uWertBody ctx place = .ok original)
    (readIndex : uWertBody ctx index = .ok offset)
    (readValue : uRecordSide ctx value (fun source _ => uWertBody ctx source) = .ok replacement) :
    uSetzeRecordSlot ctx (.index place index) value =
      .ok (.assignTab table column slot (.upd original offset replacement)) := by
  simp only [uSetzeRecordSlot, readValue, bind, Except.bind,
    uRecordReplacement_index ctx uRecordSlotRoot place index original offset replacement
      rfl read readIndex,
    uRecordReplacement_root ctx uRecordSlotRoot place _ root, access, pure, Except.pure]

end Gabbro.Grammatik.Parser.Uebersetze
