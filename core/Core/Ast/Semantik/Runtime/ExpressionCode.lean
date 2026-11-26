module

public import Core.Ast.Semantik.Runtime.Regeln

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- The static maximum counter and, for a range loop, the upper expression's
    static endpoint. Both are indexed by the address of the loop test. -/
structure SchleifenGrenze where
  paesse : Nat
  oben : Option Int

def SchleifenGrenze.whileBounded {lo hi : Int} (_ : Expr scope (.int lo hi)) :
    SchleifenGrenze :=
  ⟨hi.toNat, none⟩

def SchleifenGrenze.forRange {low lowHi highLo high : Int}
    (_ : Expr scope (.int low lowHi)) (_ : Expr scope (.int highLo high)) :
    SchleifenGrenze :=
  ⟨(high - low).toNat, some high⟩

/-- Elaborating a fragment records both its executable instructions and its written clauses.
    Sequencing preserves the order of the instructions and of each kind of clause. -/
structure Fragment where
  code : List Befehl
  klauseln : Quellklauseln Zustand
  eingang : Scope
  /-- The position where the body of a context other than `eintritt` starts. The body of
      `eintritt` is the fragment itself, from its first instruction; its entry here is unused. -/
  eintritte : Kontext → Option Nat
  /-- The memory the fragment declares: its locks, its address spaces and the initial content of the
      cells of its regions. -/
  speicher : Speicherplan
  schleifen : List (Nat × SchleifenGrenze) := []

def Fragment.leer : Fragment := ⟨[], .leer, [], fun _ => none, .leer, []⟩

def Fragment.einzel (b : Befehl) : Fragment := ⟨[b], .leer, [], fun _ => none, .leer, []⟩

/-- Sequencing shifts the entries of the second fragment behind the first one's instructions; the
    first fragment's entry of a context wins. -/
def Fragment.anhaengen (a b : Fragment) : Fragment :=
  ⟨a.code ++ b.code, a.klauseln.anhaengen b.klauseln, a.eingang,
    fun c => (a.eintritte c).or ((b.eintritte c).map (· + a.code.length)), a.speicher.anhaengen b.speicher,
    a.schleifen ++ b.schleifen.map (fun (pc, grenze) => (pc + a.code.length, grenze))⟩

/-- **A body for the contexts selected by `gilt`**: the whole fragment is what each of them runs
    from its first instruction (handlers, NMI handlers and threads started by the program). -/
def Fragment.rumpf (gilt : Kontext → Bool) (body : Fragment) : Fragment :=
  { body with eintritte := fun c => if gilt c then some 0 else body.eintritte c }

mutual

/-- An expression writes its result to the requested temporary. Its right
    operand starts above its left result, which must survive that operand. -/
def expr (slot : Nat) : Expr scope type → Fragment
  | .lit value => .einzel (.literal slot value)
  | .binary op left right =>
    ((expr slot left).anhaengen (expr (slot + 1) right)).anhaengen (.einzel (.binaer op slot))
  | .trueLit => .einzel (.wahrheitswert slot true)
  | .falseLit => .einzel (.wahrheitswert slot false)
  | .variable ref _ _ => .einzel (.lesen slot ref.index)
  | .negativeLit value => .einzel (.negativ slot value)
  | .neg operand => (expr slot operand).anhaengen (.einzel (.negieren slot))
  | .not operand => (expr slot operand).anhaengen (.einzel (.verneinen slot))
  | .div left right _ =>
    ((expr slot left).anhaengen (expr (slot + 1) right)).anhaengen (.einzel (.teilen slot))
  | .compare op left right =>
    ((expr slot left).anhaengen (expr (slot + 1) right)).anhaengen (.einzel (.vergleichen op slot))
  | .logic op left right =>
    let rhs := expr slot right
    ((expr slot left).anhaengen (.einzel (.springeWenn slot op.skips (rhs.code.length + 1)))).anhaengen rhs

  | .arrayValue (types := types) (element := element) items _ _ =>
    (itemCode slot items).anhaengen (.einzel (.baueArray slot element types.length))
  | .arrayIndex (element := element) (count := count) base index _ _ =>
    ((expr slot base).anhaengen (expr (slot + 1) index)).anhaengen
      (.einzel (.liesArray slot element count))
  | .tupleValue (firstType := a) (secondType := b) (types := tail) first second rest =>
    (((expr slot first).anhaengen (expr (slot + 1) second)).anhaengen
      (itemCode (slot + 2) rest)).anhaengen (.einzel (.baueTupel slot (a :: b :: tail)))
  | .tupleField (first := a) (second := b) (types := tail) base index =>
    (expr slot base).anhaengen (.einzel (.liesTupelfeld slot (a :: b :: tail) index))
  | .recordValue (labels := labels) (types := types) ref args fields _ =>
    let sources := List.ofFn fun i : Fin types.length => slot + (fields.slot i).val
    (labeledCode slot args).anhaengen (.einzel (.baueRecord slot ref.name.val labels types sources))
  | .recordField (name := name) (labels := labels) (types := types) base _ index _ =>
    (expr slot base).anhaengen (.einzel (.liesRecordFeld slot name labels types index))
  | .variantValue (labels := labels) (payloads := payloads) ref _ index _ _ _ payload =>
    (caseCode slot payload).anhaengen (.einzel (.baueVariante slot ref.name.val labels payloads index))
  | .textLiteral decoded => .einzel (.textLiteral slot decoded)
  | .textConcat (a := a) (b := b) left right =>
    ((expr slot left).anhaengen (expr (slot + 1) right)).anhaengen (.einzel (.textConcat slot a b))
  | .textIndex (capacity := capacity) base offset =>
    ((expr slot base).anhaengen (expr (slot + 1) offset)).anhaengen (.einzel (.textIndex slot capacity))
  | .substring (capacity := capacity) base first last =>
    (((expr slot base).anhaengen (expr (slot + 1) first)).anhaengen (expr (slot + 2) last)).anhaengen
      (.einzel (.substring slot capacity))
  | .textLength (capacity := capacity) base =>
    (expr slot base).anhaengen (.einzel (.textLength slot capacity))
  | .optionIsSome (count := count) ref _ _ =>
    (Fragment.einzel (.lesen slot ref.index)).anhaengen (.einzel (.optionIstBesetzt slot count))

def itemCode (slot : Nat) : ExprItems scope types → Fragment
  | .empty => .leer
  | .next head tail => (expr slot head).anhaengen (itemCode (slot + 1) tail)

def labeledCode (slot : Nat) : LabeledItems scope labels types → Fragment
  | .empty => .leer
  | .next _ head tail => (expr slot head).anhaengen (labeledCode (slot + 1) tail)

def caseCode (slot : Nat) : CasePayload scope payload → Fragment
  | .nullary _ => .leer
  | .value expression => expr slot expression

end

def argsCode (slot : Nat) : List (TypedExpr scope) → Fragment
  | [] => .leer
  | value :: rest => (expr slot value.2).anhaengen (argsCode (slot + 1) rest)

end Gabbro.Core.Ast.Semantik
