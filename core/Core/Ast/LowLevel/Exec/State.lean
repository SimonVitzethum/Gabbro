module

public import Core.Ast.LowLevel.Syntax
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine

/-- Operand width of a declared execution state (16, 32 or 64). -/
inductive ExecWidth where
  | w16
  | w32
  | w64
  deriving DecidableEq

def ExecWidth.bits : ExecWidth → Nat
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

/-- Privilege of a declared execution state. Lowering to user privilege is
    never a `jump long`: it is `enter guest` (§4.7, later group). -/
inductive ExecPrivilege where
  | machine
  | hypervisor
  | kernel
  | user
  deriving DecidableEq

/-- Whether translation is active in the state. -/
inductive ExecTranslation where
  | off
  | on
  deriving DecidableEq

/-- Declared guards of a state: no-execute, user-memory access only through
    the guest-copy rule, no execution of user pages. -/
inductive ExecGuard where
  | noExecute
  | userAccessGate
  | noUserExec
  deriving DecidableEq

/-- A declared neutral execution state (§4.1). -/
structure ExecStateDecl where
  widthBits : Nat
  privilege : ExecPrivilege
  translation : ExecTranslation
  guards : List ExecGuard
  deriving DecidableEq

def ExecStateDecl.wellformed (decl : ExecStateDecl) : Prop :=
  (decl.widthBits = 16 ∨ decl.widthBits = 32 ∨ decl.widthBits = 64)

/-- Entry kinds (§4.4). `nonmaskable`, `machineCheck` and `fatal` are not
    blocked by the ordinary interrupt mask; the checker allows only
    lock-free code there, on a declared own stack. -/
inductive EntryKind where
  | interrupt
  | exception
  | nonmaskable
  | machineCheck
  | fatal
  deriving DecidableEq

def EntryKind.needsOwnStack : EntryKind → Bool
  | .nonmaskable => true
  | .machineCheck => true
  | .fatal => true
  | .interrupt => false
  | .exception => false

def EntryKind.needsPriority : EntryKind → Bool
  | .interrupt => true
  | .exception => false
  | .nonmaskable => false
  | .machineCheck => false
  | .fatal => false

/-- Entry stack: shared per-core stack or a declared own stack. -/
inductive EntryStack where
  | perCore
  | own
  deriving DecidableEq

/-- A source scope associates code items with the state they run in, and
    states, spaces and stacks with arrival slots. A slot identifies an
    object in the boundary contract, never an address. -/
structure ExecScope where
  states : List Identifier
  spaces : List Identifier
  stacks : List Identifier
  code : List (Identifier × Identifier)
  entries : List Identifier

def ExecScope.slotState (scope : ExecScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val (scope.states.map Subtype.val)

def ExecScope.slotSpace (scope : ExecScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val (scope.spaces.map Subtype.val)

def ExecScope.slotStack (scope : ExecScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val (scope.stacks.map Subtype.val)

def ExecScope.slotCode (scope : ExecScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val ((scope.code.map Prod.fst).map Subtype.val)

def ExecScope.codeState (scope : ExecScope) (name : Identifier) : Option Nat := do
  let (_, state) ← scope.code.find? (fun p => p.1.val == name.val)
  scope.slotState state

/-- Observable outcome of one execution occurrence. -/
inductive ExecResult where
  | stateDeclared (slot : Nat)
  | jumped (target state : Nat)
  | jumpedLong (target dest : Nat)
  | waited
  | stopped
  | entryDeclared (name : Identifier)

/-- The neutral per-core execution frame: declared states, the current
    state (the first declared state is the arrival state), the active
    space, abstract stack and space capabilities handed by the arrival
    contract, the installed vector entries, and whether the core stopped. -/
structure ExecFrame where
  pc : Nat := 0
  states : List ExecStateDecl := []
  current : Option Nat := none
  activeSpace : Option Nat := none
  halted : Bool := false
  stacks : List Nat := []
  spaces : List Nat := []
  entries : List (Identifier × EntryKind) := []
  result : Option ExecResult := none

abbrev ExecState := Maschine.Zustand PUnit Nat UInt8 PUnit ExecFrame PUnit

end Gabbro.Core.Ast.LowLevel
