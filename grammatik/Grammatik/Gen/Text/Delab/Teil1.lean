/-
  File:      Grammatik/Gen/Text/Delab.lean
  Subject:   DELABORATION: a program of the generator (a member `z : Spez`, its program `P`, its declared starts
             `ws`) as surface items (`List SItemTief`), in the spellings the Lean front end (`elabU`, `lowerAllg`)
             maps back to the model's forms.

  One `module m` with, in order: the tables (`table Ti count n [shared] { slot { fj : T, .. } }`), the statics and
  atomics (`static mut gi : T = v [shared];`, `atomic gi : T [publishes { .. }];`), the locks (`lock Li protects
  { .. } rank r [masks irqs];`), one device `Dev` with the registers (`reg ri : u64 in lo .. hi @i class k
  [requires false] [depends { .. }]`, `mirrors`), the reasons (`reason Rn { C0 = 1 "c0", .. exhaustive }`), one
  `group` per invariant, the functions, `concurrent { .. }` for the declared starts and one `entry .. via idt`
  per function the hardware enters.

  A function: its parameters (`vk`), a device handle `d : Dev` when the unit has registers (the front end erases
  it), its result and reason channel, `requires Held(..)` for the locks its signature holds, its `requires` and
  `ensures` when they are not `true`, `effects { writes .., locks .. }`, and the body. Bodies: `let`, calls,
  `p = &f; p(..)` for an indirect call (the model's pointer expression is bound first), `locks`, `if`,
  assignments, `publishes`, `awaits`, register reads and writes through `d`, `return`.

  Partial: a form without a spelling is an error naming it; the delaborator prints every form it accepts as
  itself, never a substitute (`awaits` needs an atomic static in the model, as in the language).
-/
module
public import Grammatik.Gen.Zeugen.Schluss
public import Grammatik.Parser.Round.RundlaufProgramm
public import Grammatik.Parser.Cover.Mitglieder
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser

/-! ### Names -/

def nTab (i : Nat) : String := s!"T{i}"
def nFeld (j : Nat) : String := s!"f{j}"
def nGlob (i : Nat) : String := s!"g{i}"
def nLock (i : Nat) : String := s!"L{i}"
def nFn (i : Nat) : String := s!"fn{i}"
def nReg (i : Nat) : String := s!"r{i}"
def nVar (k : Nat) : String := s!"v{k}"
def nZeiger (k : Nat) : String := s!"p{k}"
def nGrund (n : Nat) : String := s!"R{n}"
def nFall (j : Nat) : String := s!"C{j}"

/-- The depth of a variable: `here` is 0. -/
def tiefe : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there v => tiefe v + 1

/-- A literal. -/
def zahlE (n : Int) : SExpr := if 0 ≤ n then .lit n.toNat else .un "-" (.lit (-n).toNat)

/-- A type; `otab n` names the table whose count an `option index into T` of count `n` is. -/
def typS (otab : Int → Option Nat) : Ty → Except String STyp
  | .int lo hi => .ok (.range (.atom (if 0 ≤ lo then "u64" else "i64")) (zahlE lo) (zahlE hi) false)
  | .bool => .ok (.atom "bool")
  | .why n => .ok (.atom (nGrund n))
  | .ptr ⟨0, ⟨true, rw, none⟩, .table n⟩ => .ok (.ptr "normal" (if rw then "rw" else "r") (.atom (nTab n)))
  | .ptr ⟨0, ⟨false, true, none⟩, .table n⟩ => .ok (.ptr "normal" "w" (.atom (nTab n)))
  | .ptr _ => .error "capability type without checked source binding"
  | .opt n => match otab n with
    | some i => .ok (.index true (nTab i))
    | none => .error "option of a count no table has"
  | .arr τ n => (typS otab τ).map fun t => .array t (.lit n)
  | _ => .error "type without a spelling"

variable (z : Spez)

/-! ### Expressions -/

/-- An expression; `kopf` is the number of the result variable in an `ensures` (the head of `ErgCtx`, named
    `result`), counted like every variable from the bottom of the context so that a binder below it does not
    move it. -/
def delabE (kopf : Option Nat) {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} :
    Expr z.deklaration Γ Λ τ → Except String SExpr
  | .lit n => .ok (zahlE n)
  | .tru => .ok .tru
  | .fls => .ok .fls
  | .var x => .ok (if kopf = some (Γ.length - 1 - tiefe x) then .res else .variable (nVar (Γ.length - 1 - tiefe x)))
  | .glob g _ => .ok (.variable (nGlob (show Fin z.globs.length from g).val))
  | .slot t f i _ => do
      let i' ← delabE kopf i
      .ok (.field (.index (.field (.variable (nTab (show Fin z.tabs.length from t).val)) "slots") i')
        (nFeld (show Fin _ from f).val))
  | .fnref f _ _ => .ok (.fnref (nFn (show Fin z.fns.length from f).val))
  | .widen _ _ e => delabE kopf e
  | .add a b => do .ok (.bin "+" (← delabE kopf a) (← delabE kopf b))
  | .sub a b => do .ok (.bin "-" (← delabE kopf a) (← delabE kopf b))
  | .mul a b => do .ok (.bin "*" (← delabE kopf a) (← delabE kopf b))
  | .neg a => do
      let a' ← delabE kopf a
      -- `-(n)` for a numeral (`-n` is the literal `-n`); every other operand prints `-x`/`-(x)`
      .ok (match a' with
        | .lit m => .un "-()" (.lit m)
        | x => .un "-" x)
  | .div _ _ a b => do .ok (.bin "/" (← delabE kopf a) (← delabE kopf b))
  | .rem _ _ a b => do .ok (.bin "%" (← delabE kopf a) (← delabE kopf b))
  | .sdiv _ a b => do .ok (.bin "/" (← delabE kopf a) (← delabE kopf b))
  | .srem _ a b => do .ok (.bin "%" (← delabE kopf a) (← delabE kopf b))
  | .band _ _ a b => do .ok (.bin "&" (← delabE kopf a) (← delabE kopf b))
  | .bor _ _ _ _ _ a b => do .ok (.bin "|" (← delabE kopf a) (← delabE kopf b))
  | .bxor _ _ _ _ _ a b => do .ok (.bin "^" (← delabE kopf a) (← delabE kopf b))
  | .shl _ _ _ _ _ a b => do .ok (.bin "<<" (← delabE kopf a) (← delabE kopf b))
  | .shr _ _ _ _ _ a b => do .ok (.bin ">>" (← delabE kopf a) (← delabE kopf b))
  | .none _ => .ok (.call "None" [])
  | .some e => do .ok (.call "Some" [← delabE kopf e])
  | .istSome e => do
      -- `o.is_some()` over a place; `None`/`Some(i)` have no suffix (no source program tests them)
      match ← delabE kopf e with
      | .variable v => .ok (.ext .call [] [.field (.variable v) "is_some"])
      | .field b f => .ok (.ext .call [] [.field (.field b f) "is_some"])
      | _ => .error "is_some over a value that is no place"
  | .oldG g _ => .ok (.old (.variable (nGlob (show Fin z.globs.length from g).val)))
  | .oldS t f i _ => do
      .ok (.old (.field (.index (.field (.variable (nTab (show Fin z.tabs.length from t).val)) "slots")
        (← delabE kopf i)) (nFeld (show Fin _ from f).val)))
  | .lt a b => do .ok (.bin "<" (← delabE kopf a) (← delabE kopf b))
  | .le a b => do .ok (.bin "<=" (← delabE kopf a) (← delabE kopf b))
  | .eq a b => do .ok (.bin "==" (← delabE kopf a) (← delabE kopf b))
  | .and a b => do .ok (.bin "&&" (← delabE kopf a) (← delabE kopf b))
  | .or a b => do .ok (.bin "||" (← delabE kopf a) (← delabE kopf b))
  | .not a => do .ok (.un "!" (← delabE kopf a))
  | .why n r => .ok (.why (nGrund n) (nFall r.val))
  | .forallSlots t body _ => do
      .ok (.ext .all [nVar Γ.length, "slots"] [.variable (nTab (show Fin z.tabs.length from t).val), ← delabE kopf body])
  | .existsSlots t body _ => do
      .ok (.ext .any [nVar Γ.length, "slots"] [.variable (nTab (show Fin z.tabs.length from t).val), ← delabE kopf body])
  | e => .error ("expression without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.eE e))

def delabA {Γ : Ctx} {Λ : List (Res z.deklaration)} {τs : List Ty} :
    Args z.deklaration Γ Λ τs → Except String (List SExpr)
  | .nil => .ok []
  | .cons e rest => do .ok ((← delabE z none e) :: (← delabA rest))

def delabR {Γ : Ctx} {Λ : List (Res z.deklaration)} {o : Option Ty} :
    ErgExpr z.deklaration Γ Λ o → Except String (Option SExpr)
  | .empty => .ok none
  | .val e => do .ok (some (← delabE z none e))

/-- A payload as the statement reader keeps it: the names, comma separated, or `nothing`. -/
def nutzText (gs : List z.deklaration.Glob) : String :=
  if gs.isEmpty then "nothing"
  else renderText (gs.map (fun g => [nameTok (nGlob (show Fin z.globs.length from g).val)]) |>.intersperse
    [.zeichen ","] |>.flatten)

/-- The payload of an `awaits` (braces around nothing are the empty text). -/
def nutzTextA (gs : List z.deklaration.Glob) : String :=
  if gs.isEmpty then "" else nutzText z gs

/-- The register `r` read or written through the device handle. -/
def regOrt (r : z.deklaration.Reg) : SExpr := .field (.variable "d") (nReg (show Fin z.regs.length from r).val)

/-! ### Statements and blocks -/

variable (V : Vertrag z.deklaration)

mutual

def delabS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Stmt z.deklaration V l Γ Λ Λ' → Except String (List SAnw)
  | .assignSlot t f i e _ _ => do
      .ok [.set (.field (.index (.field (.variable (nTab (show Fin z.tabs.length from t).val)) "slots")
        (← delabE z none i)) (nFeld (show Fin _ from f).val)) "=" (← delabE z none e)]
  | .assignGlob g e _ _ => do .ok [.set (.variable (nGlob (show Fin z.globs.length from g).val)) "=" (← delabE z none e)]
  | .publish g e payload _ _ _ => do
      .ok [.emit (.variable (nGlob (show Fin z.globs.length from g).val)) (← delabE z none e) (nutzText z payload)]
  | .ite c t e => do
      let c' ← delabE z none c
      let t' ← delabB t
      let e' ← delabB e
      .ok [.cond c' (.block t' none) [] (if e'.isEmpty then none else some (.block e' none))]
  | .call f args _ _ => do .ok [.call (nFn (show Fin z.fns.length from f).val) (← delabA z args)]
  | .callIndElse p args _ _ _ err => do
      let (statements, ending) ← delabEnd err
      .ok [.callIndElse (← delabE z none p) (← delabA z args)
        (nVar Γ.length) (.block statements ending)]
  | .callInd p args _ _ => do
      let as ← delabA z args
      match p with
      | .fnref f _ _ =>
        .ok [.bind false (nZeiger Γ.length) none (.fnref (nFn (show Fin z.fns.length from f).val)),
             .call (nZeiger Γ.length) as]
      | .var x => .ok [.call (nVar (Γ.length - 1 - tiefe x)) as]
      | _ => .error "indirect call through an expression without a spelling"
  | .locks L _ body => do
      .ok [.locks false (.variable (nLock (show Fin z.locks.length from L).val)) (.block (← delabB body) none)]
  | .regWrite r _ e => do .ok [.set (regOrt z r) "=" (← delabE z none e)]
  | .traverse t inv body => do
      let i' ← match inv with
        | .tru => pure none
        | i => do pure (some (← delabE z none i))
      .ok [.each (nVar Γ.length) none "slots" (.variable (nTab (show Fin z.tabs.length from t).val)) "unvisited" ""
        i' (.block (← delabB body) none)]
  | .ret e _ => do .ok [.ret (← delabR z e)]
  | .retWhy r _ => .ok [.ret (some (.why (nGrund V.gruende) (nFall r.val)))]
  | s => .error ("statement without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.cS s))

def delabB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Block z.deklaration V l Γ Λ Λ' → Except String (List SAnw)
  | .nil => .ok []
  | .cons s rest => do .ok ((← delabS s) ++ (← delabB rest))
  | .bind e rest => do .ok (.bind false (nVar Γ.length) none (← delabE z none e) :: (← delabB rest))
  | .bindCall f args _ _ _ rest => do
      .ok (.bind false (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) (← delabA z args)) ::
        (← delabB rest))
  | .bindCallElse f args _ _ _ err rest => do
      let (es, ende) ← delabEnd err
      .ok (.bindElse (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) (← delabA z args))
        (nVar Γ.length) (.block es ende) :: (← delabB rest))
  | .bindCallInd p args _ _ _ rest => do
      let as ← delabA z args
      match p with
      | .fnref f _ _ =>
        .ok (.bind false (nZeiger Γ.length) none (.fnref (nFn (show Fin z.fns.length from f).val)) ::
          .bind false (nVar Γ.length) none (.call (nZeiger Γ.length) as) :: (← delabB rest))
      | .var x => .ok (.bind false (nVar Γ.length) none (.call (nVar (Γ.length - 1 - tiefe x)) as) :: (← delabB rest))
      | _ => .error "indirect call through an expression without a spelling"
  | .regRead r _ rest => do .ok (.bind false (nVar Γ.length) none (regOrt z r) :: (← delabB rest))
  | .regReadElse r _ _ sonst rest => do
      let (es, ende) ← delabEnd sonst
      .ok (.bindElse (nVar Γ.length) none (regOrt z r) (nVar Γ.length) (.block es ende) :: (← delabB rest))
  | .awaits g payload _ _ _ rest => do
      .ok (.await (nVar Γ.length) none (.variable (nGlob (show Fin z.globs.length from g).val)) (nutzTextA z payload) ::
        (← delabB rest))
  | b => .error ("block without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.cB b))

def delabEnd {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} :
    Endblock z.deklaration V l Γ Λ → Except String (List SAnw × Option SEnde)
  | .ret e _ => do .ok ([], some (.ret (← delabR z e)))
  | .retWhy r _ => .ok ([], some (.ret (some (.why (nGrund V.gruende) (nFall r.val)))))
  | .cons s rest => do
      let ss ← delabS s
      let (rs, e) ← delabEnd rest
      .ok (ss ++ rs, e)
  | .bind e rest => do
      let x ← delabE z none e
      let (rs, en) ← delabEnd rest
      .ok (.bind false (nVar Γ.length) none x :: rs, en)
  | .bindCall f args _ _ _ rest => do
      let as ← delabA z args
      let (rs, en) ← delabEnd rest
      .ok (.bind false (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) as) :: rs, en)
  | .bindCallElse f args _ _ _ err rest => do
      let as ← delabA z args
      let (es, ee) ← delabEnd err
      let (rs, en) ← delabEnd rest
      .ok (.bindElse (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) as) (nVar Γ.length)
        (.block es ee) :: rs, en)
  | .regRead r _ rest => do
      let (rs, en) ← delabEnd rest
      .ok (.bind false (nVar Γ.length) none (regOrt z r) :: rs, en)
  | .awaits g payload _ _ _ rest => do
      let (rs, en) ← delabEnd rest
      .ok (.await (nVar Γ.length) none (.variable (nGlob (show Fin z.globs.length from g).val)) (nutzTextA z payload) ::
        rs, en)
  | .bindCallInd p args _ _ _ rest => do
      let as ← delabA z args
      let (rs, en) ← delabEnd rest
      match p with
      | .fnref f _ _ =>
        .ok (.bind false (nZeiger Γ.length) none (.fnref (nFn (show Fin z.fns.length from f).val)) ::
          .bind false (nVar Γ.length) none (.call (nZeiger Γ.length) as) :: rs, en)
      | .var x => .ok (.bind false (nVar Γ.length) none (.call (nVar (Γ.length - 1 - tiefe x)) as) :: rs, en)
      | _ => .error "indirect call through an expression without a spelling"
  | e => .error ("end block without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.cE e))

end

end Gabbro.Grammatik.Gen.Text
