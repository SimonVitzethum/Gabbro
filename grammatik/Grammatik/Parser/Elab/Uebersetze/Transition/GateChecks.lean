module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
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
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
public import Grammatik.Korpus.Programme.Export104

/-! The binding half of a `syscall` gate: answer register, handed stack, errno map and byte buffers
    (`N064`, `N447`, `N067`, `N464`, `N068`), split from `Teil12` (file-size rule). -/

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The register a binding names: `rdi = fd` binds `rdi`, a bare `rax` names `rax`. -/
def uBindReg : SRegBind → String
  | .binds r _ => r
  | .reg r => r

/-- The capacity of this exact pointer parameter. -/
def istLenof (p : String) : SExpr → Bool
  | .built f [.variable q] => strEq f "lenof" && strEq q p
  | _ => false

/-- A transfer length: another integer parameter, or a positive constant extent.
    A strict comparison with zero also requires at least one byte. -/
def istBand (params : List String) (p : String) (strict : Bool) : SExpr → Bool
  | .variable v => !strEq v p && params.any (fun y => strEq y v)
  | .lit n => strict || decide (0 < n)
  | _ => false

/-- Find a bound through conjunctions only: disjunctions do not promise either arm. -/
def istLaengenSchranke (params : List String) (p : String) : SExpr → Bool
  | .bin op a b =>
    if strEq op "&&" then istLaengenSchranke params p a || istLaengenSchranke params p b
    else
      ((strEq op "<=" || strEq op "<") && istBand params p (strEq op "<") a && istLenof p b) ||
      ((strEq op ">=" || strEq op ">") && istLenof p a && istBand params p (strEq op ">") b)
  | _ => false

/-- The way a gate is bound: a `kernel` pairing is refused (`N068` -- the call would be paired
    with a Gabbro kernel's dispatch entry and no assumption named, but the pairing check and
    the stub are unbuilt), a sealed machine is refused (`A006`). A `via` variable carries no
    binding of its own. -/
def uTorWegPruef : SWay → Except String Unit
  | .lit _ _ _ (.core p) =>
    .error ("syscall gate kernel pairing without G form: " ++ "::".intercalate p)
  | .lit _ arch _ _ =>
    if archOffen arch then .ok ()
    else .error ("syscall gate arch sealed without G form: " ++ arch)
  | .via _ => .ok ()

/-- The answer register against the clobbers (`N064`): what carries the answer out is not
    destroyed. This is the string-level shadow of `TorAbi.gut` (`Hardware/Tor/Abi.lean`): the
    elaborator cannot use that judgment directly -- the surface number is an `SExpr`, the trap
    text and the number register do not exist yet, and registers are names here. -/
def uTorAntwortPruef (outs : List SRegBind) (dirty : List String) : Except String Unit :=
  match outs.find? (fun o => dirty.any (fun d => strEq d (uBindReg o))) with
  | some o => .error ("syscall gate answer register clobbered without G form: " ++ uBindReg o)
  | none => .ok ()

/-- The handed-stack register (`N447`): the one clause that may claim stack-ness stands at most
    once -- the stub hands one register to the child, and two names would split it. -/
def uTorStapelPruef : List String → Except String Unit
  | [] => .ok ()
  | [_] => .ok ()
  | _ :: s :: _ => .error ("syscall gate second stack clause without G form: " ++ s)

/-- The `errors` map against the `or` channel (`N067`): every listed errno has exactly one arm,
    and every target is a case of the declared channel. An errno outside the table stays what it
    is -- the named hardware outcome "the kernel answered outside its contract" -- and is not
    touched here. A gate without a channel carries no map; a channel that resolves nowhere is
    refused where the head is read (`reason unknown`). -/
def uTorFehlerPruef (fail : Option String) (whys : List UWhy)
    (codes : List (String × Option SExpr × String)) : Except String Unit :=
  match fail with
  | none =>
    match codes with
    | [] => .ok ()
    | (e, _, _) :: _ =>
      .error ("syscall gate errors map without a reason channel without G form: " ++ e)
  | some r =>
    match whys.find? (fun w => strEq w.name r) with
    | none => .ok ()
    | some w =>
      match codes.find? (fun c => 1 < (codes.filter (fun d => strEq d.1 c.1)).length) with
      | some (e, _, _) => .error ("syscall gate error listed twice without G form: " ++ e)
      | none =>
        match codes.find? (fun c => !(w.cases.any (fun t => strEq t c.2.2))) with
        | some (e, _, t) =>
          .error ("syscall gate error target without a declared case without G form: " ++ e ++ " => " ++ t)
        | none => .ok ()

/-- The buffers a gate moves bytes through (`N464`): a parameter that points at numbers is a
    buffer the kernel moves bytes through -- it points at `u8`/`i8`, and the gate bounds it by a
    length clause `x <= lenof(p)` over an integer parameter or a positive constant. A pointer into a table is a
    capability, not a transfer, and is not held to this clause. -/
def uTorPufferPruef (alias : List (String × (Int × Int))) (tabs : List UTab) (params : List (String × STyp)) (pre : List SExpr) :
    Except String Unit :=
  let names := params.filterMap fun (n, t) => match uTypIn alias tabs [] [] [] t with
    | .ok (.int ..) => some n
    | _ => none
  params.foldlM (fun _ (p, t) => match t with
    | .ptr _ _ (.atom a) =>
      if strEq a "u8" || strEq a "i8" then
        if pre.any (istLaengenSchranke names p) then .ok ()
        else .error ("syscall gate buffer without length bound without G form: " ++ p)
      else
        match uTabNr tabs a with
        | .ok _ => .ok ()
        | .error _ => .error ("syscall gate buffer without byte pointee without G form: " ++ p)
    | .ptr .. => .error ("syscall gate buffer without byte pointee without G form: " ++ p)
    | _ => .ok ()) ()

/-- Check the concrete binding when present, then the buffer contract for every gate.
    A `via` variable supplies the binding, but never exempts its contract from N464. -/
def uTorBindungPruef (alias : List (String × (Int × Int))) (tabs : List UTab) (whys : List UWhy) (sc : SSyscall) : Except String Unit := do
  match sc.way with
  | .via _ => pure ()
  | .lit _ _ bind _ => do
    uTorAntwortPruef bind.outs bind.dirty
    uTorStapelPruef bind.stack
    uTorFehlerPruef sc.fail whys bind.codes
  uTorPufferPruef alias tabs sc.params sc.gate.pre

end Gabbro.Grammatik.Parser.Uebersetze
