module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Loops.Headers
public import Grammatik.Parser.Elab.Uebersetze.Records.Records

public import Grammatik.Parser.Elab.Uebersetze.Kontext.LocalBindings
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- `let [mut] x [: T] = v;` where `v` may be a call of a function of the unit: its value is bound at the
    callee's result type (`Block.bindCall`; a range annotation must contain the result range).
    Float introductions retain the canonical finite/range checks at their declared target. -/
def uBindWert (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (mu : Bool) (x : String)
    (t : Option STyp) (e : SExpr) : Except String (UStmt × UCtx) :=
  let floatTarget : Except String ((Int × Int) × (Int × Int) × UCtx) := do
    let target ← match t with
      | some annotation => uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner annotation
      | none => pure uFloatTy
    let .fl lo hi := target | throw "float: target is not a declared float type"
    let muts := if mu then x :: ctx.muts else ctx.muts.filter (fun name => !strEq name x)
    pure (lo, hi, uMitLokal ctx x .wert (.fl lo hi) muts)
  -- Only atomic, canonically typed float operands select IEEE arithmetic here.
  -- This binder does not recursively hoist nested float arithmetic.
  let floatBinary : Option (Except String (UStmt × UCtx)) := do
    let .bin operator a b := e | none
    let op ← match operator with
      | "+" => some GleitOp.add | "-" => some GleitOp.sub
      | "*" => some GleitOp.mul | "/" => some GleitOp.div
      | _ => none
    let left ← (uWertBody ctx a).toOption
    let right ← (uWertBody ctx b).toOption
    match uValueType ctx left, uValueType ctx right with
    | some (.fl ..), some (.fl ..) =>
      some (do
        let (lo, hi, next) ← floatTarget
        pure (.float x op left right lo hi, next))
    | _, _ => none
  match floatBinary with
  | some result => result
  | none =>
  match e with
  | source@(.float _) | source@(.un "-" (.float _)) | source@(.un "-()" (.float _)) => do
    let rational ← uFloatBound ctx.alias source
    let (lo, hi, next) ← floatTarget
    pure (.floatLit x rational lo hi, next)
  | .call "f32" args | .call "f64" args => do
    let [operand] := args | throw "floatOf: expected one integer operand"
    let target ← match t with
      | some annotation => uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner annotation
      | none => pure uFloatTy
    let .fl lo hi := target | throw "floatOf: target is not a declared float type"
    let side ← match uWertBody ctx operand with
      | .ok side => pure side
      | .error err => throw ("floatOf: " ++ err)
    let muts := if mu then x :: ctx.muts else ctx.muts.filter (fun name => !strEq name x)
    pure (.floatOf x side lo hi, uMitLokal ctx x .wert (.fl lo hi) muts)
  | _ =>
  match uRegOrt ctx e with
  | some (.error err) => .error err
  | some (.ok rg) =>
    if mu || t.isSome then .error "let of a register with a type without G form"
    else if rg.pruefung.isSome then .error "fallible register read needs `let .. else`"
    else .ok (.regRead x rg.dev rg.name,
      uMitLokal ctx x rg.art rg.ty (ctx.muts.filter (fun m => !strEq m x)))
  | none =>
  match (match t with | .some (.atom a) => ctx.sums.findIdx? (fun (s : USum) => strEq s.name a) | _ => none : Option Nat) with
  | .some k =>
      match ctx.sums[k]? with
      | .none => .error "tagged type unknown"
      | .some sm =>
        match uSVal ctx k e with
        | .error err => .error err
        | .ok sv =>
          .ok (.bindSum x k sv, uMitLokal ctx x (UParamArt.sum k) (Ty.sum sm.spec) (if mu then x :: ctx.muts else ctx.muts.filter (fun m => !strEq m x)))
  | .none =>
  match (match e with
      | .fnref f =>
        if (uParamNr ctx f).toOption.isSome || ctx.tabs.any (fun tb => strEq tb.name f) then none
        else
          match koepfe.findIdx? (fun (k : UFnKopf) => strEq k.name f) with
          | none => none
          | some n =>
            some (match koepfe[n]? with
              | some k =>
                if k.ext then .error "address of a foreign fn without G form"
                else if mu then .error "let mut of a function pointer without G form"
                else
                  -- The type of the pointer: the one written (`let p : fn(..) = &f;`, a pointer type of the
                  -- unit, number `zeigerBasis + j`), else `f`'s own signature (number `n`). That `f` conforms
                  -- to a written type is the lowering's decision (`Deklaration.passt`).
                  match (match t with
                      | .none => .ok n
                      | .some (.raw r) =>
                        match ctx.zeiger.findIdx? (strEq · r) with
                        | .some j => .ok (ctx.zeigerBasis + j)
                        | .none => .error "let of a function pointer with a type that is no pointer type"
                      | .some _ => .error "let of a function pointer with a type that is no pointer type" :
                      Except String Nat) with
                  | .error err => .error err
                  | .ok m =>
                    .ok (.bindFnref x f m, uMitLokal ctx x (UParamArt.fnptr m) (Ty.fnptr m)
                      (ctx.muts.filter (fun m => !strEq m x)))
              | none => .error ("function unknown: " ++ f))
      | .call c args =>
        match uFnZeiger ctx koepfe c with
        | none => none
        | some (.error err) => some (.error err)
        | some (.ok ziel) =>
          some (if mu || t.isSome then .error "let of an indirect call with a type without G form" else
            match uRuf ctx tabs koepfe ziel.name args with
            | .error err => .error err
            | .ok (callee, xs) =>
              let muts : List String := ctx.muts.filter (fun m => !strEq m x)
              if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
              else if callee.resBool then
                .ok (.bindCallInd x c callee.name xs, uMitLokal ctx x UParamArt.bool Ty.bool muts)
              else match callee.res with
                | some (lo, hi) => .ok (.bindCallInd x c callee.name xs, uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts)
                | none =>
                  match callee.resWhy with
                  | some (k, n) => .ok (.bindCallInd x c callee.name xs, uMitLokal ctx x (UParamArt.why k) (Ty.why n) muts)
                  | none => .error "call without a value")
      | _ => none : Option (Except String (UStmt × UCtx))) with
  | some r => r
  | none =>
  match e with
  | .call c args =>
    match koepfe.find? (fun (k : UFnKopf) => strEq k.name c) with
    | .none => uBindWertAllg ctx mu x t e
    | .some _ =>
      if mu then .error "let mut of a call without G form"
      else
        match uRuf ctx tabs koepfe c args with
        | .error err => .error err
        | .ok (callee, xs) =>
          let muts : List String := ctx.muts.filter (fun m => !strEq m x)
          if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
          else
          if callee.ext then
            match callee.axErg with
            | .none => .error "call without a value"
            | .some Ty.bool => .ok (.bindAx x c xs, uMitLokal ctx x UParamArt.bool Ty.bool muts)
            | .some (Ty.int lo hi) => .ok (.bindAx x c xs, uAnnotatedBinding ctx t (uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts))
            | .some (Ty.ref n) => .ok (.bindAx x c xs, uMitLokal ctx x (UParamArt.ref n) (Ty.ref n) muts)
            | .some _ => .error "answer of a foreign fn without G form"
          else if let some ty := callee.resTy then do
            match t with
            | some annotation =>
              let declared ← uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner annotation
              if decide (declared = ty) then pure () else throw "source export: call result disagrees with annotation"
            | none => pure ()
            pure (.bindCall x c xs, uMitLokal ctx x (uArtVon ty) ty muts)
          else
          match callee.resBool, callee.res with
          | true, _ =>
            match t with
            | .some (.atom "bool") =>
              .ok (.bindCall x c xs, uMitLokal ctx x UParamArt.bool (Ty.bool) muts)
            | .none =>
              .ok (.bindCall x c xs, uMitLokal ctx x UParamArt.bool (Ty.bool) muts)
            | .some _ => .error "let of a truth value with a number type"
          | false, .some (lo, hi) =>
            match (match t with
                | .none => .ok true
                | .some ty =>
                  match uErgBereich ctx.alias ty with
                  | .error err => .error err
                  | .ok (a, b) => .ok (decide (a ≤ lo) && decide (hi ≤ b)) : Except String Bool) with
            | .error err => .error err
            | .ok false => .error "let: value outside the annotated range"
            | .ok true =>
              .ok (.bindCall x c xs, uAnnotatedBinding ctx t (uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts))
          | false, .none =>
            -- A call whose answer is an `option index into T` binds an option of that table.
            match callee.resOpt, t with
            | .some (num, cnt), .none =>
              .ok (.bindCall x c xs, uMitLokal ctx x (UParamArt.opt num) (Ty.opt cnt) muts)
            | _, _ =>
            match callee.resSum, callee.resWhy, t with
            | .some (k, cases), _, .none =>
              .ok (.bindCall x c xs, uMitLokal ctx x (UParamArt.sum k) (Ty.sum cases) muts)
            | .none, .some (k, n), .none => .ok (.bindCall x c xs, uMitLokal ctx x (UParamArt.why k) (Ty.why n) muts)
            | _, _, _ => .error "call without a value"
  | _ => uBindWertAllg ctx mu x t e

/-- `return R::C` through the reason channel. -/
def uEndeKanal (ctx : UCtx) (r c : String) : Except String URet :=
  match ctx.kanal, ctx.whys.findIdx? (fun w => strEq w.name r) with
  | .some (k, _), .some j =>
    if k != j then .error "return of a foreign reason"
    else
      match ctx.whys[j]? with
      | .some w =>
        match w.cases.findIdx? (fun x => strEq x c) with
        | .some i => .ok (.why i)
        | .none => .error ("reason case unknown: " ++ c)
      | .none => .error ("reason unknown: " ++ r)
  | .none, _ => .error "return of a reason without a reason channel"
  | _, .none => .error ("reason unknown: " ++ r)

/-- The trailing return (the `check_body`/`tr_body` of
    `lean_g.rs`): a result falls off nowhere, and a missing
    result returns nowhere. -/
def uEnde (ctx : UCtx) : Option SEnde → Except String URet
  | .none =>
    -- a `-> never` function ends in a call that does not return: its `never` answer is the result
    if ctx.resTy == some Ty.never then .ok (.wert (.param "#ax")) else
    match ctx.res with
    | .some _ => .error "fn with a result falls off"
    | .none => if ctx.resBool || ctx.resOpt.isSome || ctx.resSum.isSome || ctx.resTy.isSome then .error "fn with a result falls off" else .ok .empty
  | .some (.ret .none) =>
    match ctx.res with
    | .some _ => .error "return without value with result"
    | .none => if ctx.resBool || ctx.resOpt.isSome || ctx.resSum.isSome || ctx.resTy.isSome then .error "return without value with result" else .ok .empty
  | .some (.ret (.some (.why r c))) =>
    match ctx.resWhy, ctx.whys.findIdx? (fun w => strEq w.name r) with
    | .some (k, _), .some j =>
      -- a function of reason type `R` returns the VALUE `R::C` (its channel, if any, names another reason)
      if k == j && ctx.kanal.map (·.1) != some j then
        match ctx.whys[j]? with
        | .some w =>
          match w.cases.findIdx? (fun x => strEq x c) with
          | .some i => .ok (.grund (.fall i))
          | .none => .error ("reason case unknown: " ++ c)
        | .none => .error ("reason unknown: " ++ r)
      else uEndeKanal ctx r c
    | _, _ => uEndeKanal ctx r c
  | .some (.ret (.some v)) =>
    if ctx.resTy.isSome then
      match uWertBody ctx v with
      | .error e => .error e
      | .ok w => .ok (.wert w)
    else
    match ctx.resWhy with
    | .some (k, _) =>
      match v with
      | .variable p =>
        match uParamNr ctx p with
        | .error e => .error e
        | .ok j =>
          match uArtBei ctx.kinds j with
          | .ok (.why k') => if k' == k then .ok (.grund (.var p)) else .error "return of a foreign reason"
          | _ => .error "return of a non-reason for a reason result"
      | _ => .error "reason result without G form"
    | .none =>
    match ctx.resSum with
    | .some (sidx, _) =>
      match uSVal ctx sidx v with
      | .error e => .error e
      | .ok sv => .ok (.sum sv)
    | .none =>
    match ctx.resOpt with
    | .some (num, _) =>
      match uOpt ctx num v with
      | .error e => .error e
      | .ok o => .ok (.opt o)
    | .none =>
    if ctx.resBool then
      match uBool ctx v with
      | .error e => .error e
      | .ok b => .ok (.bool b)
    else
    match ctx.res with
    | .none => .error "return with value without result"
    | .some _ =>
      match uWertBody ctx v with
      | .error e => .error e
      | .ok s => .ok (.val s)
  | .some _ => .error "block end without G form"

/-- The ender of a nested block as a statement: `return [v]` (against the function's result), or
    `leave i`/`next i` naming the innermost `traverse` binder. -/
def uEndeStmt (ctx : UCtx) : Option SEnde → Except String (List UStmt)
  | .none => .ok []
  | .some (.ret v) =>
    match uEnde ctx (.some (.ret v)) with
    | .error e => .error e
    | .ok r => .ok [UStmt.ret r]
  | .some (.leave m) =>
    if ctx.loops.head? == some ("#consume:" ++ m) then .error "consuming traversal forbids leave"
    else if ctx.loops.head? == some m then .ok [UStmt.leave m]
    else .error "leave outside the innermost loop"
  | .some (.next m) =>
    if ctx.loops.head? == some ("#consume:" ++ m) then .error "consuming traversal forbids next"
    else if ctx.loops.head? == some m then .ok [UStmt.next m]
    else .error "next outside the innermost loop"


end Gabbro.Grammatik.Parser.Uebersetze
