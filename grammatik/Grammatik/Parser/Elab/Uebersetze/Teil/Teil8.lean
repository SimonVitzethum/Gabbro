module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
public import Grammatik.Parser.Elab.Uebersetze.Records.Records

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The header of a `retry`: the label, the pass bound, the predicate, the handler. `progress` must name an
    `assume` item. -/
def uRetryKopf (ctx : UCtx) (h : String) : Except String (String × Nat × UEns × String) :=
  match uSchleifenKopf2 h with
  | .error e => .error e
  | .ok secs =>
    match uAbschnitt secs "until", uOpsZahl ctx (uAbschnitt secs "bounded"), uEinName (uAbschnitt secs "progress"),
        uEinName (uAbschnitt secs "on_exceeded") with
    | some pt, some n, some a, some y =>
      if !(ctx.annahmen.any (strEq · a)) then .error ("assumption unknown: " ++ a)
      else
        match parseTop (pt ++ [Token.ende]) with
        | .error _ => .error "retry condition without G form"
        | .ok p =>
          match uBool ctx p with
          | .error e => .error e
          | .ok pv => .ok ((match uAbschnitt secs "" with | some [.ident l] => l | some [.wort l] => l | _ => ""), n, pv, y)
    | none, _, _, _ => .error "retry without until without G form"
    | _, _, _, _ => .error "retry header without G form"

/-- The header of a `forever`: the label and the position of the assumption `progress` names. -/
def uForeverKopf (ctx : UCtx) (h : String) : Except String (String × Nat) :=
  match uSchleifenKopf2 h with
  | .error e => .error e
  | .ok secs =>
    match uAbschnitt secs "leaves" with
    | some _ => .error "forever leaves without G form"
    | none =>
      match uEinName (uAbschnitt secs "progress") with
      | none => .error "forever without progress without G form"
      | some a =>
        match ctx.annahmen.findIdx? (fun x => strEq x a) with
        | none => .error ("assumption unknown: " ++ a)
        | some k => .ok ((match uAbschnitt secs "" with | some [.ident l] => l | some [.wort l] => l | _ => ""), k)

/-- The value of a bound of a narrowed range: a numeral, a negated numeral or a named constant. -/
def uNarrowWert (ctx : UCtx) : List Token → Option Int
  | [.num n] => some (Int.ofNat n)
  | [.zeichen "-", .num n] => some (-(Int.ofNat n))
  | [.ident c] => (ctx.lits.find? (fun k => strEq k.1 c)).map (·.2)
  | [.wort c] => (ctx.lits.find? (fun k => strEq k.1 c)).map (·.2)
  | _ => none

/-- A range text `lo .. hi` / `lo ..< hi` split at the dots: the left tokens, whether the upper bound is
    exclusive, the right tokens. -/
def uTeileBereich : List Token → List Token → Option (List Token × Bool × List Token)
  | _, [] => none
  | acc, .zeichen ".." :: rest => some (acc.reverse, false, rest)
  | acc, .zeichen "..<" :: rest => some (acc.reverse, true, rest)
  | acc, t :: rest => uTeileBereich (t :: acc) rest

/-- The target range of `narrow x to T else ..`: a range (`lo .. hi`, `lo ..< hi`) or a type word. -/
def uNarrowBereich (ctx : UCtx) (t : String) : Except String (Int × Int) :=
  match lex t with
  | .error _ => .error "narrow range without G form"
  | .ok toks0 =>
    let toks := toks0.filter (fun k => match k with | .ende => false | _ => true)
    match uTeileBereich [] toks with
    | some (l, ex, r) =>
      match uNarrowWert ctx l, uNarrowWert ctx r with
      | some a, some b => .ok (a, if ex then b - 1 else b)
      | _, _ => .error "narrow bound without G form"
    | none =>
      match toks with
      | [.ident n] => uTypName ctx.alias n
      | [.wort n] => uTypName ctx.alias n
      | _ => .error "narrow range without G form"

/-- The binding the rest of the block reads after a narrowing: `x` at the narrowed range. -/
def uNarrowKopf (ctx : UCtx) (x : String) (t : String) : Except String (Int × Int × UCtx) :=
  match uParamNr ctx x with
  | .error e => .error e
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok .int =>
      match uNarrowBereich ctx t with
      | .error e => .error e
      | .ok (lo, hi) =>
        .ok (lo, hi, uMitLokal ctx x UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m x)))
    | _ => .error "narrow of a non-number"

/-- `let [mut] x [: T] = v;`: a number (the binding carries the computed range of `v`, or with `mut` the
    declared one) or a truth value; the statement and the context for the rest of the block. -/
def uBindWertAllg (ctx : UCtx) (mu : Bool) (x : String) (t : Option STyp) (e : SExpr) :
    Except String (UStmt × UCtx) :=
  let muts : List String := if mu then x :: ctx.muts else ctx.muts.filter (fun m => !strEq m x)
  let boolCtx : UCtx := { ctx with names := x :: ctx.names, kinds := UParamArt.bool :: ctx.kinds,
                                   types := Ty.bool :: ctx.types, bits := 0 :: ctx.bits, muts := muts }
  match t with
  | .some (.atom "bool") =>
    match uBool ctx e with
    | .error err => .error err
    | .ok b => .ok (.bindB x b, boolCtx)
  | .some (.index true tn) =>
    if mu then .error "let mut of an option without G form"
    else
      match uTabNr ctx.tabs tn with
      | .error err => .error err
      | .ok (num, c) =>
        match uOpt ctx num e with
        | .error err => .error err
        | .ok o => .ok (.bindOpt x num o, uMitLokal ctx x (UParamArt.opt num) (Ty.opt c) muts)
  | .none =>
    match uWertBody ctx e with
    | .ok sd =>
      match uValueType ctx sd with
      | some ty@(.prod ..) | some ty@(.arr ..) | some ty@(.str ..) =>
        .ok (.bindW x (some ty) sd, uMitLokal ctx x .wert ty muts)
      | _ =>
        if mu then .error "let mut without a type"
        else
          match uBindKopf ctx x .none with
          | .error err => .error err
          | .ok (d, ctx') => .ok (.bind x d sd, { ctx' with muts := muts })
    | .error err =>
      match uBool ctx e with
      | .ok b => .ok (.bindB x b, boolCtx)
      | .error _ =>
        match uOptEin ctx e with
        | .error _ =>
          match uSValEin ctx e with
          | .error _ => .error err
          | .ok (sv, k) =>
            match ctx.sums[k]? with
            | .none => .error err
            | .some sm => .ok (.bindSum x k sv, uMitLokal ctx x (UParamArt.sum k) (Ty.sum sm.spec) muts)
        | .ok (o, num) =>
          match ctx.tabs[num]? with
          | .none => .error err
          | .some tb => .ok (.bindOpt x num o, uMitLokal ctx x (UParamArt.opt num) (Ty.opt tb.count) muts)
  | .some ty@(.prod ..) | .some ty@(.array _ _) | .some ty@(.str _) =>
    if mu then .error "let mut of an aggregate without G form"
    else
      match uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ty with
      | .error err => .error err
      | .ok τ =>
        match uWertBody ctx e with
        | .error err => .error err
        | .ok sd => .ok (.bindW x (some τ) sd, uMitLokal ctx x UParamArt.wert τ muts)
  | .some ty =>
    match uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ty with
    | .ok ty@(.prod ..) => do
      let side ← uWertBody ctx e
      pure (.bindW x (some ty) side, uMitLokal ctx x .wert ty muts)
    | _ =>
      match uWertBody ctx e with
      | .error err => .error err
      | .ok sd =>
        match uBindKopf ctx x (.some ty) with
        | .error err => .error err
        | .ok (d, ctx') =>
          if mu then
            match d with
            | .some (lo, hi) => .ok (.bindMut x lo hi sd, { ctx' with muts := muts })
            | .none => .error "let mut without a type"
          else .ok (.bind x d sd, { ctx' with muts := muts })

/-- `let [mut] x [: T] = v;` where `v` may be a call of a function of the unit: its value is bound at the
    callee's result type (`Block.bindCall`; a range annotation must contain the result range). -/
def uBindWert (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (mu : Bool) (x : String)
    (t : Option STyp) (e : SExpr) : Except String (UStmt × UCtx) :=
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
    if mu then .error "let mut of a tagged value without G form"
    else
      match ctx.sums[k]? with
      | .none => .error "tagged type unknown"
      | .some sm =>
        match uSVal ctx k e with
        | .error err => .error err
        | .ok sv =>
          .ok (.bindSum x k sv, uMitLokal ctx x (UParamArt.sum k) (Ty.sum sm.spec) (ctx.muts.filter (fun m => !strEq m x)))
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
            | .some (Ty.int lo hi) => .ok (.bindAx x c xs, uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts)
            | .some (Ty.ref n) => .ok (.bindAx x c xs, uMitLokal ctx x (UParamArt.ref n) (Ty.ref n) muts)
            | .some _ => .error "answer of a foreign fn without G form"
          else if let some ty := callee.resTy then do
            match t with
            | some annotation =>
              let declared ← uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces annotation
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
              .ok (.bindCall x c xs, uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts)
          | false, .none =>
            match callee.resWhy, t with
            | .some (k, n), .none => .ok (.bindCall x c xs, uMitLokal ctx x (UParamArt.why k) (Ty.why n) muts)
            | _, _ => .error "call without a value"
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
    if ctx.loops.head? == some m then .ok [UStmt.leave m]
    else .error "leave outside the innermost loop"
  | .some (.next m) =>
    if ctx.loops.head? == some m then .ok [UStmt.next m]
    else .error "next outside the innermost loop"

/-- The header of `traverse b over slots of S by unvisited [touches …] [invariant p]`: the table (named
    directly or through a pointer parameter), the invariant over the OUTER context (the binder is not in
    scope there), and the context of the body, where the binder is an index into the table and the
    innermost loop label. Other domains, `of e` and `by consuming` have no G form. -/
def uSchleifenKopf (ctx : UCtx) (b : String) (o : Option SExpr) (k : String) (s : SExpr) (m : String)
    (inv : Option SExpr) : Except String (String × UEns × UCtx) :=
  if o.isSome then .error "traverse of without G form"
  else if !strEq k "slots" then .error "traverse domain without G form"
  else if !strEq m "unvisited" then .error "traverse by consuming without G form"
  else
    match (match s with
        | .variable tn =>
          match ctx.tabs.findIdx? (fun x => strEq x.name tn) with
          | .some num => .ok (tn, num)
          | .none =>
            match uParamNr ctx tn with
            | .error e => .error e
            | .ok j =>
              match uArtBei ctx.kinds j with
              | .ok (.ptr ⟨_, _, .table num⟩) =>
                match ctx.tabs[num]? with
                | .some tb => .ok (tb.name, num)
                | .none => .error "pointer table unknown"
              | _ => .error "traverse domain without G form"
        | _ => .error "traverse domain without G form" : Except String (String × Nat)) with
    | .error e => .error e
    | .ok (tab, num) =>
      match (match inv with
          | .none => .ok UEns.tru
          | .some p => uBool ctx p : Except String UEns) with
      | .error e => .error e
      | .ok iv =>
        let cnt : Int := match ctx.tabs[num]? with | .some tb => tb.count | .none => 0
        .ok (tab, iv, { ctx with names := b :: ctx.names, kinds := .index num :: ctx.kinds,
                                 types := .index cnt :: ctx.types, bits := 0 :: ctx.bits,
                                 loops := b :: ctx.loops })

end Gabbro.Grammatik.Parser.Uebersetze
