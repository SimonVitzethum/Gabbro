module
public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.CallElse
public import Grammatik.Parser.Elab.Uebersetze.Branches
public import Grammatik.Parser.Elab.Uebersetze.Breaking
public import Grammatik.Parser.Elab.Uebersetze.Folds.Substitution
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
mutual
/-- Expand expression folds before processing the ordinary statement forms.
    The wrapper shares the core's fuel; dispatch itself consumes no extra unit. -/
def uAnwReihe (tabs : List UTab) (koepfe : List UFnKopf) :
    Nat → UCtx → List SAnw → Except String (List UStmt × UCtx)
  | 0, _, _ => .error "nesting without G form"
  | _ + 1, ctx, [] => .ok ([], ctx)
  | fuel + 1, ctx, statement :: rest => do
    let (beforeStmt, ctx, statement) ← expandFoldStmt ctx statement
    let (code, ctx) ← uAnwReiheCore tabs koepfe (fuel + 1) ctx (statement :: rest)
    pure (beforeStmt ++ code, ctx)
termination_by fuel _ _ => (fuel, (1 : Nat))
decreasing_by all_goals exact Prod.Lex.right _ (by omega)
/-- A run of body statements as a flat list. A `let` extends the context for the rest of the run;
    `locks L { ... }` elaborates its body with `L` HELD (guards, calls) and the bindings made inside it
    end with it; returns retain lexical cleanup scopes, while unsupported lock expressions are refused.
    Structural in a fuel (one unit per statement and per block). -/
def uAnwReiheCore (tabs : List UTab) (koepfe : List UFnKopf) :
    Nat → UCtx → List SAnw → Except String (List UStmt × UCtx)
  | 0, _, _ => .error "nesting without G form"
  | _ + 1, ctx, [] => .ok ([], ctx)
  | _ + 1, _, .lcall .. :: _ | _ + 1, _, .bindLib .. :: _ =>
      .error "C02: library call needs certified immutable payload initialization and ordinary call expansion"
  | f + 1, ctx, .callIndElse p args e body :: rest => uCallIndElse tabs koepfe (uAnwReihe tabs koepfe f) ctx p args e body rest
  | f + 1, ctx, .callElse c args e body :: rest => uCallElse tabs koepfe (uAnwReihe tabs koepfe f) ctx c args e body rest
  | f + 1, ctx, .bind mu x t e :: rest =>
    match uBindWert ctx tabs koepfe mu x t e with
    | .error err => .error err
    | .ok (st, ctx') =>
      let ctx' := foldBindingContext ctx ctx' st
      match uAnwReihe tabs koepfe f ctx' rest with
      | .error err => .error err
      | .ok (xs, cE) => .ok (st :: xs, cE)
  | f + 1, ctx, .cases scrut arms :: rest =>
    uCases (uAnwReihe tabs koepfe f) ctx scrut arms rest
  | f + 1, ctx, .await x ty (.variable a) pl :: rest =>
    match ctx.globs.find? (fun g => strEq g.name a) with
    | .none => .error "awaits without an atomic without G form"
    | .some gl =>
      if !gl.atomic then .error "awaits without an atomic without G form"
      else if !uNamenGleich (uNutzNamen pl) gl.nutzlast then .error "awaits a payload other than the declared one"
      else match uBinderTyp ctx "awaits" ty gl.ty with
      | .error err => .error err
      | .ok () =>
        let muts := ctx.muts.filter (fun m => !strEq m x)
        let ctx' := match gl.ty with
          | .bool => uMitLokal ctx x UParamArt.bool Ty.bool muts
          | .int lo hi => uMitLokal ctx x UParamArt.int (Ty.int lo hi) muts
          | .wert τ => uMitLokal ctx x UParamArt.wert τ muts
        match uAnwReihe tabs koepfe f ctx' rest with
        | .error err => .error err
        | .ok (xs, cE) => .ok (UStmt.awaitBind x a :: xs, cE)
  | f + 1, ctx, .swap x ty (.variable a) k :: rest =>
    match ctx.globs.find? (fun g => strEq g.name a) with
    | .none => .error ("exchange of an unknown static: " ++ a)
    | .some gl =>
      match gl.ty with
      | .int lo hi =>
        match uTauschSchwanz a k with
        | .error err => .error err
        | .ok ⟨v, zweige, sonst, pub, aw, vergleich⟩ =>
          match uBinderTyp ctx "exchange" ty gl.ty with
          | .error err => .error err
          | .ok () =>
            if !uNamenGleich (pub.map String.toList) gl.nutzlast then
              .error "exchange publishes a payload other than the declared one"
            else if (aw.map (fun ns => !gl.atomic || !uNamenGleich (ns.map String.toList) gl.nutzlast)).getD false then
              .error "exchange awaits a payload other than the declared one"
            else
            let ctxV := uMitLokal ctx v UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m v))
            match uSeq (zweige.map (fun (c, e) =>
                match uBool ctxV c, uWertBody ctxV e with
                | .ok c', .ok e' => .ok (c', e')
                | .error err, _ | _, .error err => .error err)), uWertBody ctxV sonst with
            | .error err, _ | _, .error err => .error err
            | .ok zs0, .ok neu0 =>
              let zs := (List.range zs0.length).zip zs0 |>.map (fun (i, (c, e)) =>
                (c, uArmEng ctxV v lo hi (some c) ((zs0.take i).map (·.1)) e))
              let neu := uArmEng ctxV v lo hi none (zs0.map (·.1)) neu0
              let vor := if aw.isSome then [UStmt.awaitBind "#awaits" a] else []
              match vergleich with
              | none =>
                let ctx' := uMitLokal ctx x UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m x))
                match uAnwReihe tabs koepfe f ctx' rest with
                | .error err => .error err
                | .ok (xs, cE) => .ok (vor ++ UStmt.tausch x a v zs neu :: xs, cE)
              | some p =>
                match uBool ctxV p with
                | .error err => .error err
                | .ok pv =>
                  let ctx' := uMitLokal ctxV x UParamArt.bool Ty.bool (ctx.muts.filter (fun m => !strEq m x))
                  match uAnwReihe tabs koepfe f ctx' rest with
                  | .error err => .error err
                  | .ok (xs, cE) => .ok (vor ++ UStmt.tausch v a v zs neu :: UStmt.bindB x pv :: xs, cE)
      | _ => .error "exchange of a static that is not a number without G form"
  | f + 1, ctx, .ret v :: rest =>
    match uEnde ctx (some (.ret v)) with
    | .error err => .error err
    | .ok r =>
      match uAnwReihe tabs koepfe f ctx rest with
      | .error err => .error err
      | .ok (xs, cE) => .ok (UStmt.ret r :: xs, cE)
  | f + 1, ctx, .bindElse y t value e body :: rest =>
    uBindElse tabs koepfe (uAnwReihe tabs koepfe f) ctx y t value e body rest
  | f + 1, ctx, .bindAxiomOpt x t (.call c args) :: rest =>
    if t.isSome then .error "optional bind with a type without G form"
    else
      (uRuf ctx tabs koepfe c args).bind fun (callee, xs) =>
        if !callee.ext then .error "optional bind needs an axiom callee"
        else
          let next := match callee.res with
            | none => ctx
            | some r => uMitLokal ctx x UParamArt.int (Ty.int r.1 r.2)
                (ctx.muts.filter (fun m => !strEq m x))
          (uAnwReihe tabs koepfe f next rest).bind fun (ys, cE) =>
            .ok (UStmt.bindOptBeg x c xs :: ys, cE)
  | f + 1, ctx, .bindAxiomOptElse x t (.call c args) e (.block ss en) :: rest =>
    if t.isSome then .error "optional bind with a type without G form"
    else
      (uRuf ctx tabs koepfe c args).bind fun (callee, xs) =>
        if !callee.ext then .error "optional bind needs an axiom callee"
        else match callee.kanal with
        | none => .error "let else of a call without a reason channel"
        | some (num, cnt) =>
          (uAnwReihe tabs koepfe f (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
              (ctx.muts.filter (fun m => !strEq m e))) ss).bind fun (body, ctxEB) =>
            (uEndeStmt ctxEB en).bind fun endS =>
              let next := match callee.res with
                | none => ctx
                | some r => uMitLokal ctx x UParamArt.int (Ty.int r.1 r.2)
                    (ctx.muts.filter (fun m => !strEq m x))
              (uAnwReihe tabs koepfe f next rest).bind fun (ys, cE) =>
                .ok ([UStmt.bindOptElseBeg x c xs e] ++ body ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | _ + 1, _, .bindAxiomOpt .. :: _ | _ + 1, _, .bindAxiomOptElse .. :: _ =>
    .error "optional bind needs an axiom callee"
  | f + 1, ctx, .alloc mu x t an v (.some (.block ss e)) :: rest =>
    if mu || t.isSome then .error "alloc binding without G form"
    else
      match ctx.tabs.findIdx? (fun y => y.arena && strEq y.name an) with
      | .none => .error ("arena unknown: " ++ an)
      | .some num =>
        match ctx.tabs[num]? with
        | .none => .error "arena unknown"
        | .some tb =>
          match uWertBody ctx v with
          | .error err => .error err
          | .ok sv =>
            match uAnwReihe tabs koepfe f ctx ss with
            | .error err => .error err
            | .ok (body, ctxB) =>
              match (match e with
                  | .none => .error "alloc else falls through"
                  | .some _ => uFoldEndeStmt ctxB e : Except String (List UStmt)) with
              | .error err => .error err
              | .ok endS =>
                match uAnwReihe tabs koepfe f (uMitLokal ctx x (UParamArt.index num) (Ty.index tb.count)
                    (ctx.muts.filter (fun m => !strEq m x))) rest with
                | .error err => .error err
                | .ok (xs, cE) => .ok ([UStmt.allocBeg x an sv] ++ body ++ endS ++ [UStmt.blkEnd] ++ xs, cE)
  | f + 1, ctx, .alloc mu x t an v .none :: rest =>
    if mu || t.isSome then .error "alloc binding without G form"
    else
      match ctx.tabs.findIdx? (fun y => y.arena && strEq y.name an) with
      | .none => .error ("arena unknown: " ++ an)
      | .some num =>
        match ctx.tabs[num]? with
        | .none => .error "arena unknown"
        | .some tb =>
          match uWertBody ctx v with
          | .error err => .error err
          | .ok sv =>
            match uAnwReihe tabs koepfe f (uMitLokal ctx x (UParamArt.index num) (Ty.index tb.count)
                (ctx.muts.filter (fun m => !strEq m x))) rest with
            | .error err => .error err
            | .ok (xs, cE) => .ok ([UStmt.allocReqBeg x an sv] ++ xs, cE)
  | f + 1, ctx, .alloc .. :: _ => .error "alloc without else without G form"
  | f + 1, ctx, .allocVon mu x t tn :: rest =>
    match ctx.tabs.find? (fun y => strEq y.name tn) with
    | .some { von := .some p, .. } => uAnwReihe tabs koepfe f ctx (.bind mu x t (.call p []) :: rest)
    | _ => .error ("alloc of a table without provider: " ++ tn)
  | f + 1, ctx, .retry h (.block ss e) :: rest =>
    match uRetryKopf ctx h with
    | .error err => .error err
    | .ok (lab, cnt, bis, ueb) =>
      match uAnwReihe tabs koepfe f { ctx with loops := lab :: ctx.loops } ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uFoldEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          match uRuf ctx tabs koepfe ueb [] with
          | .error err => .error err
          | .ok (callee, xs) =>
            if !callee.ext then .error "on_exceeded names no foreign body"
            else
              match uAnwReihe tabs koepfe f ctx rest with
              | .error err => .error err
              | .ok (ys, cE) =>
                .ok ([UStmt.retryBeg cnt bis] ++ body ++ endS ++ [UStmt.ifElse, UStmt.axCall ueb xs, UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .loop h (.block ss e) :: rest =>
    match uForeverKopf ctx h with
    | .error err => .error err
    | .ok (lab, k) =>
      match uAnwReihe tabs koepfe f { ctx with loops := lab :: ctx.loops } ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uFoldEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          match uAnwReihe tabs koepfe f ctx rest with
          | .error err => .error err
          | .ok (ys, cE) => .ok ([UStmt.foreverBeg k] ++ body ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .trim (.variable x) t (.block ss e) :: rest =>
    match uNarrowKopf ctx x t with
    | .error err => .error err
    | .ok (lo, hi, ctx') =>
      match uAnwReihe tabs koepfe f ctx ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match (match e with
            | .none => .error "narrow else falls through"
            | .some _ => uFoldEndeStmt ctxB e : Except String (List UStmt)) with
        | .error err => .error err
        | .ok endS =>
          match uAnwReihe tabs koepfe f ctx' rest with
          | .error err => .error err
          | .ok (xs, cE) => .ok ([UStmt.narrowBeg x lo hi] ++ body ++ endS ++ [UStmt.blkEnd] ++ xs, cE)
  /- Required narrowing (C15, from `SAnw.trimReq`): the rest of the run reads
      `x` at the narrowed range; out of range is `Logik.kapazitaet`, so unlike
      `trim` there is no `else` and no `blkEnd`. -/
  | f + 1, ctx, .trimReq (.variable x) t :: rest =>
    match uNarrowKopf ctx x t with
    | .error err => .error err
    | .ok (lo, hi, ctx') =>
      match uAnwReihe tabs koepfe f ctx' rest with
      | .error err => .error err
      | .ok (xs, cE) => .ok ([UStmt.narrowReqBeg x lo hi] ++ xs, cE)
  | f + 1, ctx, .waive names body :: rest =>
    uBreaking (uAnwReihe tabs koepfe f) ctx names body rest
  | f + 1, ctx, .locks g lk (.block ss .none) :: rest =>
    if g then .error "shared lock without G form"
    else
      match lk with
      | .variable l =>
        match ctx.locks.find? (fun x => strEq x.name l) with
        | .none => .error ("lock unknown: " ++ l)
        | .some _ =>
          match uAnwReihe tabs koepfe f { ctx with held := l :: ctx.held } ss with
          | .error e => .error e
          | .ok (body, _) =>
            match uAnwReihe tabs koepfe f ctx rest with
            | .error e => .error e
            | .ok (xs, cE) => .ok ([UStmt.lockBeg l] ++ body ++ [UStmt.blkEnd] ++ xs, cE)
      | _ => .error "lock expression without G form"
  | f + 1, ctx, .cond c (.block ss e) ei els :: rest =>
    uCond (uAnwReihe tabs koepfe f) ctx c ss e ei els rest
  | f + 1, ctx, .each bnd o k s m raw inv (.block ss e) :: rest =>
    match uLoopExport ctx bnd o k s m raw inv with
    | .error err => .error err
    | .ok (header, ctxS, filter) =>
      match uAnwReihe tabs koepfe f ctxS ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uFoldEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          match uAnwReihe tabs koepfe f ctx rest with
          | .error err => .error err
          | .ok (xs, cE) =>
            .ok ([header] ++ uFilteredBody filter (body ++ endS) ++ [UStmt.blkEnd] ++ xs, cE)
  | f + 1, ctx, s :: rest =>
    match uAnw1 ctx tabs koepfe s with
    | .error e => .error e
    | .ok st =>
      match uAnwReihe tabs koepfe f ctx rest with
      | .error e => .error e
      | .ok (xs, cE) => .ok (st :: xs, cE)
termination_by fuel _ _ => (fuel, (0 : Nat))
decreasing_by all_goals exact Prod.Lex.left _ _ (by omega)
end

/-- Match dispatch supplies the same recursive reader and predecessor fuel to every arm. -/
theorem uAnwReiheCore_cases (tabs : List UTab) (koepfe : List UFnKopf) (fuel : Nat)
    (ctx : UCtx) (scrut : SExpr) (arms rest : List SAnw) :
    uAnwReiheCore tabs koepfe (fuel + 1) ctx (.cases scrut arms :: rest) =
      uCases (uAnwReihe tabs koepfe fuel) ctx scrut arms rest := by
  simp only [uAnwReiheCore]

/-- Fallible binding dispatch preserves all source shapes, including the refusal fallback. -/
theorem uAnwReiheCore_bindElse (tabs : List UTab) (koepfe : List UFnKopf) (fuel : Nat)
    (ctx : UCtx) (name : String) (ty : Option STyp) (value : SExpr) (reason : String)
    (body : SAnw) (rest : List SAnw) :
    uAnwReiheCore tabs koepfe (fuel + 1) ctx (.bindElse name ty value reason body :: rest) =
      uBindElse tabs koepfe (uAnwReihe tabs koepfe fuel) ctx name ty value reason body rest := by
  simp only [uAnwReiheCore]

/-- Conditional dispatch keeps its original body shape and recursive fuel budget. -/
theorem uAnwReiheCore_cond (tabs : List UTab) (koepfe : List UFnKopf) (fuel : Nat)
    (ctx : UCtx) (condition : SExpr) (statements : List SAnw) (ending : Option SEnde)
    (alternatives : List SAnw) (fallback : Option SAnw) (rest : List SAnw) :
    uAnwReiheCore tabs koepfe (fuel + 1) ctx
      (.cond condition (.block statements ending) alternatives fallback :: rest) =
      uCond (uAnwReihe tabs koepfe fuel) ctx condition statements ending alternatives fallback rest := by
  simp only [uAnwReiheCore]

end Gabbro.Grammatik.Parser.Uebersetze
