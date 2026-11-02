module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
public import Grammatik.Parser.Elab.Uebersetze.Folds.Substitution

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

mutual
/-- Expand expression folds before processing the ordinary statement forms. -/
def uAnwReihe (tabs : List UTab) (koepfe : List UFnKopf) :
    Nat → UCtx → List SAnw → Except String (List UStmt × UCtx)
  | 0, _, _ => .error "nesting without G form"
  | _ + 1, ctx, [] => .ok ([], ctx)
  | fuel + 1, ctx, statement :: rest => do
    let (prefix, ctx, statement) ← expandFoldStmt ctx statement
    let (code, ctx) ← uAnwReiheCore tabs koepfe fuel ctx (statement :: rest)
    pure (prefix ++ code, ctx)

/-- A run of body statements as a flat list. A `let` extends the context for the rest of the run;
    `locks L { ... }` elaborates its body with `L` HELD (guards, calls) and the bindings made inside it
    end with it; a shared hold, a `return` inside the block and every other lock expression are refused.
    Structural in a fuel (one unit per statement and per block). -/
def uAnwReiheCore (tabs : List UTab) (koepfe : List UFnKopf) :
    Nat → UCtx → List SAnw → Except String (List UStmt × UCtx)
  | 0, _, _ => .error "nesting without G form"
  | _ + 1, ctx, [] => .ok ([], ctx)
  | _ + 1, _, .lcall .. :: _ | _ + 1, _, .bindLib .. :: _ =>
      -- Unexpanded library calls never arrive here through `elabU`: `exportLibraryUnit` expands
      -- them into ordinary calls before the lowering runs. This guard stays for direct callers.
      .error "C02: library call needs certified immutable payload initialization and ordinary call expansion"
  | f + 1, ctx, .bind mu x t e :: rest =>
    match uBindWert ctx tabs koepfe mu x t e with
    | .error err => .error err
    | .ok (st, ctx') =>
      let ctx' := foldBindingContext ctx ctx' st
      match uAnwReihe tabs koepfe f ctx' rest with
      | .error err => .error err
      | .ok (xs, cE) => .ok (st :: xs, cE)
  | f + 1, ctx, .cases scrut arms :: rest =>
    match (match scrut with
        | .variable e =>
          match uParamNr ctx e with
          | .ok j =>
            match uArtBei ctx.kinds j with
            | .ok (.why num) => some (e, 0, num)
            | .ok (.sum num) => some (e, 1, num)
            | _ => none
          | .error _ =>
            (ctx.globs.find? (fun g => strEq g.name e)).bind fun g => g.sumNum.map fun num => (e, 1, num)
        | _ =>
          -- a field of a tagged type: bound to the hidden local `#m` first (`uSumPlatz`)
          match uSumPlatz ctx scrut with
          | .ok (_, num) => some ("#m", 1, num)
          | .error _ => none : Option (String × Nat × Nat)) with
    | .some (e, 1, num) =>
      -- a field of a tagged type is bound to `#m` first; the arms and the rest see it
      let (ctxM, vor) : UCtx × List UStmt :=
        match (if strEq e "#m" then (uSumPlatz ctx scrut).toOption else none), ctx.sums[num]? with
        | some (sv, _), some sm =>
          (uMitLokal ctx "#m" (UParamArt.sum num) (Ty.sum sm.spec) ctx.muts, [UStmt.bindSum "#m" num sv])
        | _, _ => (ctx, [])
      match ctxM.sums[num]? with
      | .none => .error "tagged type unknown"
      | .some sm =>
        if arms.length != sm.cases.length then .error "match arms without G form"
        else
        match uSeq (sm.cases.map fun (cn, pl) =>
            match arms.find? (fun a => match a with | .arm n _ _ => strEq n cn | _ => false) with
            | .some (.arm _ bnd (.block ss en)) =>
              match (match pl, bnd with
                  | .none, .none => some (ctxM, "")
                  | .some τ, .some k =>
                    let kind := match τ with
                      | .bool => UParamArt.bool
                      | .ref n => UParamArt.ref n
                      | .sum cs => ((ctxM.sums.findIdx? (fun s => s.spec = cs)).map UParamArt.sum).getD .wert
                      | _ => uArtVon τ
                    some (uMitLokal ctxM k kind τ (ctxM.muts.filter (fun m => !strEq m k)), k)
                  | _, _ => none : Option (UCtx × String)) with
              | .none => .error "match arm payload without G form"
              | .some (cx, k) =>
                match uAnwReihe tabs koepfe f cx ss with
                | .error err => .error err
                | .ok (bd, ctxB) =>
                  match uFoldEndeStmt ctxB en with
                  | .error err => .error err
                  | .ok endS => .ok (k, bd ++ endS)
            | _ => .error "match arms without G form") with
        | .error err => .error err
        | .ok arme =>
          match uAnwReihe tabs koepfe f ctxM rest with
          | .error err => .error err
          | .ok (ys, cE) =>
            .ok (vor ++ [UStmt.matchTagBeg num e (arme.map (·.1))] ++ uMitTrenner (arme.map (·.2)) ++ [UStmt.blkEnd] ++ ys, cE)
    | .some (e, _, num) =>
      match ctx.whys[num]? with
      | .none => .error "reason unknown"
      | .some w =>
        match uWhyArme w.cases arms with
        | .none => .error "match arms without G form"
        | .some bodies =>
          match uSeq (bodies.map fun b =>
              match b with
              | .block ss en =>
                match uAnwReihe tabs koepfe f ctx ss with
                | .error err => .error err
                | .ok (bd, ctxB) =>
                  match uFoldEndeStmt ctxB en with
                  | .error err => .error err
                  | .ok endS => .ok (bd ++ endS)
              | _ => .error "match arm without a block") with
          | .error err => .error err
          | .ok arme =>
            match uAnwReihe tabs koepfe f ctx rest with
            | .error err => .error err
            | .ok (ys, cE) => .ok ([UStmt.matchWhyBeg e] ++ uMitTrenner arme ++ [UStmt.blkEnd] ++ ys, cE)
    | .none =>
    match uOptEin ctx scrut with
    | .error err => .error (if uPraemisse err then err else "stmt without G form")
    | .ok (o, num) =>
      match ctx.tabs[num]?, (match arms with
          | [.arm "Some" (.some k) sb, .arm "None" .none nb] => some (k, sb, nb)
          | [.arm "None" .none nb, .arm "Some" (.some k) sb] => some (k, sb, nb)
          | _ => none) with
      | .some tb, .some (k, .block sss se, .block nss ne) =>
        match uAnwReihe tabs koepfe f (uMitLokal ctx k (UParamArt.index num) (Ty.index tb.count)
            (ctx.muts.filter (fun m => !strEq m k))) sss with
        | .error err => .error err
        | .ok (sbody, ctxS) =>
          match uFoldEndeStmt ctxS se with
          | .error err => .error err
          | .ok sEnd =>
            match uAnwReihe tabs koepfe f ctx nss with
            | .error err => .error err
            | .ok (nbody, ctxN) =>
              match uFoldEndeStmt ctxN ne with
              | .error err => .error err
              | .ok nEnd =>
                match uAnwReihe tabs koepfe f ctx rest with
                | .error err => .error err
                | .ok (ys, cE) =>
                  .ok ([UStmt.matchBeg num o k] ++ sbody ++ sEnd ++ [UStmt.ifElse] ++ nbody ++ nEnd ++ [UStmt.blkEnd] ++ ys, cE)
      | _, _ => .error "match arms without G form"
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
              -- each arm reads `v` narrowed by its guard and the negated guards before it
              let zs := (List.range zs0.length).zip zs0 |>.map (fun (i, (c, e)) =>
                (c, uArmEng ctxV v lo hi (some c) ((zs0.take i).map (·.1)) e))
              let neu := uArmEng ctxV v lo hi none (zs0.map (·.1)) neu0
              -- `awaits` at an exchange: the acquiring read of `Block.awaits` (its value unused) in front
              let vor := if aw.isSome then [UStmt.awaitBind "#awaits" a] else []
              match vergleich with
              | none =>
                let ctx' := uMitLokal ctx x UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m x))
                match uAnwReihe tabs koepfe f ctx' rest with
                | .error err => .error err
                | .ok (xs, cE) => .ok (vor ++ UStmt.tausch x a v zs neu :: xs, cE)
              | some p =>
                -- compare-exchange: the old value is `#alt`, the binder `x` is the success `p`
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
  | f + 1, ctx, .bindElse y t (.field a r) _ (.block ss en) :: rest =>
    match uRegOrt ctx (.field a r) with
    | none => .error "let else without G form"
    | some (.error err) => .error err
    | some (.ok rg) =>
      if t.isSome then .error "let else with a type without G form"
      else if rg.pruefung.isNone then .error "let else of a register read without a promise to check"
      else
        match uAnwReihe tabs koepfe f ctx ss with
        | .error err => .error err
        | .ok (ebody, ctxEB) =>
          match uFoldEndeStmt ctxEB en with
          | .error err => .error err
          | .ok endS =>
            match uAnwReihe tabs koepfe f (uMitLokal ctx y rg.art rg.ty
                (ctx.muts.filter (fun m => !strEq m y))) rest with
            | .error err => .error err
            | .ok (ys, cE) => .ok ([UStmt.regReadElse y rg.dev rg.name] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .bindElse y t (.call c args) e (.block ss en) :: rest =>
    if t.isSome then .error "let else with a type without G form"
    else
      match uFnZeiger ctx koepfe c with
      | some (.error err) => .error err
      | some (.ok ziel) =>
        -- a `let .. else` through a function-pointer local («C07»): the reason channel is the
        -- pointer type's (`ziel`), never a direct target's; a foreign head has no indirect form.
        match uRuf ctx tabs koepfe ziel.name args with
        | .error err => .error err
        | .ok (callee, xs) =>
          match callee.kanal with
          | .none => .error "let else of a call without a reason channel"
          | .some (num, cnt) =>
            if callee.ext then .error "let else of an indirect call without G form"
            else
              match uWertArt callee with
              | .none => .error "let else of a call without a value"
              | .some (k, ty) =>
                match uAnwReihe tabs koepfe f (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                    (ctx.muts.filter (fun m => !strEq m e))) ss with
                | .error err => .error err
                | .ok (ebody, ctxEB) =>
                  match uFoldEndeStmt ctxEB en with
                  | .error err => .error err
                  | .ok endS =>
                    match uAnwReihe tabs koepfe f (uMitLokal ctx y k ty (ctx.muts.filter (fun m => !strEq m y))) rest with
                    | .error err => .error err
                    | .ok (ys, cE) => .ok ([UStmt.bindCallIndElse y c ziel.name xs e] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
      | none =>
       match uRuf ctx tabs koepfe c args with
      | .error err => .error err
      | .ok (callee, xs) =>
        match callee.kanal with
        | .none => .error "let else of a call without a reason channel"
        | .some (num, cnt) =>
          if callee.ext then
            match callee.res with
            | .none => .error "let else of a call without a value"
            | .some r =>
              match uAnwReihe tabs koepfe f (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                  (ctx.muts.filter (fun m => !strEq m e))) ss with
              | .error err => .error err
              | .ok (ebody, ctxEB) =>
                match uFoldEndeStmt ctxEB en with
                | .error err => .error err
                | .ok endS =>
                  match uAnwReihe tabs koepfe f (uMitLokal ctx y UParamArt.int (Ty.int r.1 r.2)
                      (ctx.muts.filter (fun m => !strEq m y))) rest with
                  | .error err => .error err
                  | .ok (ys, cE) => .ok ([UStmt.bindAxElse y c xs e] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
          else
            match uWertArt callee with
            | .none => .error "let else of a call without a value"
            | .some (k, ty) =>
              match uAnwReihe tabs koepfe f (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                  (ctx.muts.filter (fun m => !strEq m e))) ss with
              | .error err => .error err
              | .ok (ebody, ctxEB) =>
                match uFoldEndeStmt ctxEB en with
                | .error err => .error err
                | .ok endS =>
                  match uAnwReihe tabs koepfe f (uMitLokal ctx y k ty (ctx.muts.filter (fun m => !strEq m y))) rest with
                  | .error err => .error err
                  | .ok (ys, cE) => .ok ([UStmt.bindElse y c xs e] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | f + 1, ctx, .bindElse .. :: _ => .error "let else without G form"
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
    -- `let r = alloc T;` is the call of `T`'s provider (`Block.alloc`, Zucker.lean): `let r = p();`
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
  | _ + 1, _, .waive .. :: _ =>
    .error "source export: invariant cost/runs/by duties lack a checked source binding"
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
    match uBool ctx c with
    | .error err => .error err
    | .ok cv =>
      match uAnwReihe tabs koepfe f ctx ss with
      | .error err => .error err
      | .ok (body, ctxB) =>
        match uFoldEndeStmt ctxB e with
        | .error err => .error err
        | .ok endS =>
          let ifElse : Option SAnw :=
            match ei with
            | .elsif c2 b2 :: ei' => some (.block [.cond c2 b2 ei' els] .none)
            | _ => els
          match (match ifElse with
              | .none => .ok []
              | .some (.block ss2 e2) =>
                match uAnwReihe tabs koepfe f ctx ss2 with
                | .error err => .error err
                | .ok (b2, ctx2) =>
                  match uFoldEndeStmt ctx2 e2 with
                  | .error err => .error err
                  | .ok end2 => .ok (b2 ++ end2)
              | .some _ => .error "else without block" : Except String (List UStmt)) with
          | .error err => .error err
          | .ok elseS =>
            match uAnwReihe tabs koepfe f ctx rest with
            | .error err => .error err
            | .ok (xs, cE) =>
              let kopf := if rest.isEmpty && uEndetS 64 (.cond c (.block ss e) ei els) then UStmt.ifEnde cv
                else UStmt.ifBeg cv
              .ok ([kopf] ++ body ++ endS ++ [UStmt.ifElse] ++ elseS ++ [UStmt.blkEnd] ++ xs, cE)
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

end

end Gabbro.Grammatik.Parser.Uebersetze
