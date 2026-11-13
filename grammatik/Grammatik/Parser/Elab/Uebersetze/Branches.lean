module

public import Grammatik.Parser.Elab.Uebersetze.CallElse
public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardNarrowing
public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardRelation
public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardMutable
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Equality
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Match dispatch with the production reader as callback. Each arm and the continuation use
    the caller's unchanged fuel budget; bindings, end markers and failures retain source order. -/
def uCases
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (scrut : SExpr) (arms rest : List SAnw) : Except String (List UStmt × UCtx) :=
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
          match uSumPlatz ctx scrut with
          | .ok (_, num) => some ("#m", 1, num)
          | .error _ => none : Option (String × Nat × Nat)) with
    | .some (e, 1, num) =>
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
                      -- Payload types retain the extent, whereas kinds carry the table position.
                      -- Preserve canonical read-back when the compiler's switch is off.
                      | .opt count =>
                        if ctxM.narrow then
                          ((uOptionTabelle ctxM.tabs count).map UParamArt.opt).getD .wert
                        else uArtVon τ
                      | _ => uArtVon τ
                    some (uMitLokal ctxM k kind τ (ctxM.muts.filter (fun m => !strEq m k)), k)
                  | _, _ => none : Option (UCtx × String)) with
              | .none => .error "match arm payload without G form"
              | .some (cx, k) =>
                match run cx ss with
                | .error err => .error err
                | .ok (bd, ctxB) =>
                  match uFoldEndeStmt ctxB en with
                  | .error err => .error err
                  | .ok endS => .ok (k, bd ++ endS)
            | _ => .error "match arms without G form") with
        | .error err => .error err
        | .ok arme =>
          match run ctxM rest with
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
                match run ctx ss with
                | .error err => .error err
                | .ok (bd, ctxB) =>
                  match uFoldEndeStmt ctxB en with
                  | .error err => .error err
                  | .ok endS => .ok (bd ++ endS)
              | _ => .error "match arm without a block") with
          | .error err => .error err
          | .ok arme =>
            match run ctx rest with
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
        match run (uMitLokal ctx k (UParamArt.index num) (Ty.index tb.count)
            (ctx.muts.filter (fun m => !strEq m k))) sss with
        | .error err => .error err
        | .ok (sbody, ctxS) =>
          match uFoldEndeStmt ctxS se with
          | .error err => .error err
          | .ok sEnd =>
            match run ctx nss with
            | .error err => .error err
            | .ok (nbody, ctxN) =>
              match uFoldEndeStmt ctxN ne with
              | .error err => .error err
              | .ok nEnd =>
                match run ctx rest with
                | .error err => .error err
                | .ok (ys, cE) =>
                  .ok ([UStmt.matchBeg num o k] ++ sbody ++ sEnd ++ [UStmt.ifElse] ++ nbody ++ nEnd ++ [UStmt.blkEnd] ++ ys, cE)
      | _, _ => .error "match arms without G form"

/-- Fallible bindings retain their original field/call classification and reason scopes.
    Unsupported value or body shapes keep the dispatcher's original refusal. -/
def uBindElse (tabs : List UTab) (koepfe : List UFnKopf)
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (y : String) (t : Option STyp) (value : SExpr) (e : String)
    (body : SAnw) (rest : List SAnw) : Except String (List UStmt × UCtx) :=
  match value, body with
  | .field a r, .block ss en =>
    match uRegOrt ctx (.field a r) with
    | none => .error "let else without G form"
    | some (.error err) => .error err
    | some (.ok rg) =>
      if t.isSome then .error "let else with a type without G form"
      else if rg.pruefung.isNone then .error "let else of a register read without a promise to check"
      else
        match run ctx ss with
        | .error err => .error err
        | .ok (ebody, ctxEB) =>
          match uFoldEndeStmt ctxEB en with
          | .error err => .error err
          | .ok endS =>
            match run (uMitLokal ctx y rg.art rg.ty
                (ctx.muts.filter (fun m => !strEq m y))) rest with
            | .error err => .error err
            | .ok (ys, cE) => .ok ([UStmt.regReadElse y rg.dev rg.name] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | .call c args, .block ss en =>
    if t.isSome then .error "let else with a type without G form"
    else
      match uFnZeiger ctx koepfe c with
      | some (.error err) => .error err
      | some (.ok ziel) =>
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
                match run (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                    (ctx.muts.filter (fun m => !strEq m e))) ss with
                | .error err => .error err
                | .ok (ebody, ctxEB) =>
                  match uFoldEndeStmt ctxEB en with
                  | .error err => .error err
                  | .ok endS =>
                    match run (uMitLokal ctx y k ty (ctx.muts.filter (fun m => !strEq m y))) rest with
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
            -- A foreign answer is a number or a Boolean (`UFnKopf.axErg`).
            match (if callee.resBool then some (UParamArt.bool, Ty.bool)
                else callee.res.map fun r => (UParamArt.int, Ty.int r.1 r.2) : Option (UParamArt × Ty)) with
            | .none => .error "let else of a call without a value"
            | .some (k, ty) =>
              match run (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                  (ctx.muts.filter (fun m => !strEq m e))) ss with
              | .error err => .error err
              | .ok (ebody, ctxEB) =>
                match uFoldEndeStmt ctxEB en with
                | .error err => .error err
                | .ok endS =>
                  match run (uMitLokal ctx y k ty
                      (ctx.muts.filter (fun m => !strEq m y))) rest with
                  | .error err => .error err
                  | .ok (ys, cE) => .ok ([UStmt.bindAxElse y c xs e] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
          else
            match uWertArt callee with
            | .none => .error "let else of a call without a value"
            | .some (k, ty) =>
              match run (uMitLokal ctx e (UParamArt.why num) (Ty.why cnt)
                  (ctx.muts.filter (fun m => !strEq m e))) ss with
              | .error err => .error err
              | .ok (ebody, ctxEB) =>
                match uFoldEndeStmt ctxEB en with
                | .error err => .error err
                | .ok endS =>
                  match run (uMitLokal ctx y k ty (ctx.muts.filter (fun m => !strEq m y))) rest with
                  | .error err => .error err
                  | .ok (ys, cE) => .ok ([UStmt.bindElse y c xs e] ++ ebody ++ endS ++ [UStmt.blkEnd] ++ ys, cE)
  | _, _ => .error "let else without G form"

/-- Conditional branches share the same recursive reader and preserve the terminal-if test,
    lexical branch contexts, fold endings and continuation elaboration order. This is the reading of a
    condition that bounds no local (`uCond` calls it then, unchanged). -/
def uCondPlain
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (c : SExpr) (ss : List SAnw) (e : Option SEnde)
    (ei : List SAnw) (els : Option SAnw) (rest : List SAnw) : Except String (List UStmt × UCtx) :=
    match uBool ctx c with
    | .error err => .error err
    | .ok cv =>
      match run ctx ss with
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
                match run ctx ss2 with
                | .error err => .error err
                | .ok (b2, ctx2) =>
                  match uFoldEndeStmt ctx2 e2 with
                  | .error err => .error err
                  | .ok end2 => .ok (b2 ++ end2)
              | .some _ => .error "else without block" : Except String (List UStmt)) with
          | .error err => .error err
          | .ok elseS =>
            match run ctx rest with
            | .error err => .error err
            | .ok (xs, cE) =>
              let kopf := if rest.isEmpty && uEndetS 64 (.cond c (.block ss e) ei els) then UStmt.ifEnde cv
                else UStmt.ifBeg cv
              .ok ([kopf] ++ body ++ endS ++ [UStmt.ifElse] ++ elseS ++ [UStmt.blkEnd] ++ xs, cE)

/-- A condition that bounds immutable number locals (`uWaechterFakten`): each branch starts by rebinding the
    bounded locals it reads at the narrowed range, `let x : lo .. hi = <x narrowed>` (`USide.eng`, no `else`, no
    new return path), and elaborates in the context of the rebinding. The then branch gets the bounds of the
    condition (`thenF`), the `else` branch (an `else if` chain is the `if` in it) those of its negation
    (`elseF`); the continuation gets the negation (`postF`) only when the then branch always ends (a `return`,
    `leave` or `next` on every path), because it is then reached only where the condition failed. Everything
    else is `uCondPlain`: same order of elaboration, same fuel, same terminal-if test (a terminal `if` has no
    continuation).

    The relational facts of the condition (`uRelFakten`: `thenR`, `elseR`, `postR`, on the same paths as the
    bounds) are applied after the rebindings (`uRelBlock`): each block reads every difference of two locals the
    facts bound as a fresh local, bound once after the rebindings to the narrowed difference. The tests of
    `terminal` and `thenEnds` read the source as written.

    Mutable unary facts (`thenM`, `elseM`) instead use `uMutBlock`: a fresh immutable snapshot replaces only
    straight-line reads before assignment, including the value of the first plain assignment. These facts
    apply only to the then block and a plain else block, never an else-if chain or the continuation. -/
def uCondGuard
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (cv : UEns) (thenF elseF postF : List (String × Int × Int))
    (thenR elseR postR : List (String × String × Int))
    (thenM elseM : List (String × Int × Int))
    (c : SExpr) (ss : List SAnw) (e : Option SEnde)
    (ei : List SAnw) (els : Option SAnw) (rest : List SAnw) : Except String (List UStmt × UCtx) :=
    let (thenMB, ctxTM, ssM, eM) := uMutBlock ctx thenM ss e
    let (thenB, ctxT0) := uWaechterBinde ctxTM thenF
    let (thenRB, ctxT, ssT, eT) := uRelBlock ctxT0 thenR ssM eM
    match run ctxT ssT with
    | .error err => .error err
    | .ok (body, ctxB) =>
      match uFoldEndeStmt ctxB eT with
      | .error err => .error err
      | .ok endS =>
        let ifElse : Option SAnw :=
          match ei with
          | .elsif c2 b2 :: ei' => some (.block [.cond c2 b2 ei' els] .none)
          | _ => els
        match (match ifElse with
            | .none => .ok []
            | .some (.block ss2 e2) =>
              let (elseMB, ctxEM, ss2M, e2M) := uMutBlock ctx elseM ss2 e2
              let (elseB, ctxE0) := uWaechterBinde ctxEM elseF
              let (elseRB, ctxE, ss2', e2') := uRelBlock ctxE0 elseR ss2M e2M
              match run ctxE ss2' with
              | .error err => .error err
              | .ok (b2, ctx2) =>
                match uFoldEndeStmt ctx2 e2' with
                | .error err => .error err
                | .ok end2 => .ok (elseMB ++ elseB ++ elseRB ++ b2 ++ end2)
            | .some _ => .error "else without block" : Except String (List UStmt)) with
        | .error err => .error err
        | .ok elseS =>
          let terminal := rest.isEmpty && uEndetS 64 (.cond c (.block ss e) ei els)
          let thenEnds := e.isSome || (match ss.getLast? with | some s => uEndetTief 64 s | none => false)
          let (post, ctxR0) : List UStmt × UCtx :=
            if thenEnds && !terminal then uWaechterBinde ctx postF else ([], ctx)
          let (postRB, ctxR, restR, _) : List UStmt × UCtx × List SAnw × Option SEnde :=
            if thenEnds && !terminal then uRelBlock ctxR0 postR rest none else ([], ctxR0, rest, none)
          match run ctxR restR with
          | .error err => .error err
          | .ok (xs, cE) =>
            let kopf := if terminal then UStmt.ifEnde cv else UStmt.ifBeg cv
            .ok ([kopf] ++ thenMB ++ thenB ++ thenRB ++ body ++ endS ++ [UStmt.ifElse] ++ elseS ++ [UStmt.blkEnd] ++ post ++
              postRB ++ xs, cE)

/-- Conditional branches. With narrowing off (`ctx.narrow = false`, the default: the canonical exporter and
    every statement about the elaborator's read-back) a condition is read by `uCondPlain`. With narrowing on (the
    Stage-0 compiler, `Stage0.Frontend.elabExpanded`) the facts of the condition (`uWaechterFakten`) are kept
    for the locals each block reads (`uWaechterGelesen`: the then block with its ending, the `else` block or
    `else if` chain, the continuation), and so are its relational facts between two such locals (`uRelFakten`);
    mutable unary facts (`uMutFakten`) apply only within a then or plain else block. A condition with no facts
    is read exactly as before (`uCondPlain`), one with any by `uCondGuard`. -/
def uCond
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (c : SExpr) (ss : List SAnw) (e : Option SEnde)
    (ei : List SAnw) (els : Option SAnw) (rest : List SAnw) : Except String (List UStmt × UCtx) :=
    if ctx.narrow then
      let fallback := match ei with
        | .elsif c2 b2 :: ei' => SAnw.block [.cond c2 b2 ei' els] none
        | _ => els.getD (.block [] none)
      match uTaggedEquality ctx c (.block ss e) fallback with
      | .error err => .error err
      | .ok (some expanded) => run ctx (expanded :: rest)
      | .ok none =>
        match uBool ctx c with
        | .error err => .error err
        | .ok cv =>
          let negated := uWaechterFakten ctx cv false
          let thenF := uWaechterGelesen (uLiestL (ss ++ [.block [] e])) (uWaechterFakten ctx cv true)
          let elseF := uWaechterGelesen (uLiestL (ei ++ els.toList)) negated
          -- The continuation ends with the ending of the enclosing block, which is not in `rest`:
          -- its facts are kept whenever the then block always ends.
          let thenEnds := e.isSome || (match ss.getLast? with | some s => uEndetTief 64 s | none => false)
          let postF := if thenEnds then negated else []
          -- The relational facts (`uRelFakten`) on the same paths; the continuation's only when the then block
          -- always ends.
          let thenR := uRelFakten ctx cv true
          let elseR := uRelFakten ctx cv false
          let postR := if thenEnds then elseR else []
          let thenM := uMutFakten ctx cv true
          let elseM : List (String × Int × Int) := match ei, els with
            | [], some (.block ..) => uMutFakten ctx cv false
            | _, _ => []
          match thenF, elseF, postF, thenR ++ elseR, thenM ++ elseM with
          | [], [], [], [], [] => uCondPlain run ctx c ss e ei els rest
          | thenF, elseF, postF, _, _ =>
            uCondGuard run ctx cv thenF elseF postF thenR elseR postR thenM elseM c ss e ei els rest
    else uCondPlain run ctx c ss e ei els rest

/-- With the compiler's switch on, an equality of two tagged values is read as its complete
    expansion into matches, through the ordinary checked reader. -/
theorem uCond_tagged
    (run : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (c : SExpr) (ss : List SAnw) (e : Option SEnde)
    (ei : List SAnw) (els : Option SAnw) (rest : List SAnw) (expanded : SAnw)
    (an : ctx.narrow = true)
    (selected : uTaggedEquality ctx c (.block ss e)
      (match ei with
       | .elsif c2 b2 :: ei' => SAnw.block [.cond c2 b2 ei' els] none
       | _ => els.getD (.block [] none)) = .ok (some expanded)) :
    uCond run ctx c ss e ei els rest = run ctx (expanded :: rest) := by
  simp only [uCond, an, ↓reduceIte, selected]

end Gabbro.Grammatik.Parser.Uebersetze
