module

public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.Kopf

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- The `else` branch of a narrowing as an end block: its statements and the ender (`return`, `leave`, `next`),
    which must not fall through; the marker `blkEnd` that closes the branch is left to the caller. -/
def lowEndStep {l : Bool} (u : UProg) (caller : Fin u.fns.length) (R : LowStufe u caller) :
    (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String (Endblock (declOf u) (verOf u caller) l Γ Λ × List UStmt)
  | _, _, _, _, [] => .error "lower: an else branch falls through"
  | _, _, _, _, .blkEnd :: _ => .error "lower: an else branch falls through"
  | _, _, _, _, .ifElse :: _ => .error "lower: an else branch falls through"
  | Γ, fn, Λ, pe, .ret v :: rest => match pe with
    | none => .error "lower: return under locks has no G form"
    | some _ => match v with
      | .why i =>
        if hi : i < (verOf u caller).gruende then
          if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
            .ok (Endblock.retWhy (D := declOf u) ⟨i, hi⟩ (of_decide_eq_true hPerm), rest)
          else .error "lower: return without produced marks"
        else .error "reason case outside the channel"
      | _ =>
      (lowErg u caller Γ Λ fn v).bind fun erg =>
        if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
          .ok (Endblock.ret erg (of_decide_eq_true hPerm), rest)
        else .error "lower: return without produced marks"
  | _, _, _, _, .leave _ :: rest =>
    if h : l = true then .ok (Endblock.leave h, rest) else .error "lower: leave outside a traverse"
  | _, _, _, _, .next _ :: rest =>
    if h : l = true then .ok (Endblock.next h, rest) else .error "lower: next outside a traverse"
  | Γ, fn, Λ, pe, .axCallElseBeg c args reason :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.axCallElseBeg c args reason) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .breakingBeg name :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.breakingBeg name) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .bind x d v :: rest =>
    (lowBindWert u Γ Λ fn d v).bind fun s =>
      (R.ende (l := l) (.int s.range.1 s.range.2 :: Γ) (fn.mitBindung x s.range) Λ pe rest).bind fun (b, r) => .ok (Endblock.bind s.term b, r)
  | Γ, fn, Λ, pe, .bindW x d v :: rest =>
    (lowBindW u Γ Λ fn d v).bind fun w =>
      (R.ende (l := l) (w.ty :: Γ) (fn.mitWert x w.ty) Λ pe rest).bind fun (b, r) => .ok (Endblock.bind w.term b, r)
  | Γ, fn, Λ, pe, .floatLit x q lo hi :: rest => do
    let (body, remaining) ← R.ende (l := l) (.fl lo hi :: Γ) (fn.mitWert x (.fl lo hi)) Λ pe rest
    pure (Endblock.floatLit q lo hi body, remaining)
  | Γ, fn, Λ, pe, .float x op a b lo hi :: rest => do
    let ⟨.fl _ _, left⟩ ← lowWertE u Γ Λ fn none a | .error "float: left operand is not a float"
    let ⟨.fl _ _, right⟩ ← lowWertE u Γ Λ fn none b | .error "float: right operand is not a float"
    let (body, remaining) ← R.ende (l := l) (.fl lo hi :: Γ) (fn.mitWert x (.fl lo hi)) Λ pe rest
    pure (Endblock.float op left right lo hi body, remaining)
  | Γ, fn, Λ, pe, .bindB x v :: rest =>
    (lowEns u Γ Λ fn none v).bind fun ev =>
      (R.ende (l := l) (.bool :: Γ) (fn.mitBindungB x) Λ pe rest).bind fun (b, r) => .ok (Endblock.bind ev b, r)
  | Γ, fn, Λ, pe, .bindMut x lo hi v :: rest =>
    (lowWertAt u Γ Λ fn lo hi v).bind fun ev =>
      (R.ende (l := l) (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) Λ pe rest).bind fun (b, r) => .ok (Endblock.bind ev b, r)
  | Γ, fn, Λ, pe, .bindCall x cname args :: rest =>
    (lowRufKopf u caller Γ fn Λ cname args).bind fun k =>
      withErg u k.callee fun τ hE =>
        (R.ende (l := l) (τ :: Γ) (fn.mitTy x τ) (nach (declOf u) k.callee Λ) pe rest).bind fun (b, r) =>
          if hr : (declOf u).gruende k.callee = 0 then
            .ok (Endblock.bindCall (D := declOf u) k.callee k.args hE k.hp hr b, r)
          else .error "call of a function with a reason channel needs `let .. else`"
  | _, _, _, _, .axCall .. :: _ => .error "lower: a foreign call in an else branch has no G form here"
  | _, _, _, _, .bindAx .. :: _ => .error "lower: a foreign call in an else branch has no G form here"
  | Γ, fn, Λ, pe, .narrowBeg x lo hi :: rest =>
    (paramPos fn.params x).bind fun j => match fn.params[j]? with
      | some (_, .int l1 h1) =>
        (lowVar Γ j (.int l1 h1)).bind fun v => match R.ende (l := l) Γ fn Λ pe rest with
          | .error e => .error e
          | .ok (sonst, .blkEnd :: rest') =>
            (R.ende (l := l) (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) Λ pe rest').bind fun (b, r) => .ok (Endblock.narrow (D := declOf u) (Expr.var v) lo hi sonst b, r)
          | .ok (_, _) => .error "lower: a narrow is not closed"
      | _ => .error "lower: narrow of a non-number"
  /-- Required narrowing at the top level of a body (C15): no `else`, no
      `blkEnd`; out of range is `Logik.kapazitaet`
      (`Endblock.narrowRequired`). -/
  | Γ, fn, Λ, pe, .narrowReqBeg x lo hi :: rest =>
    (paramPos fn.params x).bind fun j => match fn.params[j]? with
      | some (_, .int l1 h1) =>
        (lowVar Γ j (.int l1 h1)).bind fun v =>
          (R.ende (l := l) (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) Λ pe rest).bind fun (b, r) => .ok (Endblock.narrowRequired (D := declOf u) (Expr.var v) lo hi b, r)
      | _ => .error "lower: narrow of a non-number"
  | Γ, fn, Λ, pe, .bindFnref x f m :: rest =>
    (fnIdx u.fns f).bind fun g =>
      if h : (declOf u).passt g m = true then
        (R.ende (l := l) (Ty.fnptr m :: Γ) (fn.mitFnptr x m) Λ pe rest).bind fun (b, r') => .ok (Endblock.bind (Expr.fnref (D := declOf u) g m h) b, r')
      else .error "function does not conform to the pointer type"
  | Γ, fn, Λ, pe, .bindCallInd x p _ args :: rest =>
    (lowZeigerN u Γ fn p).bind fun ⟨m, v⟩ =>
      (lowRufKopfN u caller Γ fn Λ m args).bind fun k =>
        withErgN u m fun τ hE =>
          (R.ende (l := l) (τ :: Γ) (fn.mitTy x τ) (nachSig (declOf u) ((declOf u).sigNr m) Λ) pe rest).bind fun (b, r') =>
            if hr : ((declOf u).sigNr m).gruende = 0 then
              .ok (Endblock.bindCallInd (D := declOf u) (n := m) (Expr.var v) k.args hE k.hp hr b, r')
            else .error "call of a function with a reason channel needs `let .. else`"
  | Γ, fn, Λ, pe, .bindCallIndElse y p _ args e :: rest => do
    u.exportGate
    match lowZeigerN u Γ fn p with
    | .error err => .error err
    | .ok ⟨m, v⟩ =>
      match lowRufKopfN u caller Γ fn Λ m args with
      | .error err => .error err
      | .ok k =>
        if hr : 0 < ((declOf u).sigNr m).gruende then
          withErgN u m fun τ hE =>
            match R.ende (l := l) (Ty.why (((declOf u).sigNr m).gruende) :: Γ) (fn.mitWhy e 0 (((declOf u).sigNr m).gruende)) (nachSig (declOf u) ((declOf u).sigNr m) Λ) pe rest with
            | .error err => .error err
            | .ok (errb, .blkEnd :: tail) => match R.ende (l := l) (τ :: Γ) (fn.mitTy y τ) (nachSig (declOf u) ((declOf u).sigNr m) Λ) pe tail with
              | .error err => .error err
              | .ok (body, remaining) => .ok (nestedElseN u caller Γ Λ m v k τ hE hr errb body, remaining)
            | .ok (_, _) => .error "lower: a let else is not closed"
        else .error "lower: let else of a call without a reason channel"
  | Γ, fn, Λ, pe, .tausch x a v zweige neu :: rest =>
    (globIdx u.globs a).bind fun g => if hw : (verOf u caller).gschreibt g = true then
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        (lowTauschNeu u ((declOf u).gtyp g :: Γ) Λ (fn.mitTy v ((declOf u).gtyp g)) ((declOf u).gtyp g) zweige neu).bind fun ne =>
          (R.ende (l := l) ((declOf u).gtyp g :: Γ) (fn.mitTy x ((declOf u).gtyp g)) Λ pe rest).bind fun (b, r') => .ok (Endblock.exchange (D := declOf u) g ne hw hd b, r')
      else .error "access without held guard"
      else .error "exchange of a static the function does not write"
  | Γ, fn, Λ, pe, .awaitBind x a :: rest =>
    (globIdx u.globs a).bind fun g => if ha : (declOf u).atomar g = true then
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        (R.ende (l := l) ((declOf u).gtyp g :: Γ) (fn.mitTy x ((declOf u).gtyp g)) Λ pe rest).bind fun (b, r') => .ok (Endblock.awaits (D := declOf u) g ((declOf u).nutzlast g) rfl hd ha b, r')
      else .error "access without held guard"
      else .error "awaits at a static that is not atomic"
  | Γ, fn, Λ, pe, .regRead x d rg :: rest =>
    (regIdx u.regs d rg).bind fun g =>
      if hk : ((declOf u).rklasse g).lesbar = true then
        (R.ende (l := l) ((regAt u g).ty :: Γ) (fn.mitTy x (regAt u g).ty) Λ pe rest).bind fun (b, r') => .ok (Endblock.regRead (D := declOf u) g hk b, r')
      else .error "lower: register read against its class"
  | Γ, fn, Λ, pe, .regReadElse x d rg :: rest =>
    (regIdx u.regs d rg).bind fun g =>
      if hk : ((declOf u).rklasse g).lesbar = true then match (regAt u g).pruefung with
        | none => .error "lower: register read without a check"
        | some p =>
          (lowEns u ((regAt u g).ty :: Γ) Λ (fn.mitTy (regAt u g).name (regAt u g).ty) none p).bind fun zu =>
            match R.ende (l := l) Γ fn Λ pe rest with
            | .error e => .error e
            | .ok (sonst, .blkEnd :: rest') =>
              (R.ende (l := l) ((regAt u g).ty :: Γ) (fn.mitTy x (regAt u g).ty) Λ pe rest').bind fun (b, r') => .ok (Endblock.regReadElse (D := declOf u) g hk zu sonst b, r')
            | .ok (_, _) => .error "lower: a let else is not closed"
      else .error "lower: register read against its class"
  | Γ, fn, Λ, pe, .allocBeg x an v :: rest =>
    (tabIdx u.tabs an).bind fun t =>
      (globIdx u.globs (an ++ "#used")).bind fun g =>
        (fieldHit u t "wert").bind fun fh =>
          (lowWertAt u Γ Λ fn fh.range.1 fh.range.2 v).bind fun ev0 =>
            match R.ende (l := l) Γ fn Λ pe rest with
            | .error e => .error e
            | .ok (voll, .blkEnd :: rest') =>
              match R.ende (l := l) (Ty.index ((declOf u).count t) :: Γ) (fn.mitIndex x t.val ((declOf u).count t)) Λ pe rest' with
              | .error e => .error e
              | .ok (b, r) => (mkAllocEndBlock u caller Γ Λ t g fh ev0 voll b).bind fun blk => .ok (blk, r)
            | .ok (_, _) => .error "lower: an alloc is not closed"
  | Γ, fn, Λ, pe, .bindOptBeg x c args :: rest =>
    (lowAxKopf u caller Γ fn Λ c args).bind fun k =>
      if hp : rufPasstB u (verOf u caller) ((declOf u).asignatur k.ax) Λ = true then
        let fn' := match (declOf u).aerg k.ax with
          | none => fn
          | some τ => fn.mitTy x τ
        (R.ende (l := l) (ErgCtx Γ ((declOf u).aerg k.ax)) fn' (nachSig (declOf u) ((declOf u).asignatur k.ax) Λ) pe rest).bind fun (b, r) =>
          .ok (Endblock.bindAxiomOpt (e := (declOf u).aerg k.ax) k.ax k.args rfl
            (rufPasstB_ok hp) k.hd k.hgd b, r)
      else .error "foreign call does not conform to caller contract"
  | Γ, fn, Λ, pe, .bindOptElseBeg x c args e :: rest =>
    (lowAxKopf u caller Γ fn Λ c args).bind fun k =>
      if hp : rufPasstB u (verOf u caller) ((declOf u).asignatur k.ax) Λ = true then
        let fn' := match (declOf u).aerg k.ax with
          | none => fn
          | some τ => fn.mitTy x τ
        if hr : 0 < (declOf u).agruende k.ax then
          match R.ende (l := l) (reasonTy ((declOf u).agruende k.ax) :: Γ)
              (fn.mitWhy e 0 ((declOf u).agruende k.ax)) (nachSig (declOf u) ((declOf u).asignatur k.ax) Λ) pe rest with
          | .error err => .error err
          | .ok (errb, .blkEnd :: tail) =>
            (R.ende (l := l) (ErgCtx Γ ((declOf u).aerg k.ax)) fn' (nachSig (declOf u) ((declOf u).asignatur k.ax) Λ) pe tail).bind fun (b, r) =>
              .ok (Endblock.bindAxiomOptElse (e := (declOf u).aerg k.ax) k.ax k.args rfl
                (rufPasstB_ok hp) k.hd k.hgd hr errb b, r)
          | .ok (_, _) => .error "lower: a let else is not closed"
        else .error "lower: let else of a foreign call without a reason channel"
      else .error "foreign call does not conform to caller contract"
  | Γ, fn, Λ, pe, .allocReqBeg x an v :: rest =>
    (tabIdx u.tabs an).bind fun t =>
      (globIdx u.globs (an ++ "#used")).bind fun g =>
        (fieldHit u t "wert").bind fun fh =>
          (lowWertAt u Γ Λ fn fh.range.1 fh.range.2 v).bind fun ev0 =>
            match R.ende (l := l) (Ty.index ((declOf u).count t) :: Γ) (fn.mitIndex x t.val ((declOf u).count t)) Λ pe rest with
            | .error e => .error e
            | .ok (b, r) => (mkAllocRequiredEndBlock u caller Γ Λ t g fh ev0 b).bind fun blk => .ok (blk, r)
  | Γ, fn, Λ, pe, .bindAxElse y c args e :: rest => match lowAxKopf u caller Γ fn Λ c args with
    | .error err => .error err
    | .ok k =>
      if hr : 0 < (declOf u).agruende k.ax then
        withAxErg u k.ax (fun _ => .error "call without a value") fun τ hE =>
          match R.ende (l := l) (Ty.why ((declOf u).agruende k.ax) :: Γ) (fn.mitWhy e 0 ((declOf u).agruende k.ax)) Λ pe [] with
          | _ => .error "lower: a let else in an else branch has no G form here"
      else .error "lower: let else of a foreign call without a reason channel"
  | Γ, fn, Λ, pe, .bindElse y c args e :: rest => do
    u.exportGate
    match lowRufKopf u caller Γ fn Λ c args with
    | .error err => .error err
    | .ok k =>
      if hr : 0 < (declOf u).gruende k.callee then
        withErg u k.callee fun τ hE =>
          match R.ende (l := l) (Ty.why ((declOf u).gruende k.callee) :: Γ) (fn.mitWhy e 0 ((declOf u).gruende k.callee)) (nach (declOf u) k.callee Λ) pe rest with
          | .error err => .error err
          | .ok (errb, .blkEnd :: tail) => match R.ende (l := l) (τ :: Γ) (fn.mitTy y τ) (nach (declOf u) k.callee Λ) pe tail with
            | .error err => .error err
            | .ok (body, remaining) => .ok (nestedElse u caller Γ Λ k τ hE hr errb body, remaining)
          | .ok (_, _) => .error "lower: a let else is not closed"
      else .error "lower: let else of a call without a reason channel"
  | Γ, fn, Λ, pe, .matchTagBeg sidx m bs :: rest =>
    match R.struct (l := l) Γ fn Λ pe (.matchTagBeg sidx m bs) rest with
    | .error err => .error err
    | .ok ((⟨Λ₁, st⟩, rest')) => match R.ende (l := l) Γ fn Λ₁ pe rest' with
      | .error err => .error err
      | .ok (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .bindSum x sidx v :: rest =>
    if hs : sidx < u.sums.length then
      (lowSVal u Γ Λ fn 0 sidx hs v).bind fun ev =>
        match R.ende (l := l) (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ) (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) Λ pe rest with
        | .error e => .error e
        | .ok (b, r) => .ok (Endblock.bind ev b, r)
    else .error "tagged type unknown"
  | Γ, fn, Λ, pe, .matchWhyBeg e :: rest =>
    match R.struct (l := l) Γ fn Λ pe (.matchWhyBeg e) rest with
    | .error err => .error err
    | .ok ((⟨Λ₁, st⟩, rest')) => match R.ende (l := l) Γ fn Λ₁ pe rest' with
      | .error err => .error err
      | .ok (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .startS :: rest => R.ende (l := l) Γ fn Λ pe rest
  | Γ, fn, Λ, pe, .lockBeg g :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.lockBeg g) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .ifBeg c :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.ifBeg c) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .ifEnde c :: rest =>
    -- both arms end: `Endblock.ite`; with anything but a closer behind it, the plain `if`
    match lowEns u Γ Λ fn none c, R.ende (l := l) Γ fn Λ pe rest with
    | .ok cv, .ok (t, .ifElse :: rest1) => match R.ende (l := l) Γ fn Λ pe rest1 with
      | .ok (e, .blkEnd :: .blkEnd :: rest2) => .ok (Endblock.ite cv t e, .blkEnd :: rest2)
      | .ok (e, .blkEnd :: .ifElse :: rest2) => .ok (Endblock.ite cv t e, .ifElse :: rest2)
      | .ok (e, [.blkEnd]) => .ok (Endblock.ite cv t e, [])
      | _ =>
        (R.struct (l := l) Γ fn Λ pe (.ifBeg c) rest).bind fun (⟨Λ₁, st⟩, rest') =>
          (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
    | .error e, _ => .error e
    | _, _ =>
      (R.struct (l := l) Γ fn Λ pe (.ifBeg c) rest).bind fun (⟨Λ₁, st⟩, rest') =>
        (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .arrayLoopBeg bnd array inv :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.arrayLoopBeg bnd array inv) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .loopBeg bnd tab inv :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.loopBeg bnd tab inv) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .retryBeg cnt bis :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.retryBeg cnt bis) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .matchBeg num o k :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.matchBeg num o k) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, .bindOpt x num o :: rest =>
    if hnum : num < u.tabs.length then
      (lowOpt u Γ Λ fn 0 num hnum o).bind fun ev =>
        match R.ende (l := l) (.opt ((declOf u).count ⟨num, hnum⟩) :: Γ) (fn.mitOpt x num ((declOf u).count ⟨num, hnum⟩)) Λ pe rest with
        | .error e => .error e
        | .ok (b, r) => .ok (Endblock.bind ev b, r)
    else .error "option table unknown"
  | Γ, fn, Λ, pe, .foreverBeg k :: rest =>
    (R.struct (l := l) Γ fn Λ pe (.foreverBeg k) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.ende (l := l) Γ fn Λ₁ pe rest').bind fun (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, Λ, pe, s :: rest =>
    (lowStmtL u caller Γ fn Λ s).bind fun ⟨Λ₁, st⟩ =>
      (R.ende (l := l) Γ fn Λ₁ pe rest).bind fun (b, r) => .ok (Endblock.cons st b, r)

end Gabbro.Grammatik.Parser.UebersetzeAllg2
