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

/-- A flat run of statements at `Λ`, up to (not including) the `zu`/`sonst` marker that ends it, or the
    end of the list; returns the block and what is left. A `let` binds for the rest of the run: its
    type is the COMPUTED range of the value (as the exporter pushes it) and the scope grows by it.
    Structural in the fuel. -/
def lowSeqStep {l : Bool} (u : UProg) (caller : Fin u.fns.length) (R : LowStufe u caller) :
    (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String ((Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u caller) l Γ Λ Λ') × List UStmt)
  | _, _, _, _, [] => .ok (⟨_, Block.nil, []⟩)
  | _, _, _, _, .blkEnd :: rest => .ok (⟨_, Block.nil, .blkEnd :: rest⟩)
  | _, _, _, _, .ifElse :: rest => .ok (⟨_, Block.nil, .ifElse :: rest⟩)
  | Γ, fn, Λ, pe, .breakingBeg name :: rest =>
    (R.struct Γ fn Λ pe (.breakingBeg name) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .lockBeg g :: rest =>
    (R.struct Γ fn Λ pe (.lockBeg g) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .ifBeg c :: rest =>
    (R.struct Γ fn Λ pe (.ifBeg c) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .ifEnde c :: rest =>
    (R.struct Γ fn Λ pe (.ifBeg c) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .arrayLoopBeg bnd array inv :: rest =>
    (R.struct Γ fn Λ pe (.arrayLoopBeg bnd array inv) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .loopBeg bnd tab inv :: rest =>
    (R.struct Γ fn Λ pe (.loopBeg bnd tab inv) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .retryBeg cnt bis :: rest =>
    (R.struct Γ fn Λ pe (.retryBeg cnt bis) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .matchBeg num o k :: rest =>
    (R.struct Γ fn Λ pe (.matchBeg num o k) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .bindOpt x num o :: rest =>
    if hnum : num < u.tabs.length then
      (lowOpt u Γ Λ fn 0 num hnum o).bind fun ev =>
        match R.seq (l := l) (.opt ((declOf u).count ⟨num, hnum⟩) :: Γ) (fn.mitOpt x num ((declOf u).count ⟨num, hnum⟩)) Λ pe rest with
        | .error e => .error e
        | .ok ((⟨Λ', b⟩, r)) => .ok (⟨Λ', Block.bind ev b⟩, r)
    else .error "option table unknown"
  | Γ, fn, Λ, pe, .foreverBeg k :: rest =>
    (R.struct Γ fn Λ pe (.foreverBeg k) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .axCallElseBeg c args reason :: rest =>
    (R.struct Γ fn Λ pe (.axCallElseBeg c args reason) rest).bind fun (⟨Λ₁, statement⟩, tail) =>
      (R.seq Γ fn Λ₁ pe tail).bind fun (⟨Λ₂, body⟩, remaining) => .ok (⟨Λ₂, Block.cons statement body⟩, remaining)
  | Γ, fn, Λ, pe, .bind x d v :: rest =>
    (lowBindWert u Γ Λ fn d v).bind fun s =>
      (R.seq (.int s.range.1 s.range.2 :: Γ) (fn.mitBindung x s.range) Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.bind s.term b⟩, r)
  | Γ, fn, Λ, pe, .bindW x d v :: rest =>
    (lowBindW u Γ Λ fn d v).bind fun w =>
      (R.seq (w.ty :: Γ) (fn.mitWert x w.ty) Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.bind w.term b⟩, r)
  | Γ, fn, Λ, pe, .floatLit x q lo hi :: rest =>
    (R.seq (.fl lo hi :: Γ) (fn.mitWert x (.fl lo hi)) Λ pe rest).bind fun (⟨Λ', b⟩, r) =>
      .ok (⟨Λ', Block.floatLit q lo hi b⟩, r)
  | Γ, fn, Λ, pe, .float x op a b lo hi :: rest => do
    let ⟨.fl _ _, left⟩ ← lowWertE u Γ Λ fn none a | .error "float: left operand is not a float"
    let ⟨.fl _ _, right⟩ ← lowWertE u Γ Λ fn none b | .error "float: right operand is not a float"
    let (⟨Λ', body⟩, remaining) ← R.seq (.fl lo hi :: Γ) (fn.mitWert x (.fl lo hi)) Λ pe rest
    pure (⟨Λ', Block.float op left right lo hi body⟩, remaining)
  | Γ, fn, Λ, pe, .bindB x v :: rest =>
    (lowEns u Γ Λ fn none v).bind fun ev =>
      (R.seq (.bool :: Γ) (fn.mitBindungB x) Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.bind ev b⟩, r)
  | Γ, fn, Λ, pe, .bindMut x lo hi v :: rest =>
    (lowWertAt u Γ Λ fn lo hi v).bind fun ev =>
      (R.seq (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.bind ev b⟩, r)
  | Γ, fn, Λ, pe, .bindCall x cname args :: rest =>
    (lowRufKopf u caller Γ fn Λ cname args).bind fun k =>
      withErg u k.callee fun τ hE =>
        (R.seq (l := l) (τ :: Γ) (fn.mitTy x τ) (nach (declOf u) k.callee Λ) pe rest).bind fun (⟨Λ', b⟩, r) =>
          if hr : (declOf u).gruende k.callee = 0 then
            .ok (⟨Λ', Block.bindCall (D := declOf u) k.callee k.args hE k.hp hr b⟩, r)
          else .error "call of a function with a reason channel needs `let .. else`"
  | Γ, fn, Λ, pe, .axCall c args :: rest =>
    (lowAxKopf u caller Γ fn Λ c args).bind fun k =>
      withAxErg u k.ax (fun h =>
          (R.seq (l := l) Γ fn Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.cons (axiomStmt u caller Γ Λ k h) b⟩, r))
        (fun τ hE =>
          (R.seq (l := l) (τ :: Γ) (fn.mitTy "#ax" τ) Λ pe rest).bind fun (⟨Λ', b⟩, r) =>
            .ok (⟨Λ', Block.bindAxiom (D := declOf u) k.ax k.args hE k.hw k.hg k.hd k.hgd b⟩, r))
  | Γ, fn, Λ, pe, .bindAx x c args :: rest =>
    (lowAxKopf u caller Γ fn Λ c args).bind fun k =>
      withAxErg u k.ax (fun _ => .error "call without a value") (fun τ hE =>
          (R.seq (l := l) (τ :: Γ) (fn.mitTy x τ) Λ pe rest).bind fun (⟨Λ', b⟩, r) =>
            .ok (⟨Λ', Block.bindAxiom (D := declOf u) k.ax k.args hE k.hw k.hg k.hd k.hgd b⟩, r))
  | Γ, fn, Λ, pe, .startS :: rest => R.seq (l := l) Γ fn Λ pe rest
  | _, _, _, _, .bindAxElse .. :: _ => .error "lower: a foreign let else in a continuing block has no G export"
  | Γ, fn, Λ, pe, .matchTagBeg sidx m bs :: rest =>
    (R.struct Γ fn Λ pe (.matchTagBeg sidx m bs) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .bindSum x sidx v :: rest =>
    if hs : sidx < u.sums.length then
      (lowSVal u Γ Λ fn 0 sidx hs v).bind fun ev =>
        match R.seq (l := l) (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ) (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) Λ pe rest with
        | .error e => .error e
        | .ok ((⟨Λ', b⟩, r)) => .ok (⟨Λ', Block.bind ev b⟩, r)
    else .error "tagged type unknown"
  | Γ, fn, Λ, pe, .matchWhyBeg e :: rest =>
    (R.struct Γ fn Λ pe (.matchWhyBeg e) rest).bind fun (⟨Λ₁, st⟩, rest') =>
      (R.seq Γ fn Λ₁ pe rest').bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .bindElse y c args e :: rest => match lowRufKopf u caller Γ fn Λ c args with
    | .error err => .error err
    | .ok k =>
      if hr : 0 < (declOf u).gruende k.callee then
        withErg u k.callee fun τ hE =>
          match R.ende (l := l) (Ty.why ((declOf u).gruende k.callee) :: Γ) (fn.mitWhy e 0 ((declOf u).gruende k.callee)) (nach (declOf u) k.callee Λ) pe rest with
          | .error err => .error err
          | .ok (errb, .blkEnd :: rest') => match R.seq (l := l) (τ :: Γ) (fn.mitTy y τ) (nach (declOf u) k.callee Λ) pe rest' with
            | .error err => .error err
            | .ok ((⟨Λ', b⟩, r)) =>
              .ok (⟨Λ', Block.bindCallElse (D := declOf u) k.callee k.args hE k.hp hr errb b⟩, r)
          | .ok (_, _) => .error "lower: a let else is not closed"
      else .error "lower: let else of a call without a reason channel"
  | Γ, fn, Λ, pe, .allocBeg x an v :: rest =>
    (tabIdx u.tabs an).bind fun t =>
      (globIdx u.globs (an ++ "#used")).bind fun g =>
        (fieldHit u t "wert").bind fun fh =>
          (lowWertAt u Γ Λ fn fh.range.1 fh.range.2 v).bind fun ev0 =>
            match R.ende (l := l) Γ fn Λ pe rest with
            | .error e => .error e
            | .ok (voll, .blkEnd :: rest') =>
              match R.seq (l := l) (Ty.index ((declOf u).count t) :: Γ) (fn.mitIndex x t.val ((declOf u).count t)) Λ pe rest' with
              | .error e => .error e
              | .ok ((⟨Λ', b⟩, r)) =>
                if h : Λ' = Λ then
                  (mkAllocBlock u caller Γ Λ t g fh ev0 voll (by subst h; exact b)).bind fun blk => .ok (⟨Λ, blk⟩, r)
                else .error "lower: an alloc body changes held marks"
            | .ok (_, _) => .error "lower: an alloc is not closed"
  | Γ, fn, Λ, pe, .bindOptBeg x c args :: rest =>
    (lowAxKopf u caller Γ fn Λ c args).bind fun k =>
      if hp : rufPasstB u (verOf u caller) ((declOf u).asignatur k.ax) Λ = true then
        let fn' := match (declOf u).aerg k.ax with
          | none => fn
          | some τ => fn.mitTy x τ
        (R.seq (l := l) (ErgCtx Γ ((declOf u).aerg k.ax)) fn' (nachSig (declOf u) ((declOf u).asignatur k.ax) Λ) pe rest).bind fun (⟨Λ', b⟩, r) =>
          .ok (⟨Λ', Block.bindAxiomOpt (e := (declOf u).aerg k.ax) k.ax k.args rfl
            (rufPasstB_ok hp) k.hd k.hgd b⟩, r)
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
            (R.seq (l := l) (ErgCtx Γ ((declOf u).aerg k.ax)) fn' (nachSig (declOf u) ((declOf u).asignatur k.ax) Λ) pe tail).bind fun (⟨Λ', b⟩, r) =>
              .ok (⟨Λ', Block.bindAxiomOptElse (e := (declOf u).aerg k.ax) k.ax k.args rfl
                (rufPasstB_ok hp) k.hd k.hgd hr errb b⟩, r)
          | .ok (_, _) => .error "lower: a let else is not closed"
        else .error "lower: let else of a foreign call without a reason channel"
      else .error "foreign call does not conform to caller contract"
  | Γ, fn, Λ, pe, .allocReqBeg x an v :: rest =>
    (tabIdx u.tabs an).bind fun t =>
      (globIdx u.globs (an ++ "#used")).bind fun g =>
        (fieldHit u t "wert").bind fun fh =>
          (lowWertAt u Γ Λ fn fh.range.1 fh.range.2 v).bind fun ev0 =>
            match R.seq (l := l) (Ty.index ((declOf u).count t) :: Γ) (fn.mitIndex x t.val ((declOf u).count t)) Λ pe rest with
            | .error e => .error e
            | .ok ((⟨Λ', b⟩, r)) =>
              if h : Λ' = Λ then
                (mkAllocRequiredBlock u caller Γ Λ t g fh ev0 (by subst h; exact b)).bind fun blk => .ok (⟨Λ, blk⟩, r)
              else .error "lower: an alloc body changes held marks"
  | Γ, fn, Λ, pe, .narrowBeg x lo hi :: rest =>
    (paramPos fn.params x).bind fun j => match fn.params[j]? with
      | some (_, .int l1 h1) =>
        (lowVar Γ j (.int l1 h1)).bind fun v => match R.ende (l := l) Γ fn Λ pe rest with
          | .error e => .error e
          | .ok (sonst, .blkEnd :: rest') =>
            (R.seq (l := l) (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) Λ pe rest').bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.narrow (D := declOf u) (Expr.var v) lo hi sonst b⟩, r)
          | .ok (_, _) => .error "lower: a narrow is not closed"
      | some (_, .fl l1 h1) =>
        (lowVar Γ j (.fl l1 h1)).bind fun v => match R.ende (l := l) Γ fn Λ pe rest with
          | .error e => .error e
          | .ok (sonst, .blkEnd :: rest') =>
            (R.seq (l := l) (.fl (lo, 1) (hi, 1) :: Γ)
              (fn.mitWert x (.fl (lo, 1) (hi, 1))) Λ pe rest').bind fun (⟨Λ', b⟩, r) =>
                .ok (⟨Λ', Block.floatNarrow (Expr.var v) (lo, 1) (hi, 1) sonst b⟩, r)
          | .ok (_, _) => .error "lower: a narrow is not closed"
      | _ => .error "lower: narrow of a non-number"
  /-- Required narrowing (C15): no `else`, no `blkEnd`; out of range is
      `Logik.kapazitaet` (`Block.narrowRequired`). -/
  | Γ, fn, Λ, pe, .narrowReqBeg x lo hi :: rest =>
    (paramPos fn.params x).bind fun j => match fn.params[j]? with
      | some (_, .int l1 h1) =>
        (lowVar Γ j (.int l1 h1)).bind fun v =>
          (R.seq (l := l) (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.narrowRequired (D := declOf u) (Expr.var v) lo hi b⟩, r)
      | _ => .error "lower: narrow of a non-number"
  | Γ, fn, Λ, pe, .bindFnref x f m :: rest =>
    (fnIdx u.fns f).bind fun g =>
      if h : (declOf u).passt g m = true then
        (R.seq (l := l) (Ty.fnptr m :: Γ) (fn.mitFnptr x m) Λ pe rest).bind fun (⟨Λ', b⟩, r') => .ok (⟨Λ', Block.bind (Expr.fnref (D := declOf u) g m h) b⟩, r')
      else .error "function does not conform to the pointer type"
  | Γ, fn, Λ, pe, .bindCallInd x p _ args :: rest =>
    (lowZeigerN u Γ fn p).bind fun ⟨m, v⟩ =>
      (lowRufKopfN u caller Γ fn Λ m args).bind fun k =>
        withErgN u m fun τ hE =>
          (R.seq (l := l) (τ :: Γ) (fn.mitTy x τ) (nachSig (declOf u) ((declOf u).sigNr m) Λ) pe rest).bind fun (⟨Λ', b⟩, r') =>
            if hr : ((declOf u).sigNr m).gruende = 0 then
              .ok (⟨Λ', Block.bindCallInd (D := declOf u) (n := m) (Expr.var v) k.args hE k.hp hr b⟩, r')
            else .error "call of a function with a reason channel needs `let .. else`"
  | Γ, fn, Λ, pe, .bindCallIndElse x p _ args e :: rest =>
    (lowZeigerN u Γ fn p).bind fun ⟨m, v⟩ =>
      (lowRufKopfN u caller Γ fn Λ m args).bind fun k =>
        if hr : 0 < ((declOf u).sigNr m).gruende then
          withErgN u m fun τ hE =>
            match R.ende (l := l) (Ty.why (((declOf u).sigNr m).gruende) :: Γ) (fn.mitWhy e 0 (((declOf u).sigNr m).gruende)) (nachSig (declOf u) ((declOf u).sigNr m) Λ) pe rest with
            | .error err => .error err
            | .ok (errb, .blkEnd :: tail) => match R.seq (l := l) (τ :: Γ) (fn.mitTy y τ) (nachSig (declOf u) ((declOf u).sigNr m) Λ) pe tail with
              | .error err => .error err
              | .ok ((⟨Λ', body⟩, remaining)) => .ok (⟨Λ', nestedElseN u caller Γ Λ m v k τ hE hr errb body⟩, remaining)
            | .ok (_, _) => .error "lower: a let else is not closed"
        else .error "lower: let else of a call without a reason channel"
  | Γ, fn, Λ, pe, .tausch x a v zweige neu :: rest =>
    (globIdx u.globs a).bind fun g => if hw : (verOf u caller).gschreibt g = true then
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        (lowTauschNeu u ((declOf u).gtyp g :: Γ) Λ (fn.mitTy v ((declOf u).gtyp g)) ((declOf u).gtyp g) zweige neu).bind fun ne =>
          (R.seq (l := l) ((declOf u).gtyp g :: Γ) (fn.mitTy x ((declOf u).gtyp g)) Λ pe rest).bind fun (⟨Λ', b⟩, r') => .ok (⟨Λ', Block.exchange (D := declOf u) g ne hw hd b⟩, r')
      else .error "access without held guard"
      else .error "exchange of a static the function does not write"
  | Γ, fn, Λ, pe, .awaitBind x a :: rest =>
    (globIdx u.globs a).bind fun g => if ha : (declOf u).atomar g = true then
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
        (R.seq (l := l) ((declOf u).gtyp g :: Γ) (fn.mitTy x ((declOf u).gtyp g)) Λ pe rest).bind fun (⟨Λ', b⟩, r') => .ok (⟨Λ', Block.awaits (D := declOf u) g ((declOf u).nutzlast g) rfl hd ha b⟩, r')
      else .error "access without held guard"
      else .error "awaits at a static that is not atomic"
  | Γ, fn, Λ, pe, .regRead x d r :: rest =>
    (regIdx u.regs d r).bind fun g =>
      if hk : ((declOf u).rklasse g).lesbar = true then
        match R.seq (l := l) ((regAt u g).ty :: Γ) (fn.mitTy x (regAt u g).ty) Λ pe rest with
        | .error e => .error e
        | .ok ((⟨Λ', b⟩, r')) => .ok (⟨Λ', Block.regRead (D := declOf u) g hk b⟩, r')
      else .error "lower: register read against its class"
  | Γ, fn, Λ, pe, .regReadElse x d r :: rest =>
    (regIdx u.regs d r).bind fun g =>
      if hk : ((declOf u).rklasse g).lesbar = true then match (regAt u g).pruefung with
        | none => .error "lower: register read without a check"
        | some p => match lowEns u ((regAt u g).ty :: Γ) Λ (fn.mitTy (regAt u g).name (regAt u g).ty) none p with
          | .error e => .error e
          | .ok zu => match R.ende (l := l) Γ fn Λ pe rest with
            | .error e => .error e
            | .ok (sonst, .blkEnd :: rest') =>
              match R.seq (l := l) ((regAt u g).ty :: Γ) (fn.mitTy x (regAt u g).ty) Λ pe rest' with
              | .error e => .error e
              | .ok ((⟨Λ', b⟩, r')) => .ok (⟨Λ', Block.regReadElse (D := declOf u) g hk zu sonst b⟩, r')
            | .ok (_, _) => .error "lower: a let else is not closed"
      else .error "lower: register read against its class"
  | Γ, fn, Λ, pe, .ret v :: rest =>
    (lowRetStmt u caller Γ fn Λ pe v).bind fun st =>
      (R.seq Γ fn Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.cons st b⟩, r)
  | Γ, fn, Λ, pe, .leave _ :: rest =>
    if h : l = true then (R.seq Γ fn Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.cons (Stmt.leave h) b⟩, r)
    else .error "lower: leave outside a traverse"
  | Γ, fn, Λ, pe, .next _ :: rest =>
    if h : l = true then (R.seq Γ fn Λ pe rest).bind fun (⟨Λ', b⟩, r) => .ok (⟨Λ', Block.cons (Stmt.next h) b⟩, r)
    else .error "lower: next outside a traverse"
  | Γ, fn, Λ, pe, s :: rest =>
    (lowStmtL u caller Γ fn Λ s).bind fun ⟨Λ₁, st⟩ =>
      (R.seq Γ fn Λ₁ pe rest).bind fun (⟨Λ₂, b⟩, r) => .ok (⟨Λ₂, Block.cons st b⟩, r)

/-- Float narrowing uses the same checked local lookup and ending fallback as
    integer narrowing. The successful continuation alone sees the shadow binding;
    the fallback retains the original scope and resource inventory. -/
theorem lowSeqStep_floatNarrow {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ Λ' : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (x : String) (j : Nat) (l1 h1 : Int × Int) (lo hi : Int)
    (rest tail remaining : List UStmt) (v : Var Γ (.fl l1 h1))
    (fallback : Endblock (declOf u) (verOf u caller) l Γ Λ)
    (body : Block (declOf u) (verOf u caller) l (.fl (lo, 1) (hi, 1) :: Γ) Λ Λ')
    (position : paramPos fn.params x = .ok j)
    (parameter : fn.params[j]? = some (x, .fl l1 h1))
    (localVar : lowVar Γ j (.fl l1 h1) = .ok v)
    (handler : R.ende (l := l) Γ fn Λ pe rest = .ok (fallback, .blkEnd :: tail))
    (continuation : R.seq (l := l) (.fl (lo, 1) (hi, 1) :: Γ)
      (fn.mitWert x (.fl (lo, 1) (hi, 1))) Λ pe tail = .ok (⟨Λ', body⟩, remaining)) :
    lowSeqStep (l := l) u caller R Γ fn Λ pe (.narrowBeg x lo hi :: rest) =
      .ok (⟨Λ', Block.floatNarrow (Expr.var v) (lo, 1) (hi, 1) fallback body⟩, remaining) := by
  simp only [lowSeqStep, position, parameter, localVar, handler, continuation, bind, Except.bind, pure, Except.pure] <;> rfl

end Gabbro.Grammatik.Parser.UebersetzeAllg2
