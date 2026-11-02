module

public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
public import Grammatik.Parser.Elab.UebersetzeAllg3.Transition

@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000


/-! ## Bodies and program assembly -/

/-- The fuel of a nested block (statements and nesting depth together). -/
def blockFuel : Nat := 100000

/-- The body reader, structural in a fuel: straight-line writes, direct calls, `locks`, `if` and
    `traverse` and `let` bindings (the scope `Γ`/`fn` grows by each), then the trailing return. -/
def lowBodyF (u : UProg) (caller : Fin u.fns.length) :
    (Γ : Ctx) → UFn → Nat → List UStmt → URet →
    Except String (Endblock (declOf u) (verOf u caller) false Γ (resOf u caller))
  | _, _, 0, _, _ => .error "lower: body too long"
  | Γ, fn, _ + 1, [], r => lowEnd u caller Γ fn r
  | Γ, fn, n + 1, .bind x d v :: rest, r =>
    match lowBindWert u Γ (resOf u caller) fn d v with
    | .error e => .error e
    | .ok s =>
      match lowBodyF u caller (.int s.range.1 s.range.2 :: Γ) (fn.mitBindung x s.range) n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.bind s.term e)
  | Γ, fn, n + 1, .bindW x d v :: rest, r =>
    match lowBindW u Γ (resOf u caller) fn d v with
    | .error e => .error e
    | .ok w =>
      match lowBodyF u caller (w.ty :: Γ) (fn.mitWert x w.ty) n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.bind w.term e)
  | Γ, fn, n + 1, .axCall c args :: rest, r =>
    match lowAxKopf u caller Γ fn (resOf u caller) c args with
    | .error e => .error e
    | .ok k =>
      withAxErg u k.ax
        (fun h =>
          match lowBodyF u caller Γ fn n rest r with
          | .error e => .error e
          | .ok e => .ok (Endblock.cons (axiomStmt u caller Γ (resOf u caller) k h) e))
        (fun τ hE =>
          match lowBodyF u caller (τ :: Γ) (fn.mitTy "#ax" τ) n rest r with
          | .error e => .error e
          | .ok e =>
            .ok (Endblock.bindAxiom (D := declOf u) k.ax k.args hE
              k.hw
              k.hg
              k.hd
              k.hgd e))
  | Γ, fn, n + 1, .bindAx x c args :: rest, r =>
    match lowAxKopf u caller Γ fn (resOf u caller) c args with
    | .error e => .error e
    | .ok k =>
      withAxErg u k.ax (fun _ => .error "call without a value")
        (fun τ hE =>
          match lowBodyF u caller (τ :: Γ) (fn.mitTy x τ) n rest r with
          | .error e => .error e
          | .ok e =>
            .ok (Endblock.bindAxiom (D := declOf u) k.ax k.args hE
              k.hw
              k.hg
              k.hd
              k.hgd e))
  | Γ, fn, n + 1, .bindCall x cname args :: rest, r =>
    match lowRufKopf u caller Γ fn (resOf u caller) cname args with
    | .error e => .error e
    | .ok k =>
      withErg u k.callee fun τ hE =>
        match lowBodyF u caller (τ :: Γ) (fn.mitTy x τ) n rest r with
        | .error e => .error e
        | .ok e =>
          if hr : (declOf u).gruende k.callee = 0 then
            have e' : Endblock (declOf u) (verOf u caller) false (τ :: Γ)
                (nach (declOf u) k.callee (resOf u caller)) := by
              rw [nach_eq u k.callee (resOf u caller)]
              exact e
            .ok (Endblock.bindCall (D := declOf u) k.callee k.args hE k.hp hr e')
          else .error "call of a function with a reason channel needs `let .. else`"
  | Γ, fn, n + 1, .narrowBeg x lo hi :: rest, r =>
    match paramPos fn.params x with
    | .error e => .error e
    | .ok j =>
      match fn.params[j]? with
      | some (_, .int l1 h1) =>
        match lowVar Γ j (.int l1 h1) with
        | .error e => .error e
        | .ok v =>
          match lowEndL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) rest with
          | .error e => .error e
          | .ok (sonst, .blkEnd :: rest') =>
            match lowBodyF u caller (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n rest' r with
            | .error e => .error e
            | .ok b => .ok (Endblock.narrow (D := declOf u) (Expr.var v) lo hi sonst b)
          | .ok (_, _) => .error "lower: a narrow is not closed"
      | _ => .error "lower: narrow of a non-number"
  | Γ, fn, n + 1, .bindFnref x f m :: rest, r =>
    match fnIdx u.fns f with
    | .error e => .error e
    | .ok g =>
      if h : (declOf u).passt g m = true then
        match lowBodyF u caller (Ty.fnptr m :: Γ) (fn.mitFnptr x m) n rest r with
        | .error e => .error e
        | .ok e => .ok (Endblock.bind (Expr.fnref (D := declOf u) g m h) e)
      else .error "function does not conform to the pointer type"
  | Γ, fn, n + 1, .bindCallInd x p _ args :: rest, r =>
    match lowZeigerN u Γ fn p with
    | .error e => .error e
    | .ok ⟨m, v⟩ =>
      match lowRufKopfN u caller Γ fn (resOf u caller) m args with
      | .error e => .error e
      | .ok k =>
        withErgN u m fun τ hE =>
          match lowBodyF u caller (τ :: Γ) (fn.mitTy x τ) n rest r with
          | .error e => .error e
          | .ok e =>
            if hr : ((declOf u).sigNr m).gruende = 0 then
              have e' : Endblock (declOf u) (verOf u caller) false (τ :: Γ)
                  (nachSig (declOf u) ((declOf u).sigNr m) (resOf u caller)) := by
                rw [nachSigAt_eq u m (resOf u caller)]
                exact e
              .ok (Endblock.bindCallInd (D := declOf u) (n := m) (Expr.var v) k.args hE k.hp hr e')
            else .error "call of a function with a reason channel needs `let .. else`"
  | Γ, fn, n + 1, .bindCallIndElse x p _ args e :: rest, r =>
    match lowZeigerN u Γ fn p with
    | .error e => .error e
    | .ok ⟨m, v⟩ =>
      match lowRufKopfN u caller Γ fn (resOf u caller) m args with
      | .error e => .error e
      | .ok k =>
        if hr : 0 < ((declOf u).sigNr m).gruende then
          withErgN u m fun τ hE =>
            match lowEndL (l := false) u caller (Ty.why (((declOf u).sigNr m).gruende) :: Γ)
                (fn.mitWhy e 0 (((declOf u).sigNr m).gruende)) blockFuel (resOf u caller) (some ⟨rfl⟩) rest with
            | .error err => .error err
            | .ok (errb, .blkEnd :: rest') =>
              match lowBodyF u caller (τ :: Γ) (fn.mitTy x τ) n rest' r with
              | .error err => .error err
              | .ok ee =>
                have errb' : Endblock (declOf u) (verOf u caller) false
                    (Ty.why (((declOf u).sigNr m).gruende) :: Γ)
                    (nachSig (declOf u) ((declOf u).sigNr m) (resOf u caller)) := by
                  rw [nachSigAt_eq u m (resOf u caller)]
                  exact errb
                have ee' : Endblock (declOf u) (verOf u caller) false (τ :: Γ)
                    (nachSig (declOf u) ((declOf u).sigNr m) (resOf u caller)) := by
                  rw [nachSigAt_eq u m (resOf u caller)]
                  exact ee
                .ok (Endblock.bindCallIndElse (D := declOf u) (n := m) (Expr.var v) k.args hE k.hp hr errb' ee')
            | .ok (_, _) => .error "lower: a let else is not closed"
        else .error "lower: let else of a call without a reason channel"
  | Γ, fn, n + 1, .tausch x a v zweige neu :: rest, r =>
    match globIdx u.globs a with
    | .error e => .error e
    | .ok g =>
      if hw : (verOf u caller).gschreibt g = true then
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ resOf u caller) then
        match lowTauschNeu u ((declOf u).gtyp g :: Γ) (resOf u caller) (fn.mitTy v ((declOf u).gtyp g)) ((declOf u).gtyp g) zweige neu with
        | .error e => .error e
        | .ok ne =>
          match lowBodyF u caller ((declOf u).gtyp g :: Γ) (fn.mitTy x ((declOf u).gtyp g)) n rest r with
          | .error e => .error e
          | .ok b => .ok (Endblock.exchange (D := declOf u) g ne hw hd b)
      else .error "access without held guard"
      else .error "exchange of a static the function does not write"
  | Γ, fn, n + 1, .awaitBind x a :: rest, r =>
    match globIdx u.globs a with
    | .error e => .error e
    | .ok g =>
      if ha : (declOf u).atomar g = true then
      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ resOf u caller) then
        match lowBodyF u caller ((declOf u).gtyp g :: Γ) (fn.mitTy x ((declOf u).gtyp g)) n rest r with
        | .error e => .error e
        | .ok e => .ok (Endblock.awaits (D := declOf u) g ((declOf u).nutzlast g) rfl hd ha e)
      else .error "access without held guard"
      else .error "awaits at a static that is not atomic"
  | Γ, fn, n + 1, .regRead x d rg :: rest, r =>
    match regIdx u.regs d rg with
    | .error e => .error e
    | .ok g =>
      if hk : ((declOf u).rklasse g).lesbar = true then
        match lowBodyF u caller ((regAt u g).ty :: Γ) (fn.mitTy x (regAt u g).ty) n rest r with
        | .error e => .error e
        | .ok e => .ok (Endblock.regRead (D := declOf u) g hk e)
      else .error "lower: register read against its class"
  | Γ, fn, n + 1, .regReadElse x d rg :: rest, r =>
    match regIdx u.regs d rg with
    | .error e => .error e
    | .ok g =>
      if hk : ((declOf u).rklasse g).lesbar = true then
        match (regAt u g).pruefung with
        | none => .error "lower: register read without a check"
        | some p =>
          match lowEns u ((regAt u g).ty :: Γ) (resOf u caller)
              (fn.mitTy (regAt u g).name (regAt u g).ty) none p with
          | .error e => .error e
          | .ok zu =>
            match lowEndL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) rest with
            | .error e => .error e
            | .ok (sonst, .blkEnd :: rest') =>
              match lowBodyF u caller ((regAt u g).ty :: Γ) (fn.mitTy x (regAt u g).ty) n rest' r with
              | .error e => .error e
              | .ok e => .ok (Endblock.regReadElse (D := declOf u) g hk zu sonst e)
            | .ok (_, _) => .error "lower: a let else is not closed"
      else .error "lower: register read against its class"
  | _, _, _ + 1, .allocBeg .. :: _, _ =>
    .error "lower: an alloc at the top level of a body has no G form (Endblock lacks arenaAlloc)"
  | Γ, fn, n + 1, .ret v :: rest, r =>
    match lowRetStmt (l := false) u caller Γ fn (resOf u caller) (some ⟨rfl⟩) v with
    | .error e => .error e
    | .ok st =>
      match lowBodyF u caller Γ fn n rest r with
      | .error e => .error e
      | .ok ee => .ok (Endblock.cons st ee)
  | Γ, fn, n + 1, .bindElse y c args e :: rest, r =>
    match lowRufKopf u caller Γ fn (resOf u caller) c args with
    | .error err => .error err
    | .ok k =>
      if hr : 0 < (declOf u).gruende k.callee then
        withErg u k.callee fun τ hE =>
          match lowEndL (l := false) u caller (Ty.why ((declOf u).gruende k.callee) :: Γ)
              (fn.mitWhy e 0 ((declOf u).gruende k.callee)) blockFuel (resOf u caller) (some ⟨rfl⟩) rest with
          | .error err => .error err
          | .ok (errb, .blkEnd :: rest') =>
            match lowBodyF u caller (τ :: Γ) (fn.mitTy y τ) n rest' r with
            | .error err => .error err
            | .ok ee =>
              have errb' : Endblock (declOf u) (verOf u caller) false
                  (Ty.why ((declOf u).gruende k.callee) :: Γ) (nach (declOf u) k.callee (resOf u caller)) := by
                rw [nach_eq u k.callee (resOf u caller)]
                exact errb
              have ee' : Endblock (declOf u) (verOf u caller) false (τ :: Γ)
                  (nach (declOf u) k.callee (resOf u caller)) := by
                rw [nach_eq u k.callee (resOf u caller)]
                exact ee
              .ok (Endblock.bindCallElse (D := declOf u) k.callee k.args hE k.hp hr errb' ee')
          | .ok (_, _) => .error "lower: a let else is not closed"
      else .error "lower: let else of a call without a reason channel"
  | Γ, fn, n + 1, .bindAxElse y c args e :: rest, r =>
    match lowAxKopf u caller Γ fn (resOf u caller) c args with
    | .error err => .error err
    | .ok k =>
      if hr : 0 < (declOf u).agruende k.ax then
        withAxErg u k.ax (fun _ => .error "call without a value") fun τ hE =>
          match lowEndL (l := false) u caller (Ty.why ((declOf u).agruende k.ax) :: Γ)
              (fn.mitWhy e 0 ((declOf u).agruende k.ax)) blockFuel (resOf u caller) (some ⟨rfl⟩) rest with
          | .error err => .error err
          | .ok (errb, .blkEnd :: rest') =>
            match lowBodyF u caller (τ :: Γ) (fn.mitTy y τ) n rest' r with
            | .error err => .error err
            | .ok ee =>
              .ok (Endblock.bindAxiomElse (D := declOf u) k.ax k.args hE hr
                k.hw
                k.hg
                k.hd
                k.hgd errb ee)
          | .ok (_, _) => .error "lower: a let else is not closed"
      else .error "lower: let else of a foreign call without a reason channel"
  | Γ, fn, n + 1, (.matchTagBeg sidx m bs) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.matchTagBeg sidx m bs) rest with
    | .error err => .error err
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error err => .error err
      | .ok ee => .ok (Endblock.cons st ee)
  | Γ, fn, n + 1, .bindSum x sidx v :: rest, r =>
    if hs : sidx < u.sums.length then
      match lowSVal u Γ (resOf u caller) fn 0 sidx hs v with
      | .error e => .error e
      | .ok ev =>
        match lowBodyF u caller (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ)
            (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) n rest r with
        | .error e => .error e
        | .ok ee => .ok (Endblock.bind ev ee)
    else .error "tagged type unknown"
  | Γ, fn, n + 1, (.matchWhyBeg e) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.matchWhyBeg e) rest with
    | .error err => .error err
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error err => .error err
      | .ok ee => .ok (Endblock.cons st ee)
  | Γ, fn, n + 1, .startS :: rest, r => lowBodyF u caller Γ fn n rest r
  | Γ, fn, n + 1, .bindB x v :: rest, r =>
    match lowEns u Γ (resOf u caller) fn none v with
    | .error e => .error e
    | .ok ev =>
      match lowBodyF u caller (.bool :: Γ) (fn.mitBindungB x) n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.bind ev e)
  | Γ, fn, n + 1, .bindMut x lo hi v :: rest, r =>
    match lowWertAt u Γ (resOf u caller) fn lo hi v with
    | .error e => .error e
    | .ok ev =>
      match lowBodyF u caller (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.bind ev e)
  | Γ, fn, n + 1, (.lockBeg g) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.lockBeg g) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.ifBeg c) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.ifBeg c) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.ifEnde c) :: rest, .keins =>
    -- the last statement of a body without a trailing return, both arms ending: `Endblock.ite`
    match lowEns u Γ (resOf u caller) fn none c,
        lowEndL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) rest with
    | .ok cv, .ok (t, .ifElse :: rest1) =>
      match lowEndL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) rest1 with
      | .ok (e, [.blkEnd]) => .ok (Endblock.ite cv t e)
      | .ok (_, _) => .error "lower: a terminal if is followed by statements"
      | .error err => .error err
    | .error err, _ => .error err
    | _, _ => .error "fn with a result falls off"
  | Γ, fn, n + 1, (.ifEnde c) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.ifBeg c) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.arrayLoopBeg b array i) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.arrayLoopBeg b array i) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.loopBeg b t i) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.loopBeg b t i) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.retryBeg c b) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.retryBeg c b) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.matchBeg num o k) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.matchBeg num o k) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, .bindOpt x num o :: rest, r =>
    if hnum : num < u.tabs.length then
      match lowOpt u Γ (resOf u caller) fn 0 num hnum o with
      | .error e => .error e
      | .ok ev =>
        match lowBodyF u caller (.opt ((declOf u).count ⟨num, hnum⟩) :: Γ)
            (fn.mitOpt x num ((declOf u).count ⟨num, hnum⟩)) n rest r with
        | .error e => .error e
        | .ok e => .ok (Endblock.bind ev e)
    else .error "option table unknown"
  | Γ, fn, n + 1, (.foreverBeg k) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.foreverBeg k) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, s :: rest, r =>
    match lowStmtL u caller Γ fn (resOf u caller) s with
    | .error e => .error e
    | .ok st =>
      match lowBodyF u caller Γ fn n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)

/-- The body: the statements of a function, then the trailing return, in the scope of its parameters. -/
def lowBody (u : UProg) (caller : Fin u.fns.length)
    (ss : List UStmt) (r : URet) :
    Except String (Endblock (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller)) :=
  lowBodyF u caller (ctxOf u caller) (fnAt u caller) (ss.length + 1) ss r


/-- One whole function: contracts and body through the
    declaration. -/
def lowerFnPlain (u : UProg) (c : Fin u.fns.length) :
    Except String (EnsTy u c × RumpTy u c × ReqTy u c) :=
  match lowEnsList u (ctxOf u c) (resOf u c) (fnAt u c) none (fnAt u c).needs with
  | .error e => .error e
  | .ok r0 =>
  match lowEnsList u (ErgCtx (ctxOf u c) ((verOf u c).erg))
      (resOf u c) (fnAt u c) (fnAt u c).ergTy
      (fnAt u c).gives with
  | .error e => .error e
  | .ok e0 =>
    match lowBody u c (fnAt u c).body (fnAt u c).ret with
    | .error e => .error e
    | .ok b0 =>
      have e1 : EnsTy u c := by
        show Expr (declOf u)
          (ErgCtx ((declOf u).params c) ((declOf u).erg c))
          (vertragVon (declOf u) c).ende .bool
        rw [← ensCtx_eq u c, ← endeRes_eq u c]
        exact e0
      have b1 : RumpTy u c := by
        show Endblock (declOf u) (vertragVon (declOf u) c) false
          ((declOf u).params c)
          (Signatur.anfang (declOf u) ((declOf u).signatur c))
        rw [← ctxParams_eq u c, ← anfangRes_eq u c]
        exact b0
      have r1 : ReqTy u c := by
        show Expr (declOf u) ((declOf u).params c) (Signatur.anfang (declOf u) ((declOf u).signatur c)) .bool
        rw [← ctxParams_eq u c, ← anfangRes_eq u c]
        exact r0
      .ok (e1, b1, r1)

/-- One whole function. A function a transition declaration generates is lowered as
    the typed expansion of that declaration (`lowerTransitionAt`); a function of the
    generated name range that matches no declaration is refused, never lowered as an
    ordinary function. -/
def lowerFnAt (u : UProg) (c : Fin u.fns.length) :
    Except String (EnsTy u c × RumpTy u c × ReqTy u c) :=
  match transitionOfFn u c with
  | some (state, tr) => lowerTransitionAt u c state tr
  | none =>
    if (fnAt u c).name.startsWith "#transition#" then
      .error "generated transition function without declaration"
    else lowerFnPlain u c

/-- Every function lowers (the success check of `lowerAllg`;
    the values ride `lowerFnAt` directly). -/
def lowerEach (u : UProg) :
    List (Fin u.fns.length) → Except String Unit
  | [] => .ok ()
  | f :: fs =>
    match lowerFnAt u f with
    | .error e => .error e
    | .ok _ => lowerEach u fs

end Gabbro.Grammatik.Parser.UebersetzeAllg2
