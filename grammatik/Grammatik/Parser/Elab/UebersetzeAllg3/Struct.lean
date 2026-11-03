module

public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.CallElse

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- Consuming keeps the written mutation sub-contract. A consumes of slots grants the
    same write footprint as writes, but must name the selected domain explicitly. -/
def lowConsumingEffects (u : UProg) (fn : UFn) (table : String) (effects : List SEffekt) :
    Except String Unit := do
  let head : UFnKopf := {name := fn.name, names := fn.params.map (·.1), kinds := fn.kinds,
    types := fn.params.map (·.2), res := none, held := fn.held}
  let consumed ← (effects.filterMap fun effect => match effect with
    | .takes place => some place
    | _ => none).mapM (uSchreibtOrt head u.tabs)
  if !(consumed.any (strEq · table)) then
    throw "consuming traversal touches must consume its domain"
  let normalized ← effects.mapM fun effect => match effect with
    | .takes place => pure (SEffekt.writes place)
    | .reads _ | .writes _ | .locks .. | .pure => pure effect
    | _ => throw "consuming traversal touches effect without G form"
  let checked ← uEffekteAux head u.tabs u.locks u.globs normalized
  if !(checked.puts.all (fun name => fn.puts.any (strEq · name))) ||
      !(checked.gputs.all (fun name => fn.gputs.any (strEq · name))) then
    throw "consuming traversal touches exceeds function writes"
  pure ()

/-- The existing value elaborator computes the finite bound. Negative measures are
    refused; widening to 0 .. bound never narrows or changes the value. -/
def lowConsumingMass (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (source : USide) :
    Except String (Σ bound : Int, Expr (declOf u) Γ Λ (.int 0 bound)) := do
  let mass ← (lowSideVal u Γ Λ fn source).mapError ("consuming traversal decreases: " ++ ·)
  if lower : 0 ≤ mass.range.1 then
    pure ⟨mass.range.2, Expr.widen lower (Int.le_refl _) mass.term⟩
  else throw "consuming traversal decreases must have a nonnegative range"

/-- The structured statements, each with the rest of the run after its body: `locks g { … }` (the lock
    by name, the rank rule; no `return` inside), `if c { … } else { … }` and `traverse` (its body is a
    block with `l = true`, the binder an index into the table, the invariant read in the OUTER scope). -/
def lowStructStep {l : Bool} (u : UProg) (caller : Fin u.fns.length) (R : LowStufe u caller) :
    (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → UStmt → List UStmt →
    Except String ((Σ Λ' : List (Res (declOf u)), Stmt (declOf u) (verOf u caller) l Γ Λ Λ') × List UStmt)
  | Γ, fn, Λ, pe, .axCallElseBeg c args reason, rest =>
    (lowAxCallElse u caller R Γ fn Λ pe c args reason rest).map fun (st, rest') => (⟨Λ, st⟩, rest')
  | Γ, fn, Λ, _, .lockBeg g, rest =>
    (lockIdx u.locks g).bind fun L =>
      if hr : rangOkB u Λ L = true then match R.seq Γ fn (Res.held L :: Λ) none rest with
        | .error e => .error e
        | .ok ((⟨Λ', body⟩, .blkEnd :: rest')) =>
          if h : Λ' = Res.held L :: Λ then
            .ok (⟨Λ, Stmt.locks L (rangOkB_sound u Λ L hr) (by subst h; exact body)⟩, rest')
          else .error "lower: a locks block changes held marks"
        | .ok (_, _) => .error "lower: a locks block is not closed"
      else .error "lower: locks against a held lock of higher or equal rank"
  | Γ, fn, Λ, pe, .ifBeg c, rest =>
    (lowEns u Γ Λ fn none c).bind fun cv => match R.seq Γ fn Λ pe rest with
      | .error e => .error e
      | .ok ((⟨Λ₁, tb⟩, .ifElse :: rest1)) => match R.seq Γ fn Λ pe rest1 with
        | .error e => .error e
        | .ok ((⟨Λ₂, eb⟩, .blkEnd :: rest2)) =>
          if h : Λ₁ = Λ₂ then
            .ok (⟨Λ₁, Stmt.ite cv tb (by subst h; exact eb)⟩, rest2)
          else .error "lower: if arms end with different held marks"
        | .ok (_, _) => .error "lower: an if is not closed"
      | .ok (_, _) => .error "lower: an if has no else part"
  | Γ, fn, Λ, pe, .arrayLoopBeg binder source invariant, rest => do
    u.exportGate
    let array ← lowArrayValue u Γ Λ fn none source
    let carrier ← arrayCarrier u array.count
    let iv ← lowEns u Γ Λ fn none invariant
    match R.seq (l := true) (Ty.index ((declOf u).count carrier.table) :: Γ) (fn.mitTy binder (.index ((declOf u).count carrier.table))) Λ pe rest with
    | .error error => .error error
    | .ok ((⟨Λ', body⟩, .blkEnd :: remaining)) =>
      if h : Λ' = Λ then
        .ok (⟨Λ, Stmt.traverse carrier.table iv (by subst h; exact body)⟩, remaining)
      else .error "lower: an array traverse body changes held marks"
    | .ok (_, _) => .error "lower: an array traverse is not closed"
  | Γ, fn, Λ, pe, .loopBeg bnd tab inv, rest =>
    (tabIdx u.tabs tab).bind fun t =>
      (lowEns u Γ Λ fn none inv).bind fun iv =>
        match R.seq (l := true) (Ty.index ((declOf u).count t) :: Γ) (fn.mitIndex bnd t.val ((declOf u).count t)) Λ pe rest with
        | .error e => .error e
        | .ok ((⟨Λ', body⟩, .blkEnd :: rest')) =>
          if h : Λ' = Λ then
            .ok (⟨Λ, Stmt.traverse t iv (by subst h; exact body)⟩, rest')
          else .error "lower: a traverse body changes held marks"
        | .ok (_, _) => .error "lower: a traverse is not closed"
  | Γ, fn, Λ, pe, .consumeLoopBeg binder table predecessor member edge inv mass effects, rest => do
    let t ← tabIdx u.tabs table
    lowConsumingEffects u fn table effects
    let iv ← lowEns u Γ Λ fn none inv
    let ⟨bound, measure⟩ ← lowConsumingMass u Γ Λ fn mass
    let inner := fn.mitIndex binder t.val ((declOf u).count t)
    let membership ← lowEns u (.index ((declOf u).count t) :: Γ) Λ inner none member
    let relation ← lowEns u (.index ((declOf u).count t) :: .index ((declOf u).count t) :: Γ) Λ
      (inner.mitIndex predecessor t.val ((declOf u).count t)) none edge
    match R.seq (l := true) (.index ((declOf u).count t) :: Γ) inner Λ pe rest with
    | .error error => .error error
    | .ok ((⟨Λ', body⟩, .blkEnd :: remaining)) =>
      if h : Λ' = Λ then
        .ok (⟨Λ, Stmt.consumeTraverse t membership relation iv bound measure (by subst h; exact body)⟩, remaining)
      else .error "lower: a consuming traverse body changes held marks"
    | .ok (_, _) => .error "lower: a consuming traverse is not closed"
  | Γ, fn, Λ, pe, .retryBeg cnt bis, rest =>
    (lowEns u Γ Λ fn none bis).bind fun bv => match R.seq (l := true) Γ fn Λ pe rest with
      | .error e => .error e
      | .ok ((⟨Λ₁, body⟩, .ifElse :: rest1)) => match R.seq (l := l) Γ fn Λ pe rest1 with
        | .error e => .error e
        | .ok ((⟨Λ₂, ueb⟩, .blkEnd :: rest2)) =>
          if h₁ : Λ₁ = Λ then
            if h₂ : Λ₂ = Λ then
              .ok (⟨Λ, Stmt.retry cnt bv (by subst h₁; exact body) (by subst h₂; exact ueb)⟩, rest2)
            else .error "lower: a retry overflow changes held marks"
          else .error "lower: a retry body changes held marks"
        | .ok (_, _) => .error "lower: a retry is not closed"
      | .ok (_, _) => .error "lower: a retry has no overflow part"
  | Γ, fn, Λ, pe, .matchTagBeg sidx m bs, rest =>
    if hs : sidx < u.sums.length then match paramPos fn.params m with
      | .error err =>
        -- a static of a tagged type
        match globIdx u.globs m with
        | .error _ => .error err
        | .ok g =>
          if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then match h : (declOf u).gtyp g with
            | .sum cs => match R.arms (l := l) Γ fn Λ pe cs bs rest with
              | .error err => .error err
              | .ok (arms, .blkEnd :: rest') =>
                .ok (⟨Λ, Stmt.onTag (D := declOf u) (h ▸ Expr.glob (D := declOf u) g hd) arms⟩, rest')
              | .ok (_, _) => .error "lower: a match is not closed"
            | _ => .error "lower: match of a non-tagged value"
          else .error "access without held guard"
      | .ok j => match fn.params[j]? with
        | some (_, .sum cs) => match lowVar Γ j (.sum cs) with
          | .error err => .error err
          | .ok v => match R.arms (l := l) Γ fn Λ pe cs bs rest with
            | .error err => .error err
            | .ok (arms, .blkEnd :: rest') => .ok (⟨Λ, Stmt.onTag (D := declOf u) (Expr.var v) arms⟩, rest')
            | .ok (_, _) => .error "lower: a match is not closed"
        | _ => .error "lower: match of a non-tagged value"
    else .error "tagged type unknown"
  | Γ, fn, Λ, pe, .matchWhyBeg e, rest => match paramPos fn.params e with
    | .error err => .error err
    | .ok j => match fn.params[j]? with
      | some (_, .why cnt) => match lowVar Γ j (.why cnt) with
        | .error err => .error err
        | .ok v => match R.garms (l := l) Γ fn Λ pe cnt rest with
          | .error err => .error err
          | .ok (arms, .blkEnd :: rest') => .ok (⟨Λ, Stmt.onWhy (D := declOf u) (Expr.var v) arms⟩, rest')
          | .ok (_, _) => .error "lower: a match is not closed"
      | _ => .error "lower: match of a non-reason"
  | Γ, fn, Λ, pe, .matchBeg num o k, rest =>
    if hnum : num < u.tabs.length then
      (lowOpt u Γ Λ fn 0 num hnum o).bind fun ov =>
        match R.seq (l := l) (Ty.index ((declOf u).count ⟨num, hnum⟩) :: Γ) (fn.mitIndex k num ((declOf u).count ⟨num, hnum⟩)) Λ pe rest with
        | .error e => .error e
        | .ok ((⟨Λ₁, sb⟩, .ifElse :: rest1)) => match R.seq (l := l) Γ fn Λ pe rest1 with
          | .error e => .error e
          | .ok ((⟨Λ₂, nb⟩, .blkEnd :: rest2)) =>
            if h : Λ₁ = Λ₂ then
              .ok (⟨Λ₁, Stmt.onOption (D := declOf u) ov sb (by subst h; exact nb)⟩, rest2)
            else .error "lower: match arms end with different held marks"
          | .ok (_, _) => .error "lower: a match is not closed"
        | .ok (_, _) => .error "lower: a match has no None arm"
    else .error "option table unknown"
  | Γ, fn, Λ, pe, .foreverBeg k, rest =>
    if hk : k < u.annahmen.length then match R.seq (l := true) Γ fn Λ pe rest with
      | .error e => .error e
      | .ok ((⟨Λ', body⟩, .blkEnd :: rest')) =>
        if h : Λ' = Λ then
          .ok (⟨Λ, Stmt.forever (D := declOf u) (some ⟨k, hk⟩) Expr.tru (by subst h; exact body)⟩, rest')
        else .error "lower: a forever body changes held marks"
      | .ok (_, _) => .error "lower: a forever is not closed"
    else .error "lower: assumption unknown"
  | _, _, _, _, _, _ => .error "lower: not a structured statement"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
