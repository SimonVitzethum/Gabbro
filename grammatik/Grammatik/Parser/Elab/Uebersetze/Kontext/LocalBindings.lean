module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.LoopHeaders
public import Grammatik.Parser.Elab.Uebersetze.Records.Records

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

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

/-- The binding the rest of the block reads after a narrowing: `x` at the narrowed range.
    The existing `narrowBeg` carries integral bounds, embedded exactly as float rationals;
    `finite` uses binary64's extreme endpoints. Fractional float ranges remain refused. -/
def uNarrowKopf (ctx : UCtx) (x : String) (t : String) : Except String (Int × Int × UCtx) :=
  match uParamNr ctx x with
  | .error e => .error e
  | .ok j =>
    match uArtBei ctx.kinds j, ctx.types[j]? with
    | .ok _, some (.fl ..) =>
      if strEq t "finite" then
        .ok (-uFloatLimit, uFloatLimit,
          uMitLokal ctx x .wert uFloatTy (ctx.muts.filter (fun m => !strEq m x)))
      else do
        let (lo, hi) ← uNarrowBereich ctx t
        pure (lo, hi, uMitLokal ctx x .wert (.fl (lo, 1) (hi, 1))
          (ctx.muts.filter (fun m => !strEq m x)))
    | .ok .int, _ =>
      match uNarrowBereich ctx t with
      | .error e => .error e
      | .ok (lo, hi) =>
        .ok (lo, hi, uMitLokal ctx x UParamArt.int (Ty.int lo hi) (ctx.muts.filter (fun m => !strEq m x)))
    | _, _ => .error "narrow of a non-number"

/-- The finite spelling retains a float binding and the exact binary64 bounds.
    No integer conversion or unchecked expression cast is involved. -/
theorem uNarrowKopf_floatFinite (ctx : UCtx) (x : String) (j : Nat) (lo hi : Int × Int)
    (k : UParamArt) (position : uParamNr ctx x = .ok j) (kind : uArtBei ctx.kinds j = .ok k)
    (typeAt : ctx.types[j]? = some (.fl lo hi)) :
    uNarrowKopf ctx x "finite" = .ok (-uFloatLimit, uFloatLimit,
      uMitLokal ctx x .wert uFloatTy (ctx.muts.filter (fun m => !strEq m x))) := by
  simp only [uNarrowKopf, position, kind, typeAt] <;> rfl

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
      | some ty@(.fl ..) | some ty@(.prod ..) | some ty@(.arr ..) | some ty@(.str ..) =>
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
  | .some ty@(.array _ _) | .some ty@(.str _) =>
    -- A `let mut` array or string is assigned as a whole (`x = v;`, `x[i] = v;` replaces an element).
    match uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner ty with
    | .error err => .error err
    | .ok τ =>
      match uWertBody ctx e with
      | .error err => .error err
      | .ok sd => .ok (.bindW x (some τ) sd, uMitLokal ctx x UParamArt.wert τ muts)
  | .some ty =>
    match uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner ty with
    | .ok ty@(.fl ..) | .ok ty@(.prod ..) => do
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


end Gabbro.Grammatik.Parser.Uebersetze
