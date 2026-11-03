module

public import Grammatik.Parser.Elab.Uebersetze.Records.Records

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The range a side of a guard is known to lie in: a literal, or a number local or parameter at its type. -/
def uSeiteBereich (ctx : UCtx) : USide → Option (Int × Int)
  | .lit k => some (k, k)
  | .param p =>
    match uParamNr ctx p with
    | .ok j => match ctx.types[j]? with | some (.int lo hi) => some (lo, hi) | _ => none
    | .error _ => none
  | _ => none

/-- What a guard says about the local `v`: a lower and an upper bound, from comparisons with a side of known range
    `x .. y` (a literal, or a number local: `v < X` gives `v ≤ y - 1`) under `and` (and their negations,
    `pos = false`, under `or`); anything else says nothing. -/
def uGrenzen (ctx : UCtx) (v : String) : Bool → UEns → Option Int × Option Int
  | pos, .cmp op (.param x) s =>
    if !strEq x v then
      (match s with
       | .param y => if strEq y v then (match uSeiteBereich ctx (.param x) with
           | some r => uGrenzeCmp pos (uDreh op) r | none => (none, none)) else (none, none)
       | _ => (none, none))
    else match uSeiteBereich ctx s with | some r => uGrenzeCmp pos op r | none => (none, none)
  | pos, .cmp op s (.param x) =>
    if !strEq x v then (none, none)
    else match uSeiteBereich ctx s with | some r => uGrenzeCmp pos (uDreh op) r | none => (none, none)
  | true, .and a b => uGrenzenUnd (uGrenzen ctx v true a) (uGrenzen ctx v true b)
  | false, .or a b => uGrenzenUnd (uGrenzen ctx v false a) (uGrenzen ctx v false b)
  | pos, .not a => uGrenzen ctx v (!pos) a
  | _, _ => (none, none)
where
  /-- `v op X` (or its negation) as bounds of `v`, for `X` in `r.1 .. r.2`. -/
  uGrenzeCmp (pos : Bool) (op : String) (r : Int × Int) : Option Int × Option Int :=
    if pos then
      if strEq op "<" then (none, some (r.2 - 1)) else if strEq op "<=" then (none, some r.2)
      else if strEq op ">" then (some (r.1 + 1), none) else if strEq op ">=" then (some r.1, none)
      else if strEq op "==" then (some r.1, some r.2) else (none, none)
    else
      if strEq op "<" then (some r.1, none) else if strEq op "<=" then (some (r.1 + 1), none)
      else if strEq op ">" then (none, some r.2) else if strEq op ">=" then (none, some (r.2 - 1))
      else if strEq op "!=" then (some r.1, some r.2) else (none, none)
  /-- `k op x` read as `x op' k`. -/
  uDreh (op : String) : String :=
    if strEq op "<" then ">" else if strEq op "<=" then ">=" else if strEq op ">" then "<"
    else if strEq op ">=" then "<=" else op
  /-- Both bounds hold: the tighter of each. -/
  uGrenzenUnd (a b : Option Int × Option Int) : Option Int × Option Int :=
    (match a.1, b.1 with | some x, some y => some (max x y) | some x, none => some x | none, y => y,
     match a.2, b.2 with | some x, some y => some (min x y) | some x, none => some x | none, y => y)

/-- Every read of the local `v` in `s` narrowed to `lo .. hi` (`USide.eng`). -/
def uSideEng (v : String) (lo hi : Int) : USide → USide
  | .param p => if strEq p v then .eng (.param p) lo hi else .param p
  | .add a b => .add (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .sub a b => .sub (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .mul a b => .mul (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .conv l h a => .conv l h (uSideEng v lo hi a)
  | .band a b => .band (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .bor a b => .bor (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .bxor a b => .bxor (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .div a b => .div (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .rem a b => .rem (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .shl a b => .shl (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .shr a b => .shr (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .neg a => .neg (uSideEng v lo hi a)
  | .ib1 o w a => .ib1 o w (uSideEng v lo hi a)
  | .ib2 o w a b => .ib2 o w (uSideEng v lo hi a) (uSideEng v lo hi b)
  | .product identity reordered fields =>
    .product identity reordered (fields.attach.map (fun field => (field.val.1, uSideEng v lo hi field.val.2)))
  | .field base name => .field (uSideEng v lo hi base) name
  | .replace base name value => .replace (uSideEng v lo hi base) name (uSideEng v lo hi value)
  | s => s
termination_by side => sizeOf side
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have smaller := recordField_sizeOf_lt fields field.val field.property
      omega

/-- Narrowing retains exactly the original ordered product fields. -/
theorem uSideEng_product (v : String) (lo hi : Int) (identity : Nat) (reordered : Bool) (fields : List (Ty × USide)) :
    uSideEng v lo hi (.product identity reordered fields) =
      .product identity reordered (fields.map (fun field => (field.1, uSideEng v lo hi field.2))) := by
  rw [uSideEng]; exact congrArg (USide.product identity reordered) (List.attach_map_val (l := fields) (f := fun field => (field.1, uSideEng v lo hi field.2)))

/-- The value of an `update` arm with `v` narrowed by the arm's guard (`pos` the arm's own condition, `negs` the
    conditions of the arms before it, all false there), inside the static's range `slo .. shi`. -/
def uArmEng (ctx : UCtx) (v : String) (slo shi : Int) (pos : Option UEns) (negs : List UEns) (s : USide) : USide :=
  let gs := (match pos with | some c => [uGrenzen ctx v true c] | none => []) ++ negs.map (uGrenzen ctx v false)
  let lo := gs.foldl (fun acc g => match g.1 with | some x => max acc x | none => acc) slo
  let hi := gs.foldl (fun acc g => match g.2 with | some x => min acc x | none => acc) shi
  if lo == slo && hi == shi then s else if lo ≤ hi then uSideEng v lo hi s else s

end Gabbro.Grammatik.Parser.Uebersetze
