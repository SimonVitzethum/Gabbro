module

public import Grammatik.Parser.Elab.Uebersetze.Narrowing

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The local names a guard compares directly with another side: the candidates for narrowing. -/
def uWaechterNamen : UEns → List String
  | .cmp _ (.param x) (.param y) => [x, y]
  | .cmp _ (.param x) _ => [x]
  | .cmp _ _ (.param y) => [y]
  | .and a b => uWaechterNamen a ++ uWaechterNamen b
  | .or a b => uWaechterNamen a ++ uWaechterNamen b
  | .not a => uWaechterNamen a
  | _ => []

/-- A context in which the names that carry no proved range cannot be found: the placeholder of an untyped
    local (`UCtx.unknownRanges`) and every `let mut` local. A guard says nothing about such a name, and
    nothing is read from its type. -/
def uWaechterCtx (ctx : UCtx) : UCtx :=
  { ctx with names := ctx.names.map (fun n =>
      if ctx.unknownRanges.any (strEq n) || ctx.muts.any (strEq n) then "#hidden" else n) }

/-- The range an immutable number local or parameter `v` is narrowed within: its type, when its kind is a
    plain number (an index, an option, a float and every other kind keep their binding). -/
def uWaechterBereich (ctx : UCtx) (v : String) : Option (Int × Int) :=
  match uParamNr ctx v with
  | .error _ => none
  | .ok j =>
    match uArtBei ctx.kinds j, ctx.types[j]? with
    | .ok .int, some (.int lo hi) => some (lo, hi)
    | _, _ => none

/-- Guard bounds, including exclusion of a literal at an end of the current inclusive range `lo .. hi`.
    Named constants have already become literals in `uBool`. Equality on the true path and inequality on
    the false path already get their singleton bounds from `uGrenzen`; only the opposite paths need this
    guard-specific rule. An interior exclusion gives no interval bound. Conjunctions on the true path and
    disjunctions on the false path intersect facts, exactly as in `uGrenzen`; negation reverses polarity.

    On these paths an immutable integer differs from the excluded endpoint, so it is at least `lo + 1`
    or at most `hi - 1`. Rebinding with the total `USide.eng` therefore preserves its value: the fallback
    cannot be reached. The shared `uGrenzen` and its `update`-arm callers retain their existing behaviour. -/
def uWaechterGrenzen (ctx : UCtx) (v : String) (lo hi : Int) : Bool → UEns → Option Int × Option Int
  | pos, .cmp op a b =>
    if (pos && strEq op "!=") || (!pos && strEq op "==") then
      let excluded : Option Int := match a, b with
        | .param x, .lit c | .lit c, .param x => if strEq x v then some c else none
        | _, _ => none
      match excluded with
      | some c =>
        if c == lo then (some (lo + 1), none)
        else if c == hi then (none, some (hi - 1)) else (none, none)
      | none => (none, none)
    else uGrenzen ctx v pos (.cmp op a b)
  | true, .and a b =>
    uGrenzen.uGrenzenUnd (uWaechterGrenzen ctx v lo hi true a) (uWaechterGrenzen ctx v lo hi true b)
  | false, .or a b =>
    uGrenzen.uGrenzenUnd (uWaechterGrenzen ctx v lo hi false a) (uWaechterGrenzen ctx v lo hi false b)
  | pos, .not a => uWaechterGrenzen ctx v lo hi (!pos) a
  | pos, cv => uGrenzen ctx v pos cv

/-- What the guard `cv` fixes about `v` when it holds (`pos`) or fails: the narrowed range, when it is a
    non-empty proper part of the range of `v`. Guard bounds extend the shared `uGrenzen` bounds only with
    endpoint exclusions (`uWaechterGrenzen`). Empty and unchanged intersections still give no fact. -/
def uWaechterEnge (ctx : UCtx) (v : String) (pos : Bool) (cv : UEns) : Option (Int × Int) :=
  match uWaechterBereich ctx v with
  | none => none
  | some (lo, hi) =>
    let g := uWaechterGrenzen ctx v lo hi pos cv
    let lo' := match g.1 with | some a => max lo a | none => lo
    let hi' := match g.2 with | some b => min hi b | none => hi
    if lo' ≤ hi' && !(lo' == lo && hi' == hi) then some (lo', hi') else none

/-- The narrowings one side of a guard brings, each local once, in the order the guard names them. Every range
    is computed in the context before any of them is applied. -/
def uWaechterFakten (ctx : UCtx) (cv : UEns) (pos : Bool) : List (String × Int × Int) :=
  let hidden := uWaechterCtx ctx
  (uWaechterNamen cv).foldl (fun (acc : List (String × Int × Int)) v =>
    if acc.any (fun f => strEq f.1 v) then acc
    else
      match uWaechterEnge hidden v pos cv with
      | some (lo, hi) => acc ++ [(v, lo, hi)]
      | none => acc) []

/-- `let v : lo .. hi = <v narrowed to lo .. hi>;` as one statement (the value form `USide.eng`, no `else` and
    no return path), and the context in which `v` is an immutable number of that range. The storage width of
    the old binding stays, so `~v` reads the same bits. -/
def uWaechterBindung (ctx : UCtx) (v : String) (lo hi : Int) : UStmt × UCtx :=
  let bits : Nat := match uParamNr ctx v with
    | .ok j => ctx.bits.getD j 0
    | .error _ => 0
  (UStmt.bind v (some (lo, hi)) (USide.eng (USide.param v) lo hi),
   { ctx with names := v :: ctx.names, kinds := UParamArt.int :: ctx.kinds,
              types := Ty.int lo hi :: ctx.types, bits := bits :: ctx.bits })

/-- The rebindings of a list of narrowings, in order. -/
def uWaechterBinde (ctx : UCtx) : List (String × Int × Int) → List UStmt × UCtx
  | [] => ([], ctx)
  | (v, lo, hi) :: rest =>
    let (stmt, ctx') := uWaechterBindung ctx v lo hi
    let (stmts, ctx'') := uWaechterBinde ctx' rest
    (stmt :: stmts, ctx'')


/-! ### The names a block reads

A narrowing costs one range test in every branch it is applied to (and declared `costs` count it), so a branch
narrows only the locals it reads. The walks below over-approximate the reads: every name an expression or a
statement mentions counts, shadowing is ignored, and `"*"` stands for every name (a raw statement, raw loop
words, a walk out of fuel). Narrowing a name that is not read costs one test and is never unsound; not
narrowing a read name only leaves it at its declared range. -/

/-- The fuel of the read walks: the nesting depth of statements and expressions they follow. -/
def uLiestTiefe : Nat := 256

/-- The names an expression mentions. -/
def uLiestE : Nat → SExpr → List String
  | 0, _ => ["*"]
  | f + 1, e => match e with
    | .variable s => [s]
    | .field x _ | .arrow x _ | .un _ x | .old x => uLiestE f x
    | .index x i | .bin _ x i => uLiestE f x ++ uLiestE f i
    | .call g xs => g :: xs.flatMap (uLiestE f)
    | .fnref p => [p]
    | .built _ xs => xs.flatMap (uLiestE f)
    | .why g _ => [g]
    | .ext _ ws xs => ws ++ xs.flatMap (uLiestE f)
    | _ => []

/-- The names a type mentions in its bounds (a bound is a constant expression; a raw or linked type
    mentions none the branch could read). -/
def uLiestT : Nat → STyp → List String
  | 0, _ => ["*"]
  | f + 1, t => match t with
    | .ptr _ _ b | .wrap b => uLiestT f b
    | .range b lo hi _ => uLiestT f b ++ uLiestE f lo ++ uLiestE f hi
    | .array b n => uLiestT f b ++ uLiestE f n
    | .embed b _ x => uLiestT f b ++ (x.map (uLiestE f)).getD []
    | .str n => uLiestE f n
    | _ => []

/-- The names an optional type mentions. -/
def uLiestTO (f : Nat) (ty : Option STyp) : List String := (ty.map (uLiestT f)).getD []

/-- The names a statement mentions, nested blocks included. -/
def uLiestS : Nat → SAnw → List String
  | 0, _ => ["*"]
  | f + 1, a => match a with
    | .bind _ _ ty e | .bindQ _ _ ty e | .bindAxiomOpt _ ty e | .await _ ty e _ | .swap _ ty e _ =>
      uLiestTO f ty ++ uLiestE f e
    | .bindElse _ ty e _ b | .bindAxiomOptElse _ ty e _ b => uLiestTO f ty ++ uLiestE f e ++ uLiestS f b
    | .bindLib _ _ ty c =>
      uLiestTO f ty ++ c.args.flatMap (uLiestE f) ++ c.region.filterMap (fun | .ident s => some s | _ => none)
    | .lcall c => c.args.flatMap (uLiestE f) ++ c.region.filterMap (fun | .ident s => some s | _ => none)
    | .set p _ v | .emit p v _ => uLiestE f p ++ uLiestE f v
    | .shift p _ _ | .free p | .trimReq p _ => uLiestE f p
    | .call g xs | .callQ g xs | .genericCall g _ xs => g :: xs.flatMap (uLiestE f)
    | .callElse g xs _ b => g :: xs.flatMap (uLiestE f) ++ uLiestS f b
    | .callIndElse p xs _ b => uLiestE f p ++ xs.flatMap (uLiestE f) ++ uLiestS f b
    | .cond c t ei e =>
      uLiestE f c ++ uLiestS f t ++ ei.flatMap (uLiestS f) ++ (e.map (uLiestS f)).getD []
    | .elsif c b | .trim c _ b | .locks _ c b => uLiestE f c ++ uLiestS f b
    | .cases c as => uLiestE f c ++ as.flatMap (uLiestS f)
    | .arm _ _ b | .retry _ b | .loop _ b | .waive _ b | .watch _ b | .child b => uLiestS f b
    | .each _ o _ s _ r i b =>
      (o.map (uLiestE f)).getD [] ++ uLiestE f s ++ (if strEq r "" then [] else ["*"]) ++
        (i.map (uLiestE f)).getD [] ++ uLiestS f b
    | .step x y => [x, y]
    | .ret v => (v.map (uLiestE f)).getD []
    | .alloc _ _ ty _ e b => uLiestTO f ty ++ uLiestE f e ++ (b.map (uLiestS f)).getD []
    | .allocVon _ _ ty _ => uLiestTO f ty
    | .reset x p => x :: (match p with | some (lo, n) => uLiestE f lo ++ uLiestE f n | none => [])
    | .grow x e b => x :: uLiestE f e ++ uLiestS f b
    | .block as en =>
      as.flatMap (uLiestS f) ++ (match en with | some (.ret (some v)) => uLiestE f v | _ => [])
    | .other _ => ["*"]
    | _ => []

/-- The names a run of statements mentions. -/
def uLiestL (ss : List SAnw) : List String := ss.flatMap (uLiestS uLiestTiefe)

/-- Whether a name is among the names read (`"*"` reads every name). -/
def uGelesen (reads : List String) (v : String) : Bool := reads.any (fun n => strEq n v || strEq n "*")

/-- The narrowings of the locals a block reads. -/
def uWaechterGelesen (reads : List String) (fs : List (String × Int × Int)) : List (String × Int × Int) :=
  fs.filter (fun fct => uGelesen reads fct.1)

end Gabbro.Grammatik.Parser.Uebersetze
