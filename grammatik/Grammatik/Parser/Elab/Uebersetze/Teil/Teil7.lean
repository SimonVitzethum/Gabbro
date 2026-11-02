module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Transition.Resolve

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- `place = v;` at a slot or a static (the place reader decides which). -/
def uSetzePlatz (ctx : UCtx) (ziel wert : SExpr) : Except String UStmt :=
  match uZugriff ctx ziel with
  | .error e => uGlobSchreib ctx ziel wert e
  | .ok (.thru b, tb, f, ix) =>
    match uStelle ctx.names b with
    | .error e => .error e
    | .ok j =>
      match uArtBei ctx.kinds j with
      | .ok (.ptr ⟨0, ⟨_, true, none⟩, .table _⟩) =>
        if (uOptFeld ctx tb f).isSome then
          match uOptFeld ctx tb f with
          | .none => .error "option field without G form"
          | .some num =>
            match uOpt ctx num wert with
            | .error e => .error e
            | .ok v => .ok (.assignOpt b f ix v)
        else
        if uBoolFeld ctx tb f then
          match uBool ctx wert with
          | .error e => .error e
          | .ok v => .ok (.assignB b f ix v)
        else
          match uWertBody ctx wert with
          | .error e => .error e
          | .ok v => .ok (.assign b f ix (uWrap ctx tb f v))
      | _ => .error "write through a read pointer"
  | .ok (.tabelle b, tb, f, ix) =>
    if (uOptFeld ctx tb f).isSome then
      match uOptFeld ctx tb f with
      | .none => .error "option field without G form"
      | .some num =>
        match uOpt ctx num wert with
        | .error e => .error e
        | .ok v => .ok (.assignTabOpt b f ix v)
    else
    if uBoolFeld ctx tb f then
      match uBool ctx wert with
      | .error e => .error e
      | .ok v => .ok (.assignTabB b f ix v)
    else
      match uWertBody ctx wert with
      | .error e => .error e
      | .ok v => .ok (.assignTab b f ix (uWrap ctx tb f v))

/-- `x = v;` at a `let mut` local. -/
def uSetzeLokal (ctx : UCtx) (x : String) (wert : SExpr) : Except String UStmt :=
  match uParamNr ctx x with
  | .error e => .error e
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok .int =>
      match uWertBody ctx wert with
      | .error e => .error e
      | .ok v => .ok (.setVar x v)
    | .ok .bool =>
      match uBool ctx wert with
      | .error e => .error e
      | .ok v => .ok (.setVarB x v)
    | _ => .error "assignment to a pointer or an index"

/-- The binary operator of a compound assignment `x op= v` (the surface has `+= -= &= |=`). -/
def uOpBasis : String → Option String
  | "+=" => some "+"
  | "-=" => some "-"
  | "&=" => some "&"
  | "|=" => some "|"
  | _ => none

/-- An assignment, plain or compound (`p op= v` is `p = p op v`): a `let mut` local, a slot or a static. -/
def uSetze (ctx : UCtx) (ziel : SExpr) (op : String) (wert : SExpr) : Except String UStmt :=
  match (if strEq op "=" then some wert else (uOpBasis op).map fun b => SExpr.bin b ziel wert) with
  | none => .error "stmt without G form"
  | some w =>
    match ziel with
    | .variable x => if ctx.muts.any (strEq · x) then uSetzeLokal ctx x w else uSetzePlatz ctx ziel w
    | .arrow (.variable r) f =>
      match uRefLokal ctx r with
      | .some _ =>
        match uWertBody ctx w with
        | .error e => .error e
        | .ok v => .ok (.assignRef r f v)
      | .none => uSetzePlatz ctx ziel w
    | _ => uSetzePlatz ctx ziel w

/-- A call through a local function pointer `p` (bound by `let p = &f;`): `some` of the head of the function it
    points at; `none` when `p` is no such local. -/
def uFnZeiger (ctx : UCtx) (koepfe : List UFnKopf) (p : String) : Option (Except String UFnKopf) :=
  match uParamNr ctx p with
  | .error _ => none
  | .ok j =>
    match uArtBei ctx.kinds j with
    | .ok (.fnptr n) =>
      if n < ctx.zeigerBasis then
        some (match koepfe[n]? with
          | some k => .ok k
          | none => .error "function pointer to no function")
      else
        -- a pointer of a declared pointer type: the head of the type (`fn#j`)
        some (match koepfe.find? (fun (k : UFnKopf) => strEq k.name ("fn#" ++ toString (n - ctx.zeigerBasis))) with
          | some k => .ok k
          | none => .error "function pointer of no type")
    | _ => none

/-- The kind word of a statement, named in a refusal. -/
def anwArt : SAnw → String
  | .bind .. => "let" | .bindElse .. => "let else"
  | .bindAxiomOpt .. => "let?" | .bindAxiomOptElse .. => "let? else" | .bindLib .. => "library let" | .set .. => "assignment"
  | .shift .. => "shift" | .call .. => "call" | .lcall .. => "library call" | .cond .. => "if"
  | .elsif .. => "else if" | .cases .. => "match" | .arm .. => "match arm" | .each .. => "traverse"
  | .retry .. => "retry" | .loop .. => "loop" | .waive .. => "waive" | .trim .. => "trim" | .locks .. => "locks"
  | .watch .. => "watch" | .leave .. => "leave" | .next .. => "next" | .emit .. => "emit" | .await .. => "await"
  | .swap .. => "exchange" | .step .. => "step" | .ret .. => "return" | .alloc .. => "alloc" | .reset .. => "reset"
  | .grow .. => "grow" | .free .. => "free" | .child .. => "child" | .start .. => "start" | .other w => w
  | .block .. => "block" | .allocVon .. => "alloc from a provider"

/-- One body statement: an assignment or a direct call (the
    `tr_stmt` of `lean_g.rs`; mid-body `return` and every other statement are explicit errors). -/
def uAnw1 (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) :
    SAnw → Except String UStmt
  | .set ziel op wert =>
    match uRegOrt ctx ziel with
    | some (.error e) => .error e
    | some (.ok rg) =>
      if !strEq op "=" then .error "compound register write without G form"
      else if rg.bool then
        match uBool ctx wert with
        | .error e => .error e
        | .ok b => .ok (.regWriteB rg.dev rg.name b)
      else
        match uWertBody ctx wert with
        | .error e => .error e
        | .ok s => .ok (.regWrite rg.dev rg.name s)
    | none => uSetze ctx ziel op wert
  | .emit ziel wert p => uAtomSchreib ctx ziel wert p
  | .shift z von nach =>
    match uZugriff ctx z with
    | .error e => .error e
    | .ok (.thru .., _, _, _) => .error "transition through a pointer without G form"
    | .ok (.tabelle _, tb, f, ix) =>
      uTransitionAt ctx.zustaende tb f ix von nach
  | .reset a .none =>
    if ctx.tabs.any (fun x => x.arena && strEq x.name a) then .ok (.assignGlob (a ++ "#used") (.lit 0))
    else .error ("arena unknown: " ++ a)
  /- `reset A at i count n;` over a zero-initialized static array (C18): the static as
      written must be a declared static array (`GTy.wert (.arr ..)`); the two operands
      elaborate as body values and travel as `UStmt.resetRange` metadata. Range validity
      (`0 ≤ i`, `n ≤ len`, `i ≤ len - n`) and the zero observation are user duties
      discharged at lowering, which refuses the metadata until the C18 range-store proof
      and the page-return bridge are connected. -/
  | .reset a (some (i, n)) =>
    match ctx.globs.find? (fun g => strEq g.name a) with
    | none => .error ("static unknown: " ++ a)
    | some g => match g.ty with
      | .wert (.arr _ _) =>
        match uWertBody ctx i with
        | .error e => .error e
        | .ok iu => match uWertBody ctx n with
          | .error e => .error e
          | .ok nu => .ok (.resetRange a iu nu)
      | _ => .error ("reset range of a static that is not a static array: " ++ a)
  | .call c args =>
    match uNamedTransition ctx.zustaende c with
    | some (.error message) => .error message
    | some (.ok (state, tr)) =>
      if koepfe.any (fun head => strEq head.name c) then
        .error "transition name conflicts with an ordinary function"
      else if !args.isEmpty then .error "transition call takes no explicit arguments"
      else if tr.primitive then .error "constant field transition requires an explicit target"
      else
        match uTransitionArguments tr none with
        | .error message => .error message
        | .ok snapshots => .ok (.call (uTransitionFunction state tr.name) snapshots)
    | none =>
    match uFnZeiger ctx koepfe c with
    | some (.error e) => .error e
    | some (.ok ziel) =>
      match uRuf ctx tabs koepfe ziel.name args with
      | .error e => .error e
      | .ok (callee, xs) =>
        if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
        else .ok (.callInd c callee.name xs)
    | none =>
    match uRuf ctx tabs koepfe c args with
    | .error e => .error e
    | .ok (callee, xs) =>
      if callee.kanal.isSome then .error "call of a function with a reason channel needs `let .. else`"
      else .ok (if callee.ext then .axCall c xs else .call c xs)
  | .start _ =>
    if ctx.held.isEmpty then .ok .startS else .error "start under a held lock: the start step has an empty held list"
  | s => .error ("stmt without G form: " ++ anwArt s)

/-- A written binder type at a read of the static `A` (`awaits`, `exchange`): it must be `A`'s own type. -/
def uBinderTyp (ctx : UCtx) (wo : String) : Option STyp → GTy → Except String Unit
  | .none, _ => .ok ()
  | .some (.atom "bool"), .bool => .ok ()
  | .some t, .int lo hi =>
    match uErgBereich ctx.alias t with
    | .ok (l, h) => if l == lo && h == hi then .ok () else .error (wo ++ " binder typed other than its static")
    | .error err => .error err
  | .some _, _ => .error (wo ++ " binder typed other than its static")

/-- The names in braces at the head of `ts` (`{ p, q }`), and what follows. -/
def uKlammerNamen : List Token → Option (List String × List Token)
  | .zeichen "{" :: ts =>
    let innen := ts.takeWhile (fun t => t != .zeichen "}")
    match ts.dropWhile (fun t => t != .zeichen "}") with
    | .zeichen "}" :: rest =>
      if innen.all (fun t => match t with | .ident _ => true | .zeichen "," => true | _ => false) then
        some (innen.filterMap (fun t => match t with | .ident n => some n | _ => none), rest)
      else none
    | _ => none
  | _ => none

/-- The clauses behind an exchange: `[publishes nothing | publishes { … }] [awaits { … }]`. The payload names
    (empty for `nothing` or no clause) and the `awaits` names, if any. -/
def uTauschKlauseln : List Token → Except String (List String × Option (List String))
  | ts =>
    let (pub, ts1) : List String × List Token := match ts with
      | .wort "publishes" :: .wort "nothing" :: r => ([], r)
      | .wort "publishes" :: r => (match uKlammerNamen r with | some (ns, r') => (ns, r') | none => ([], .wort "publishes" :: r))
      | r => ([], r)
    match ts1 with
    | [] => .ok (pub, none)
    | .wort "awaits" :: r =>
      match uKlammerNamen r with
      | some (ns, []) => .ok (pub, some ns)
      | _ => .error "exchange clause without G form"
    | _ => .error "exchange clause without G form"

/-- The value an arm of an `update` body returns: `{ return e; }`. -/
def uArmWert : SAnw → Option SExpr
  | .block [] (some (.ret (some e))) => some e
  | _ => none

/-- An `update` body as guarded values and a last value: `if c₁ { return e₁; } else if … else { return e; }`, or
    `if c₁ { return e₁; } … return e;`. Fuel for the chain. -/
def uZweige : Nat → SAnw → Option (List (SExpr × SExpr) × SExpr)
  | 0, _ => none
  | _ + 1, .block [] (some (.ret (some e))) => some ([], e)
  | f + 1, .block (.cond c t ei els :: rest) ende =>
    match uArmWert t with
    | none => none
    | some e1 =>
      let weiter : Option SAnw := match ei, els with
        | .elsif c2 b2 :: ei', _ => some (.block (.cond c2 b2 ei' els :: rest) ende)
        | [], some b => if rest.isEmpty && ende.isNone then some b else none
        | [], none => some (.block rest ende)
        | _, _ => none
      match weiter.bind (uZweige f) with
      | some (zs, s) => some ((c, e1) :: zs, s)
      | none => none
  | _ + 1, _ => none

/-- `old(A)` in the predicate of a compare-exchange is the old value of `A`, the local `#alt`. Fuel for the depth. -/
def uAltErsetze (a : String) : Nat → SExpr → SExpr
  | 0, e => e
  | _ + 1, .old (.variable b) => if strEq a b then .variable "#alt" else .old (.variable b)
  | f + 1, .un o e => .un o (uAltErsetze a f e)
  | f + 1, .bin o x y => .bin o (uAltErsetze a f x) (uAltErsetze a f y)
  | f + 1, .call n args => .call n (args.map (uAltErsetze a f))
  | _ + 1, e => e

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
    .product identity reordered (fields.map (fun (ty, side) => (ty, uSideEng v lo hi side)))
  | .field base name => .field (uSideEng v lo hi base) name
  | .replace base name value => .replace (uSideEng v lo hi base) name (uSideEng v lo hi value)
  | s => s

/-- The value of an `update` arm with `v` narrowed by the arm's guard (`pos` the arm's own condition, `negs` the
    conditions of the arms before it, all false there), inside the static's range `slo .. shi`. -/
def uArmEng (ctx : UCtx) (v : String) (slo shi : Int) (pos : Option UEns) (negs : List UEns) (s : USide) : USide :=
  let gs := (match pos with | some c => [uGrenzen ctx v true c] | none => []) ++ negs.map (uGrenzen ctx v false)
  let lo := gs.foldl (fun acc g => match g.1 with | some x => max acc x | none => acc) slo
  let hi := gs.foldl (fun acc g => match g.2 with | some x => min acc x | none => acc) shi
  if lo == slo && hi == shi then s else if lo ≤ hi then uSideEng v lo hi s else s

/-- An exchange as read from its tail: the update binder, the guarded values, the last value, the payload, the
    `awaits` names, and whether it is the compare form (whose binder is the success, a truth value). -/
structure UTausch where
  v : String
  zweige : List (SExpr × SExpr)
  sonst : SExpr
  pub : List String
  aw : Option (List String)
  vergleich : Option SExpr

/-- The tail of an exchange (`exchstmt` of SYNTAX.md): `update(v) [bounded n ops] [on_exceeded k] { … } [clauses]`,
    or `e when p returns r [clauses]` (compare-exchange: the new value `e` if `p` holds of the old value, else the
    old value; the binder is `p`, Rust `kosten.rs`). The bound and the exit belong to the lowering (G takes the
    exchange as one atomic step, A10). -/
def uTauschSchwanz (a k : String) : Except String UTausch :=
  match lex k with
  | .error _ => .error "exchange without G form"
  | .ok toks0 =>
    let toks := toks0.filter (fun t => match t with | .ende => false | _ => true)
    let fuel := 8 * toks.length + 30
    match toks with
    | .wort "update" :: .zeichen "(" :: .ident v :: .zeichen ")" :: rest =>
      match rest.dropWhile (fun t => t != .zeichen "{") with
      | .zeichen "{" :: innen =>
        match parseBlock fuel (.zeichen "{" :: innen) with
        | .ok (b, kl) =>
          match uZweige 64 b, uTauschKlauseln kl with
          | some (zs, s), .ok (pub, aw) => .ok ⟨v, zs, s, pub, aw, none⟩
          | none, _ => .error "exchange update body other than guarded values without G form"
          | _, .error err => .error err
        | .error _ =>
          -- an expression body `{ e }`
          match parseOr fuel innen with
          | .error _ => .error "exchange update body without G form"
          | .ok (e, .zeichen "}" :: kl) =>
            match uTauschKlauseln kl with
            | .error err => .error err
            | .ok (pub, aw) => .ok ⟨v, [], e, pub, aw, none⟩
          | .ok (_, _) => .error "exchange update body other than one value without G form"
      | _ => .error "exchange update without a body"
    | _ =>
      match parseOr fuel toks with
      | .ok (neu, .wort "when" :: r1) =>
        match parseOr fuel r1 with
        | .ok (p, .wort "returns" :: .ident _ :: kl) =>
          match uTauschKlauseln kl with
          | .error err => .error err
          | .ok (pub, aw) =>
            let p' := uAltErsetze a 64 p
            .ok ⟨"#alt", [(p', neu)], .variable "#alt", pub, aw, some p'⟩
        | _ => .error "exchange compare form without G form"
      | _ => .error "exchange without G form"

/-- The context after `let x [: T]`: the annotated range (when there is one) and the context in which the
    rest of the block reads `x` as a numeric parameter that shadows any earlier name. -/
def uBindKopf (ctx : UCtx) (x : String) : Option STyp → Except String (Option (Int × Int) × UCtx)
  | .none =>
    .ok (.none, { ctx with names := x :: ctx.names, kinds := .int :: ctx.kinds,
                           types := .int 0 0 :: ctx.types, bits := 0 :: ctx.bits })
  | .some ty =>
    match uErgBereich ctx.alias ty with
    | .error e => .error e
    | .ok (lo, hi) =>
      .ok (.some (lo, hi), { ctx with names := x :: ctx.names, kinds := .int :: ctx.kinds,
                                      types := .int lo hi :: ctx.types,
                                      bits := uParamBreite ty :: ctx.bits })

/-- The context after a local `x` of kind `k` and type `ty`. -/
def uMitLokal (ctx : UCtx) (x : String) (k : UParamArt) (ty : Ty) (muts : List String) : UCtx :=
  { ctx with names := x :: ctx.names, kinds := k :: ctx.kinds, types := ty :: ctx.types, bits := 0 :: ctx.bits, muts := muts }

/-- The words that start a section of a `retry`/`forever` header. -/
def uSchleifenWort (s : String) : Bool :=
  strEq s "until" || strEq s "bounded" || strEq s "per_pass" || strEq s "progress" ||
    strEq s "on_exceeded" || strEq s "effects" || strEq s "leaves"

/-- A loop header split into its sections: the key word (empty for the leading label) and the tokens up to
    the next key word at brace depth zero. -/
def uKopfAbschnitte : List Token → Nat → String → List Token → List (String × List Token) →
    List (String × List Token)
  | [], _, k, acc, out => out ++ [(k, acc.reverse)]
  | t :: rest, d, k, acc, out =>
    match t with
    | .zeichen "{" => uKopfAbschnitte rest (d + 1) k (t :: acc) out
    | .zeichen "}" => uKopfAbschnitte rest (d - 1) k (t :: acc) out
    | .wort w =>
      if d == 0 && uSchleifenWort w then uKopfAbschnitte rest d w [] (out ++ [(k, acc.reverse)])
      else uKopfAbschnitte rest d k (t :: acc) out
    | .ident w =>
      if d == 0 && uSchleifenWort w then uKopfAbschnitte rest d w [] (out ++ [(k, acc.reverse)])
      else uKopfAbschnitte rest d k (t :: acc) out
    | _ => uKopfAbschnitte rest d k (t :: acc) out

/-- The tokens of a section by key word. -/
def uAbschnitt (secs : List (String × List Token)) (k : String) : Option (List Token) :=
  (secs.find? (fun s => strEq s.1 k)).map (·.2)

/-- A loop header's sections (the raw header of `SAnw.retry`/`SAnw.loop` read again by the lexer). -/
def uSchleifenKopf2 (h : String) : Except String (List (String × List Token)) :=
  match lex h with
  | .error _ => .error "loop header without G form"
  | .ok toks0 => .ok (uKopfAbschnitte (toks0.filter (fun k => match k with | .ende => false | _ => true)) 0 "" [] [])

/-- A name section: one word. -/
def uEinName : Option (List Token) → Option String
  | some [.ident n] => some n
  | some [.wort n] => some n
  | _ => none

/-- `bounded N ops`. -/
def uOpsZahl (ctx : UCtx) : Option (List Token) → Option Nat
  | some [.num n, .wort _] => some n
  | some [.num n, .ident _] => some n
  | some [.ident c, .wort _] => (ctx.lits.find? (fun k => strEq k.1 c)).bind fun k => if 0 ≤ k.2 then some k.2.toNat else none
  | _ => none

end Gabbro.Grammatik.Parser.Uebersetze
