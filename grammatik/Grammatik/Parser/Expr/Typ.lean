/-
  File:      Grammatik/Parser/Expr/Typ.lean
  Subject:   T3: the surface type `STyp` (SYNTAX.md section 2, `typeexpr`) and its reader. It stood in
             `ElementTief.lean`; statements carry types now (`let x : T = e;`), so the type reader
             comes before the statement reader.
-/
import Grammatik.Parser.Expr.Tokens

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/- A surface type: SYNTAX.md section 2 `typeexpr` without spans or
    checks. `atom` is one name, `path` a `::` path, `ptr` a
    `ptr<space, rights>` capability, `index` an `[option] index
    into T`, `bereich` a `base in lo .. hi` range (`exkl` for
    `..<`), `reihe` an array, `wrap` a `wrapping` width and
    `embed` an `embeds [hi:lo] [scale e]` field. A brace or
    `fn(…)` group (`structty`, `variants`, `fnptr`) rides `roh`,
    balanced but uninterpreted (see CUTS). -/
inductive STyp
  | atom : String → STyp
  | path : List String → STyp
  | ptr : String → String → STyp → STyp
  | index : Bool → String → STyp
  | range : STyp → SExpr → SExpr → Bool → STyp
  | array : STyp → SExpr → STyp
  | wrap : STyp → STyp
  | embed : STyp → String → Option SExpr → STyp
  | raw : String → STyp
  /-- `string max N` (`stringty`): the bound as an expression. -/
  | str : SExpr → STyp
  /-- `entry fn(params) [-> T]` (`entryfn`): the parameter words raw, the result type read. -/
  | entry : String → Option STyp → STyp
  deriving Repr

-- Shape equality on surface types, as a `Bool`: one recursive
-- function plus the list helper, exactly like
-- `beqSExpr`/`beqSExprList` (which reduce by kernel evaluation).
mutual
def beqSTyp : STyp → STyp → Bool
  | .atom a, .atom b => strEq a b
  | .path a, .path b => beqWorte a b
  | .ptr r1 w1 t1, .ptr r2 w2 t2 =>
    strEq r1 r2 && strEq w1 w2 && beqSTyp t1 t2
  | .index o1 t1, .index o2 t2 => (o1 == o2) && strEq t1 t2
  | .range b1 l1 h1 x1, .range b2 l2 h2 x2 =>
    beqSTyp b1 b2 && beqSExpr l1 l2 && beqSExpr h1 h2 && (x1 == x2)
  | .array t1 n1, .array t2 n2 => beqSTyp t1 t2 && beqSExpr n1 n2
  | .wrap t1, .wrap t2 => beqSTyp t1 t2
  | .embed b1 s1 x1, .embed b2 s2 x2 =>
    beqSTyp b1 b2 && strEq s1 s2 && beqOptExpr x1 x2
  | .raw a, .raw b => strEq a b
  | .str a, .str b => beqSExpr a b
  | .entry a x, .entry b y => strEq a b && beqSTypOpt x y
  | _, _ => false
def beqSTypOpt : Option STyp → Option STyp → Bool
  | none, none => true
  | some a, some b => beqSTyp a b
  | _, _ => false
def beqSTypList : List STyp → List STyp → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSTyp x y && beqSTypList xs ys
  | _, _ => false
end

/-- The clause head words of `fndecl` (SYNTAX.md section 6). -/
def istKlauselKopf (s : String) : Bool :=
  ["requires", "ensures", "maintains", "refines", "effects",
   "costs", "deadline", "decreases", "by", "section", "arch",
   "payload", "advances", "retires"].any (strEq · s)

/-- A `::` path: one name plus `sammleSegmente`. -/
def nimmPfad : List Token → Except String (List String × List Token)
  | t :: rest => match nameText t with
    | some s => let (segs, r) := sammleSegmente rest [s]; .ok (segs, r)
    | none => .error "path expected"
  | [] => .error "path expected"

/-- A string literal token (claims, sections, assumptions). -/
def nimmTextTok : List Token → Except String (String × List Token)
  | .text s :: rest => .ok (s, rest)
  | _ => .error "string expected"

/-- Is the next token this punctuation? -/
def istZeichenZ (z : String) : List Token → Bool
  | .zeichen s :: _ => strEq s z
  | _ => false

/-- Raw words of a balanced group whose opener is already
    counted (`pr`/`pk`/`pg` are the pending `)`/`]`/`}`).
    Structural on the token list. -/
def sammleAusgewogen : List Token → Nat → Nat → Nat →
    Except String (String × List Token)
  | [], _, _, _ => .error "unbalanced group"
  | (.zeichen s :: rest), pr, pk, pg =>
    if strEq s "(" then match sammleAusgewogen rest (pr + 1) pk pg with
      | .ok (h, r) => .ok ("( " ++ h, r)
      | .error e => .error e
    else if strEq s ")" then
      if pr == 0 then .error "unbalanced group"
      else if pr == 1 && pk == 0 && pg == 0 then .ok (") ", rest)
      else match sammleAusgewogen rest (pr - 1) pk pg with
        | .ok (h, r) => .ok (") " ++ h, r)
        | .error e => .error e
    else if strEq s "[" then match sammleAusgewogen rest pr (pk + 1) pg with
      | .ok (h, r) => .ok ("[ " ++ h, r)
      | .error e => .error e
    else if strEq s "]" then
      if pk == 0 then .error "unbalanced group"
      else if pr == 0 && pk == 1 && pg == 0 then .ok ("] ", rest)
      else match sammleAusgewogen rest pr (pk - 1) pg with
        | .ok (h, r) => .ok ("] " ++ h, r)
        | .error e => .error e
    else if strEq s "{" then match sammleAusgewogen rest pr pk (pg + 1) with
      | .ok (h, r) => .ok ("{ " ++ h, r)
      | .error e => .error e
    else if strEq s "}" then
      if pg == 0 then .error "unbalanced group"
      else if pr == 0 && pk == 0 && pg == 1 then .ok ("} ", rest)
      else match sammleAusgewogen rest pr pk (pg - 1) with
        | .ok (h, r) => .ok ("} " ++ h, r)
        | .error e => .error e
    else match sammleAusgewogen rest pr pk pg with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (t :: rest), pr, pk, pg => match sammleAusgewogen rest pr pk pg with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- Raw words until a clause head, a body `{`, `;`, `=` or the
    end (the `by` tail). Structural on the token list. -/
def nimmBisKopf : List Token → Except String (String × List Token)
  | [] => .ok ("", [])
  | (.wort s :: rest) =>
    if istKlauselKopf s then .ok ("", .wort s :: rest)
    else match nimmBisKopf rest with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (.zeichen s :: rest) =>
    if strEq s "{" || strEq s ";" || strEq s "=" then
      .ok ("", .zeichen s :: rest)
    else match nimmBisKopf rest with
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
      | .error e => .error e
  | (.ende :: rest) => .ok ("", .ende :: rest)
  | (t :: rest) => match nimmBisKopf rest with
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- `rights = right { "+" right }`, `right = r | w | rw | x | own [ "@" ident ]`, kept as one string
    (`rw+own`, `own@h`). -/
def parseRechte : Nat → List Token → Except String (String × List Token)
  | 0, _ => .error "out of fuel"
  | f + 1, toks => do
    let (n, r) ← nimmName toks
    let (s, r1) ← (match r with
      | .zeichen "@" :: t => do
        let (a, r') ← nimmName t
        pure (n ++ "@" ++ a, r')
      | _ => pure (n, r))
    match r1 with
    | .zeichen "+" :: r2 => do
      let (rest, r3) ← parseRechte f r2
      pure (s ++ "+" ++ rest, r3)
    | _ => pure (s, r1)

mutual
def parseTyp (f : Nat) (toks : List Token) :
    Except String (STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "ptr" then match fordereZeichen "<" rest with
        | .error e => .error e
        | .ok r1 => match nimmName r1 with
          | .error e => .error e
          | .ok (raum, r2) => match fordereZeichen "," r2 with
            | .error e => .error e
            | .ok r3 => match parseRechte f r3 with
              | .error e => .error e
              | .ok (rechte, r4) => match fordereZeichen ">" r4 with
                | .error e => .error e
                | .ok r5 => match parseTyp f r5 with
                  | .error e => .error e
                  | .ok (ziel, r) => .ok (.ptr raum rechte ziel, r)
      else if strEq s "option" then match rest with
        | .wort t :: rest' =>
          if strEq t "index" then match nimmWort "into" rest' with
            | .error e => .error e
            | .ok r => match nimmName r with
              | .error e => .error e
              | .ok (n, r') => .ok (.index true n, r')
          else .error "type expected"
        | _ => .error "type expected"
      else if strEq s "index" then match nimmWort "into" rest with
        | .error e => .error e
        | .ok r => match nimmName r with
          | .error e => .error e
          | .ok (n, r') => .ok (.index false n, r')
      else if strEq s "entry" then match rest with
        | .wort t :: .zeichen "(" :: r =>
          if strEq t "fn" then match sammleAusgewogen r 1 0 0 with
            | .error e => .error e
            | .ok (h, r') => match r' with
              | .zeichen "->" :: r'' => match parseTyp f r'' with
                | .error e => .error e
                | .ok (t', r3) => .ok (.entry h (some t'), r3)
              | _ => .ok (.entry h none, r')
          else .error "type expected"
        | _ => .error "type expected"
      else if strEq s "fn" then match fordereZeichen "(" rest with
        | .error e => .error e
        | .ok r => match sammleAusgewogen r 1 0 0 with
          | .error e => .error e
          | .ok (h, r') =>
            match nimmBisKopf r' with
            | .error e => .error e
            | .ok (t, r'') => .ok (.raw ("fn ( " ++ h ++ t), r'')
      else match nimmPfad toks with
        | .error e => .error e
        | .ok (segs, r) => match segs with
          | [] => .error "type expected"
          | [a] => parseTypNach f (.atom a) r
          | _ => parseTypNach f (.path segs) r
    | .ident "string" :: .wort "max" :: rest => match parseOr f rest with
      | .error e => .error e
      | .ok (n, r) => .ok (.str n, r)
    | .ident _ :: _ => match nimmPfad toks with
      | .error e => .error e
      | .ok (segs, r) => match segs with
        | [] => .error "type expected"
        | [a] => parseTypNach f (.atom a) r
        | _ => parseTypNach f (.path segs) r
    | .zeichen "{" :: rest => match nimmBereichWorte rest 1 with
      | .error e => .error e
      | .ok (h, r) => .ok (.raw ("{ " ++ h), r)
    | .zeichen "[" :: rest => match parseTyp f rest with
      | .error e => .error e
      | .ok (t, r1) => match fordereZeichen ";" r1 with
        | .error e => .error e
        | .ok r2 => match parseOr f r2 with
          | .error e => .error e
          | .ok (n, r3) => match fordereZeichen "]" r3 with
            | .error e => .error e
            | .ok r => .ok (.array t n, r)
    | _ => .error "type expected"
/-- The `in range` / `wrapping` / `embeds` suffixes behind a base
    type (`intty`, `slottype`, `fieldty`). -/
def parseTypNach (f : Nat) (basis : STyp) (toks : List Token) :
    Except String (STyp × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "in" then match parseOr f rest with
        | .error e => .error e
        | .ok (lo, r1) => match r1 with
          | .zeichen o :: r2 =>
            if strEq o ".." || strEq o "..<" then
              match parseOr f r2 with
              | .error e => .error e
              | .ok (hi, r) =>
                parseTypNach f (.range basis lo hi (strEq o "..<")) r
            else .error "range expected"
          | _ => .error "range expected"
      else if strEq s "wrapping" then
        parseTypNach f (.wrap basis) rest
      else if strEq s "embeds" then match fordereZeichen "[" rest with
        | .error e => .error e
        | .ok r1 => match sammleAusgewogen r1 0 1 0 with
          | .error e => .error e
          | .ok (h, r2) => match r2 with
            | .wort t :: r3 =>
              if strEq t "scale" then match parseOr f r3 with
                | .error e => .error e
                | .ok (e, r) =>
                  parseTypNach f (.embed basis h (some e)) r
              else parseTypNach f (.embed basis h none) r2
            | _ => parseTypNach f (.embed basis h none) r2
      else .ok (basis, toks)
    | _ => .ok (basis, toks)
end

end Gabbro.Grammatik.Parser
