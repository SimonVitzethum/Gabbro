module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs2

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- Register bindings after the opening `{`. -/
def parseRegBindFolge (f : Nat) (toks : List Token) :
    Except String (List SRegBind × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseRegBind toks with
    | .error e => .error e
    | .ok (b, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
            | .zeichen "}" :: r3 => .ok ([b], r3)
            | _ => match parseRegBindFolge f r2 with
              | .error e => .error e
              | .ok (bs, r') => .ok (b :: bs, r')
          | _ => match fordereZeichen "}" r1 with
            | .error e => .error e
            | .ok r' => .ok ([b], r')

/-- A `{` … `}` register map (`regs in` / `regs out`). -/
def parseRegBindListe (f : Nat) (toks : List Token) :
    Except String (List SRegBind × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseRegBindFolge f r with
        | .error e => .error e
        | .ok (bs, r') => .ok (bs, r')

/-- The arguments of a start: in parentheses, or none. -/
def startArgs (f : Nat) (r0 : List Token) : Except String (List SExpr × List Token) :=
  match r0 with
  | .zeichen "(" :: r => parseArgs f r
  | _ => .ok ([], r0)

/-- Starts after the opening `{`: a path, its arguments in parentheses if any. -/
def parsePfadFolge (f : Nat) (toks : List Token) :
    Except String (List (List String × List SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmPfad toks with
    | .error e => .error e
    | .ok (p, r0) =>
      match startArgs f r0 with
      | .error e => .error e
      | .ok (as, r1) => match r1 with
        | .zeichen "," :: r2 => match r2 with
          | .zeichen "}" :: r3 => .ok ([(p, as)], r3)
          | _ => match parsePfadFolge f r2 with
            | .error e => .error e
            | .ok (ps, r') => .ok ((p, as) :: ps, r')
        | _ => match fordereZeichen "}" r1 with
          | .error e => .error e
          | .ok r' => .ok ([(p, as)], r')

/-- A `{` … `}` path list (`concurrent`, `group over`;
    trailing commas allowed). -/
def parsePfadListe (f : Nat) (toks : List Token) :
    Except String (List (List String × List SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parsePfadFolge f r with
        | .error e => .error e
        | .ok (ps, r') => .ok (ps, r')

/-- One boot step: `step f(args) ;` or `step n = e ;`. -/
def parseBootSchritt (f : Nat) (toks : List Token) :
    Except String (SBootSchritt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "step" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (p, r2) => match r2 with
        | .zeichen "(" :: r3 => match r3 with
          | .zeichen ")" :: r4 => match fordereZeichen ";" r4 with
            | .error e => .error e
            | .ok r => .ok (.call p [], r)
          | _ => match parsePredListe f r3 with
            | .error e => .error e
            | .ok (as, r4) => match fordereZeichen ")" r4 with
              | .error e => .error e
              | .ok r5 => match fordereZeichen ";" r5 with
                | .error e => .error e
                | .ok r => .ok (.call p as, r)
        | .zeichen "=" :: r3 => match parseOr f r3 with
          | .error e => .error e
          | .ok (e, r4) => match fordereZeichen ";" r4 with
            | .error e => .error e
            | .ok r => match p with
              | [n] => .ok (.set n e, r)
              | _ => .error "step expected"
        | _ => .error "step expected"

/-- A `{` … `}` name list that may stand empty (`preserves`,
    `clobbers`, `gates`). -/
def parseNamenEingeklammert (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "{" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen "}" :: r' => .ok ([], r')
      | _ => match parseNamenListe f r with
        | .error e => .error e
        | .ok (ns, r1) => match r1 with
          | .zeichen "," :: r2 => match fordereZeichen "}" r2 with
            | .ok r' => .ok (ns, r')
            | .error _ => .error "} expected"
          | _ => match fordereZeichen "}" r1 with
            | .error e => .error e
            | .ok r' => .ok (ns, r')

/-- `syscontract`: `[requires p,…] [ensures p,…] effects {…} [costs <= e ops]`. -/
def parseGate (f : Nat) (toks : List Token) :
    Except String (SGate × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (rq, r1) ← (match toks with
      | .wort "requires" :: rest => parsePredListe f rest
      | _ => pure ([], toks))
    let (en, r2) ← (match r1 with
      | .wort "ensures" :: rest => parsePredListe f rest
      | _ => pure ([], r1))
    let r3 ← nimmWort "effects" r2
    let (ef, r4) ← parseEffektBlock f r3
    let (ko, r5) ← (match r4 with
      | .wort "costs" :: rest => do
        let r ← fordereZeichen "<=" rest
        let (e, ra) ← parseOr f r
        let rb ← nimmWort "ops" ra
        pure (some e, rb)
      | _ => pure (none, r4))
    pure ({ pre := rq, post := en, uses := ef, cost := ko }, r5)

/-- The pairs of an `errors` map behind its `{`, up to and including the `}`. -/
def parseErrsRest (f : Nat) (toks : List Token) :
    Except String (List (String × Option SExpr × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: r => .ok ([], r)
    | _ => do
      let (a, r1) ← nimmName toks
      let (num, r2) ← (match r1 with
        | .zeichen "=" :: r => do
          let (e, r') ← parseOr f r
          pure (some e, r')
        | _ => pure (none, r1))
      let r3 ← fordereZeichen "=>" r2
      let (b, r4) ← nimmName r3
      match r4 with
      | .zeichen "," :: r5 => do
        let (xs, r6) ← parseErrsRest f r5
        pure ((a, num, b) :: xs, r6)
      | _ => do
        let r5 ← fordereZeichen "}" r4
        pure ([(a, num, b)], r5)

/-- The `errors {…}` map: `errno [= n] => Ground` pairs. -/
def parseErrs (f : Nat) (toks : List Token) :
    Except String (List (String × Option SExpr × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r ← fordereZeichen "{" toks
    parseErrsRest f r

/-- `{ "stack" ident }` between `regs out` and `clobbers`. -/
def parseStackClauses (f : Nat) (toks : List Token) :
    Except String (List String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort "stack" :: rest => do
      let (n, r1) ← nimmName rest
      let (ns, r) ← parseStackClauses f r1
      pure (n :: ns, r)
    | _ => pure ([], toks)

/-- `result area REGISTER`: an explicit hidden argument, never a raw source
    pointer conversion or an implicit choice of provider ABI. -/
def parseResultArea (toks : List Token) : Except String (Option String × List Token) :=
  match toks with
  | .wort "result" :: .ident "area" :: rest => do
    let (register, rest) ← nimmName rest
    pure (some register, rest)
  | .wort "result" :: rest => do
    let rest ← nimmWort "area" rest
    let (register, rest) ← nimmName rest
    pure (some register, rest)
  | _ => pure (none, toks)

/-- `sysbind` (SYNTAX.md 12.1): `number e regs in {…} regs out {…} {stack r} clobbers {…} errors {…}`. -/
def parseBind (f : Nat) (toks : List Token) :
    Except String (SBind × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "number" toks
    let (num, r2) ← parseOr f r1
    let r3 ← nimmWort "regs" r2
    let r4 ← nimmWort "in" r3
    let (ri, r5) ← parseRegBindListe f r4
    let r6 ← nimmWort "regs" r5
    let r7 ← nimmWort "out" r6
    let (ro, r8) ← parseRegBindListe f r7
    let (area, r8) ← parseResultArea r8
    let (sk, r9) ← parseStackClauses f r8
    let r10 ← nimmWort "clobbers" r9
    let (cb, r11) ← parseNamenEingeklammert f r10
    let r12 ← nimmWort "errors" r11
    let (em, r) ← parseErrs f r12
    pure ({ id := num, ins := ri, outs := ro, stack := sk, dirty := cb, codes := em, resultArea := area }, r)


end Gabbro.Grammatik.Parser
