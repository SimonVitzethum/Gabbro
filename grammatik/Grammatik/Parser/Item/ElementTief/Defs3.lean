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
    let (sk, r9) ← parseStackClauses f r8
    let r10 ← nimmWort "clobbers" r9
    let (cb, r11) ← parseNamenEingeklammert f r10
    let r12 ← nimmWort "errors" r11
    let (em, r) ← parseErrs f r12
    pure ({ id := num, ins := ri, outs := ro, stack := sk, dirty := cb, codes := em }, r)

/-- `syspair`: `assume a (falsifier s | unfalsifiable "…") ;` or `kernel path ;`. -/
def parsePair (toks : List Token) :
    Except String (SHerkunft × List Token) :=
  match toks with
  | .wort "assume" :: rest => do
    let (a, r1) ← nimmName rest
    let (k, r2) ← parseKlasse r1
    let r ← fordereZeichen ";" r2
    pure (.assum a k, r)
  | .wort "kernel" :: rest => do
    let (p, r1) ← nimmPfad rest
    let r ← fordereZeichen ";" r1
    pure (.core p, r)
  | _ => .error "syscall expected"

/-- `syscall V ;` (a variable) or a gate: `syscall g(params) [-> T] [or R]` then either the literal
    binding `abi A arch X <sysbind> <contract> <pair>` or `via V <contract> ;` (SYNTAX.md 12.1, 12.3). -/
def parseSysrufTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "syscall" toks
    let (n, r2) ← nimmName r1
    match r2 with
    | .zeichen ";" :: r => pure (.varT n, r)
    | _ => do
      let (ps, r3) ← parseParams f r2
      let (erg, fehler, r4) ← parseErgebnis f r3
      match r4 with
      | .wort "via" :: r5 => do
        let (v, r6) ← nimmName r5
        let (cv, r7) ← parseGate f r6
        let r ← fordereZeichen ";" r7
        pure (.callT { name := n, params := ps, res := erg, fail := fehler,
                         way := .via v, gate := cv }, r)
      | _ => do
        let r5 ← nimmWort "abi" r4
        let (abi, r6) ← nimmName r5
        let r7 ← nimmWort "arch" r6
        let (arch, r8) ← nimmName r7
        let (bd, r9) ← parseBind f r8
        let (cv, r10) ← parseGate f r9
        let (hk, r) ← parsePair r10
        pure (.callT { name := n, params := ps, res := erg, fail := fehler,
                         way := .lit abi arch bd hk, gate := cv }, r)

def parseGruppenInvListe (f : Nat) (toks : List Token) :
    Except String (List SGruppenInv × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: _ =>
      if strEq s "invariant" then match parseGruppenInv f toks with
        | .error e => .error e
        | .ok (iv, r1) => match parseGruppenInvListe f r1 with
          | .error e => .error e
          | .ok (ivs, r) => .ok (iv :: ivs, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)

/-- `walk n levels e { node : T, down : f when p, leaf : q,
    invariants }`. -/
def parseWegTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "walk" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "levels" r2 with
        | .error e => .error e
        | .ok r3 => match parseOr f r3 with
          | .error e => .error e
          | .ok (lv, r4) => match fordereZeichen "{" r4 with
            | .error e => .error e
            | .ok r5 => match nimmWort "node" r5 with
              | .error e => .error e
              | .ok r6 => match fordereZeichen ":" r6 with
                | .error e => .error e
                | .ok r7 => match parseTyp f r7 with
                  | .error e => .error e
                  | .ok (kn, r8) => match fordereZeichen "," r8 with
                    | .error e => .error e
                    | .ok r9 => match nimmWort "down" r9 with
                      | .error e => .error e
                      | .ok r10 => match fordereZeichen ":" r10 with
                        | .error e => .error e
                        | .ok r11 => match nimmName r11 with
                          | .error e => .error e
                          | .ok (dn, r12) => match nimmWort "when" r12 with
                            | .error e => .error e
                            | .ok r13 => match parsePred f r13 with
                              | .error e => .error e
                              | .ok (dp, r14) =>
                                match fordereZeichen "," r14 with
                                | .error e => .error e
                                | .ok r15 => match nimmWort "leaf" r15 with
                                  | .error e => .error e
                                  | .ok r16 => match fordereZeichen ":" r16 with
                                    | .error e => .error e
                                    | .ok r17 => match parsePred f r17 with
                                      | .error e => .error e
                                      | .ok (lf, r18) => match r18 with
                                        | .zeichen "," :: r19 =>
                                          match parseGruppenInvListe f r19 with
                                          | .error e => .error e
                                          | .ok (ivs, r20) =>
                                            match fordereZeichen "}" r20 with
                                            | .error e => .error e
                                            | .ok r => .ok (.walkT
                                              ({ name := n, stufen := lv,
                                                 node := kn,
                                                 dname := dn,
                                                 dwhen := dp, blatt := lf,
                                                 invarianten := ivs } : SWeg), r)
                                        | _ =>
                                          match fordereZeichen "}" r18 with
                                          | .error e => .error e
                                          | .ok r => .ok (.walkT
                                            ({ name := n, stufen := lv,
                                               node := kn,
                                               dname := dn,
                                               dwhen := dp, blatt := lf,
                                               invarianten := [] } : SWeg), r)

/-- `rcu n protects {…} [reclaims p] ;`. -/
def parseRcuTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "rcu" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "protects" r2 with
        | .error e => .error e
        | .ok r3 => match parsePlatzListe f r3 with
          | .error e => .error e
          | .ok (ps, r4) => match r4 with
            | .wort s :: r5 =>
              if strEq s "reclaims" then match parseOr f r5 with
                | .error e => .error e
                | .ok (p, r6) => match fordereZeichen ";" r6 with
                  | .error e => .error e
                  | .ok r => .ok (.rcuT n ps (some p), r)
              else match fordereZeichen ";" r4 with
                | .error e => .error e
                | .ok r => .ok (.rcuT n ps none, r)
            | _ => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.rcuT n ps none, r)

/-- `entrust n at m arch a { regs in {…} stack s assume g ; }`. -/
def parseAnvertrautTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "entrust" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "at" r2 with
        | .error e => .error e
        | .ok r3 => match nimmName r3 with
          | .error e => .error e
          | .ok (m, r4) => match nimmWort "arch" r4 with
            | .error e => .error e
            | .ok r5 => match nimmName r5 with
              | .error e => .error e
              | .ok (a, r6) => match fordereZeichen "{" r6 with
                | .error e => .error e
                | .ok r7 => match nimmWort "regs" r7 with
                  | .error e => .error e
                  | .ok r8 => match nimmWort "in" r8 with
                    | .error e => .error e
                    | .ok r9 => match parseRegBindListe f r9 with
                      | .error e => .error e
                      | .ok (ri, r10) => match nimmWort "stack" r10 with
                        | .error e => .error e
                        | .ok r11 => match nimmName r11 with
                          | .error e => .error e
                          | .ok (st, r12) =>
                            match nimmWort "assume" r12 with
                            | .error e => .error e
                            | .ok r13 => match nimmName r13 with
                              | .error e => .error e
                              | .ok (g, r14) =>
                                match fordereZeichen ";" r14 with
                                | .error e => .error e
                                | .ok r15 =>
                                  match fordereZeichen "}" r15 with
                                  | .error e => .error e
                                  | .ok r => .ok
                                    (.trustT n m a ri st g, r)

def parseBootSchritte (f : Nat) (toks : List Token) :
    Except String (List SBootSchritt × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: _ =>
      if strEq s "step" then match parseBootSchritt f toks with
        | .error e => .error e
        | .ok (st, r1) => match parseBootSchritte f r1 with
          | .error e => .error e
          | .ok (ss, r) => .ok (st :: ss, r)
      else .ok ([], toks)
    | _ => .ok ([], toks)
