module

public import Grammatik.Parser.Item.ElementTief.Defs3a
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs2

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

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

/-- `entrust n at Code arch a via service;`; legacy state is retained for named refusal. -/
def parseAnvertrautTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) := do
  let r ← nimmWort "entrust" toks
  let (name, r) ← nimmName r
  let r ← nimmWort "at" r
  let (code, r) ← nimmName r
  let r ← nimmWort "arch" r
  let (arch, r) ← nimmName r
  let (service, r) ← match r with
    | .wort "via" :: r => do
      let (service, r) ← nimmName r
      pure (some service, r)
    | _ => pure (none, r)
  match r with
  | .zeichen ";" :: r => pure (.trustT name code arch [] "" "" service, r)
  | _ =>
    let r ← fordereZeichen "{" r
    let r ← nimmWort "regs" r
    let r ← nimmWort "in" r
    let (registers, r) ← parseRegBindListe f r
    let r ← nimmWort "stack" r
    let (stack, r) ← nimmName r
    let r ← nimmWort "assume" r
    let (assumption, r) ← nimmName r
    let r ← fordereZeichen ";" r
    let r ← fordereZeichen "}" r
    pure (.trustT name code arch registers stack assumption service, r)


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
