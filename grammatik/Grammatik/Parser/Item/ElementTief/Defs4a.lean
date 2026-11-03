module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs3

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- `boot n arch a { steps dispatch p ; }`. -/
def parseStartTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "boot" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "arch" r2 with
        | .error e => .error e
        | .ok r3 => match nimmName r3 with
          | .error e => .error e
          | .ok (a, r4) => match fordereZeichen "{" r4 with
            | .error e => .error e
            | .ok r5 => match parseBootSchritte f r5 with
              | .error e => .error e
              | .ok (ss, r6) => match nimmWort "dispatch" r6 with
                | .error e => .error e
                | .ok r7 => match nimmPfad r7 with
                  | .error e => .error e
                  | .ok (dp, r8) => match fordereZeichen ";" r8 with
                    | .error e => .error e
                    | .ok r9 => match fordereZeichen "}" r9 with
                      | .error e => .error e
                      | .ok r => .ok (.bootT n a ss dp, r)

mutual
/-- A `constwert`: an expression or an array literal, whose rows may nest (lanes 111, 170). -/
def parseKonstWert (f : Nat) (toks : List Token) :
    Except String (SKonstWert × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "[" :: rest => do
      let (xs, r) ← parseConstRows f rest
      pure (.rows xs, r)
    | _ => do
      let (e, r) ← parseOr f toks
      pure (.one e, r)

/-- The elements of an array literal behind its `[`, up to and including the `]`
    (a trailing comma is allowed). -/
def parseConstRows (f : Nat) (toks : List Token) :
    Except String (List SKonstWert × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "]" :: r => .ok ([], r)
    | _ => do
      let (v, r1) ← parseKonstWert f toks
      match r1 with
      | .zeichen "," :: r2 => do
        let (vs, r3) ← parseConstRows f r2
        pure (v :: vs, r3)
      | .zeichen "]" :: r => pure ([v], r)
      | _ => .error "wanted ]"

end

/-- Behind the initialiser: `[aligned e] [section "s"] [shared] ;`, in this order. -/
def parseGlobTail (f : Nat) (toks : List Token) :
    Except String ((Option SExpr × Option String × Bool) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (al, r1) ← (match toks with
      | .wort "aligned" :: rest => do
        let (e, r) ← parseOr f rest
        pure (some e, r)
      | _ => pure (none, toks))
    let (sec, r2) ← (match r1 with
      | .wort "section" :: rest => do
        let (t, r) ← nimmTextTok rest
        pure (some t, r)
      | _ => pure (none, r1))
    let (sh, r3) : Bool × List Token := match r2 with
      | .wort "shared" :: rest => (true, rest)
      | _ => (false, r2)
    let r ← fordereZeichen ";" r3
    pure ((al, sec, sh), r)

def parseGlobAfter (f : Nat) (ver : Bool) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (n, r1) ← nimmName toks
    let r2 ← fordereZeichen ":" r1
    let (t, r3) ← parseTyp f r2
    let r4 ← fordereZeichen "=" r3
    let (v, r5) ← parseKonstWert f r4
    let ((al, sec, sh), r) ← parseGlobTail f r5
    pure (.globT ver n t v al sec sh, r)

/-- `static [mut] n : T = e [section s] [shared] ;`. -/
def parseGlobTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "static" toks with
    | .error e => .error e
    | .ok r1 => match r1 with
      | .wort s :: r2 =>
        if strEq s "mut" then match parseGlobAfter f true r2 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)
        else match parseGlobAfter f false r1 with
          | .error e => .error e
          | .ok (it, r) => .ok (it, r)
      | _ => match parseGlobAfter f false r1 with
        | .error e => .error e
        | .ok (it, r) => .ok (it, r)

/-- `translator n for g(params) [-> T] clauses block`: the target `g` is a `::` path, kept as
    joined text like every other resolved call name; resolution turns it into its item key. -/
def parseTranslatorTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "translator" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "for" r2 with
        | .error e => .error e
        | .ok r3 => match nimmPfad r3 with
          | .error e => .error e
          | .ok (g, r4) => match parseParams f r4 with
            | .error e => .error e
            | .ok (ps, r5) => match parseErgebnis f r5 with
              | .error e => .error e
              | .ok (erg, fehler, r6) => match parseKlauseln f r6 with
                | .error e => .error e
                | .ok (ks, r7) => match parseBlock f r7 with
                  | .error e => .error e
                  | .ok (b, r) => .ok (.transT ("::".intercalate g)
                    ({ art := "", name := n, params := ps,
                       res := erg, fehler, klauseln := ks } : FnSig) b, r)

/-- Behind the merge operator: `[per cpu e] [assume n] ;`. -/
def parseAkkumRest (f : Nat) (toks : List Token) :
    Except String (Option SExpr × Option String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let (c, r1) ← (match toks with
      | .wort s :: rest =>
        if strEq s "per" then match nimmWort "cpu" rest with
          | .error e => .error e
          | .ok r1 => match parseOr f r1 with
            | .error e => .error e
            | .ok (e, r2) => .ok (some e, r2)
        else .ok (none, toks)
      | _ => .ok (none, toks))
    let (q, r2) ← (match r1 with
      | .wort s :: rest =>
        if strEq s "assume" then match nimmName rest with
          | .error e => .error e
          | .ok (n, r) => .ok (some n, r)
        else .ok (none, r1)
      | _ => .ok (none, r1))
    let r ← fordereZeichen ";" r2
    pure (c, q, r)

/-- `accumulates n : T merge op [per cpu e] [assume q] ;`. -/
def parseAkkumTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "accumulates" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen ":" r2 with
        | .error e => .error e
        | .ok r3 => match parseTyp f r3 with
          | .error e => .error e
          | .ok (t, r4) => match nimmWort "merge" r4 with
            | .error e => .error e
            | .ok r5 => match r5 with
              | .wort m :: r6 =>
                if strEq m "max" || strEq m "min" || strEq m "add" ||
                    strEq m "or" || strEq m "and" then
                  match parseAkkumRest f r6 with
                  | .error e => .error e
                  | .ok (p, q, r) => .ok (.accT n t m p q, r)
                else .error "merge expected"
              | _ => .error "merge expected"


end Gabbro.Grammatik.Parser
