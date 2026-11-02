module

public import Grammatik.Parser.Item.ElementTief.Defs5a
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs4

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- `reason n { c = num "text" … [exhaustive] }` (cases are
    whitespace-separated, commas allowed). -/
def parseGrundTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "reason" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseGrundFaelle f r3 with
          | .error e => .error e
          | .ok ((cs, ex), r) => .ok (.whyT n cs ex, r)

/-- `use path ;`. -/
def parseUseTief : List Token → Except String (SItemTief × List Token)
  | toks => match nimmWort "use" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (p, r2) => match fordereZeichen ";" r2 with
        | .error e => .error e
        | .ok r => .ok (.useT p, r)

/-- `concurrent { paths } ;`. -/
def parseNebenTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "concurrent" toks with
    | .error e => .error e
    | .ok r1 => match parsePfadListe f r1 with
      | .error e => .error e
      | .ok (ps, r2) => match fordereZeichen ";" r2 with
        | .error e => .error e
        | .ok r => .ok (.concT ps, r)

/-- The bindings `V = sysbind syspair` of a target body, up to and including its `}`. -/
def parseGoalBinds (f : Nat) (toks : List Token) :
    Except String (List (String × SBind × SHerkunft) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: r => .ok ([], r)
    | _ => do
      let (v, r1) ← nimmName toks
      let r2 ← fordereZeichen "=" r1
      let (bd, r3) ← parseBind f r2
      let (hk, r4) ← parsePair r3
      let (bs, r) ← parseGoalBinds f r4
      pure ((v, bd, hk) :: bs, r)

/-- `target T ;` (the selection) or `target T abi A arch X { V = <sysbind> <pair> … }` (SYNTAX.md 12.3). -/
def parseGoal (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "target" toks
    let (n, r2) ← nimmName r1
    match r2 with
    | .zeichen ";" :: r => pure (.goalT n none, r)
    | _ => do
      let r3 ← nimmWort "abi" r2
      let (abi, r4) ← nimmName r3
      let r5 ← nimmWort "arch" r4
      let (arch, r6) ← nimmName r5
      let r7 ← fordereZeichen "{" r6
      let (bs, r) ← parseGoalBinds f r7
      pure (.goalT n (some (abi, arch, bs)), r)

/-- `assume n [arch a] "text" (falsifier | unfalsifiable) ;`. -/
def parseAnnahmeTief : List Token → Except String (SItemTief × List Token)
  | toks => match nimmWort "assume" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match r2 with
        | .wort s :: r3 =>
          if strEq s "arch" then match nimmName r3 with
            | .error e => .error e
            | .ok (a, r4) => match nimmTextTok r4 with
              | .error e => .error e
              | .ok (t, r5) => match parseKlasse r5 with
                | .error e => .error e
                | .ok (k, r6) => match fordereZeichen ";" r6 with
                  | .error e => .error e
                  | .ok r => .ok (.assumT n (some a) t k, r)
          else match nimmTextTok r2 with
            | .error e => .error e
            | .ok (t, r3) => match parseKlasse r3 with
              | .error e => .error e
              | .ok (k, r4) => match fordereZeichen ";" r4 with
                | .error e => .error e
                | .ok r => .ok (.assumT n none t k, r)
        | _ => match nimmTextTok r2 with
          | .error e => .error e
          | .ok (t, r3) => match parseKlasse r3 with
            | .error e => .error e
            | .ok (k, r4) => match fordereZeichen ";" r4 with
              | .error e => .error e
              | .ok r => .ok (.assumT n none t k, r)

def parsePruefungRest (f : Nat) (toks : List Token) :
    Except String ((List SExpr × Option (String × String)) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "floor" then match parsePredListe f rest with
        | .error e => .error e
        | .ok (ps, r1) => match parsePruefungRest f r1 with
          | .error e => .error e
          | .ok (((qs, so)), r) => .ok (((ps ++ qs, so)), r)
      else if strEq s "counterprobe" then match nimmTextTok rest with
        | .error e => .error e
        | .ok (t, r1) => match nimmWort "expects" r1 with
          | .error e => .error e
          | .ok r2 => match nimmName r2 with
            | .error e => .error e
            | .ok (e, r3) => match fordereZeichen "}" r3 with
              | .error e => .error e
              | .ok r => .ok ((([], some (t, e))), r)
      else match fordereZeichen "}" toks with
        | .error e => .error e
        | .ok r => .ok ((([], none)), r)
    | _ => match fordereZeichen "}" toks with
      | .error e => .error e
      | .ok r => .ok ((([], none)), r)

/-- `check n { claim … measures … gates … can_fail … [floor …]
    [counterprobe …] }`. -/
def parsePruefungTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "check" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match nimmWort "claim" r3 with
          | .error e => .error e
          | .ok r4 => match nimmTextTok r4 with
            | .error e => .error e
            | .ok (c, r5) => match nimmWort "measures" r5 with
              | .error e => .error e
              | .ok r6 => match parsePredListe f r6 with
                | .error e => .error e
                | .ok (ms, r7) => match nimmWort "gates" r7 with
                  | .error e => .error e
                  | .ok r8 => match parseNamenListe f r8 with
                    | .error e => .error e
                    | .ok (gs, r9) => match nimmWort "can_fail" r9 with
                      | .error e => .error e
                      | .ok r10 => match parseBlock f r10 with
                        | .error e => .error e
                        | .ok (b, r11) => match parsePruefungRest f r11 with
                          | .error e => .error e
                          | .ok (((boden, sonde)), r) => .ok (.checkT
                            ({ cname := n, claim := c, misst := ms,
                               gates := gs, canFail := b, boden,
                               sonde } : SCheck), r)

def parseAtomarRest (f : Nat)
    (acc : String × STyp × Option (List SExpr) × Option String × Option String)
    (toks : List Token) :
    Except String
      ((String × STyp × Option (List SExpr) × Option String × Option String) ×
       List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "publishes" then match rest with
        | .wort t :: r1 =>
          if strEq t "nothing" then
            match acc with
            | (a, b, _, d, e) =>
              parseAtomarRest f (a, b, some [], d, e) r1
          else match parsePlatzListe f rest with
            | .error e => .error e
            | .ok (ps, r) => match acc with
              | (a, b, _, d, e) =>
                parseAtomarRest f (a, b, some ps, d, e) r
        | _ => match parsePlatzListe f rest with
          | .error e => .error e
          | .ok (ps, r) => match acc with
            | (a, b, _, d, e) =>
              parseAtomarRest f (a, b, some ps, d, e) r
      else if strEq s "acquire" || strEq s "release" ||
          strEq s "seq" || strEq s "relaxed" then match acc with
        | (a, b, c, _, e) =>
          parseAtomarRest f (a, b, c, some s, e) rest
      else if strEq s "observed" then match nimmWort "by" rest with
        | .error e => .error e
        | .ok r1 => match nimmName r1 with
          | .error e => .error e
          | .ok (o, r2) => match acc with
            | (a, b, c, d, _) =>
              parseAtomarRest f (a, b, c, d, some o) r2
      else match fordereZeichen ";" toks with
        | .error e => .error e
        | .ok r => .ok (acc, r)
    | _ => match fordereZeichen ";" toks with
      | .error e => .error e
      | .ok r => .ok (acc, r)
