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

/-- `translator n for g(params) [-> T] clauses block`. -/
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
        | .ok r3 => match nimmName r3 with
          | .error e => .error e
          | .ok (g, r4) => match parseParams f r4 with
            | .error e => .error e
            | .ok (ps, r5) => match parseErgebnis f r5 with
              | .error e => .error e
              | .ok (erg, fehler, r6) => match parseKlauseln f r6 with
                | .error e => .error e
                | .ok (ks, r7) => match parseBlock f r7 with
                  | .error e => .error e
                  | .ok (b, r) => .ok (.transT g
                    ({ art := "", name := n, params := ps,
                       res := erg, fehler, klauseln := ks } : FnSig) b, r)

def parseAkkumRest (f : Nat) (toks : List Token) :
    Except String (Option SExpr × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "per" then match nimmWort "cpu" rest with
        | .error e => .error e
        | .ok r1 => match parseOr f r1 with
          | .error e => .error e
          | .ok (e, r2) => match fordereZeichen ";" r2 with
            | .error e => .error e
            | .ok r => .ok (some e, r)
      else match fordereZeichen ";" toks with
        | .error e => .error e
        | .ok r => .ok (none, r)
    | _ => match fordereZeichen ";" toks with
      | .error e => .error e
      | .ok r => .ok (none, r)

/-- `accumulates n : T merge op [per cpu e] ;`. -/
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
                  | .ok (p, r) => .ok (.accT n t m p, r)
                else .error "merge expected"
              | _ => .error "merge expected"

/-- The `art` of a function: the last modifier, `""` for plain. -/
def letzteArt : List String → String
  | [] => ""
  | [a] => a
  | _ :: rest => letzteArt rest

def parseGruppeRest (f : Nat) (toks : List Token) :
    Except String (List SGruppenInv × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "{" :: rest => match parseGruppenInvListe f rest with
      | .error e => .error e
      | .ok (ivs, r1) => match fordereZeichen "}" r1 with
        | .error e => .error e
        | .ok r => .ok (ivs, r)
    | .zeichen ";" :: rest => .ok ([], rest)
    | _ => .error "group expected"

/-- `group n over {…} ({ invariants } | ;)`. -/
def parseGruppeTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "group" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match nimmWort "over" r2 with
        | .error e => .error e
        | .ok r3 => match fordereZeichen "{" r3 with
          | .error e => .error e
          | .ok r4 => match parseNamenListe f r4 with
            | .error e => .error e
            | .ok (ms, r5) => match r5 with
              | .zeichen "," :: r6 => match fordereZeichen "}" r6 with
                | .error e => .error e
                | .ok r7 => match parseGruppeRest f r7 with
                  | .error e => .error e
                  | .ok (ivs, r) => .ok (.groupT n ms ivs, r)
              | _ => match fordereZeichen "}" r5 with
                | .error e => .error e
                | .ok r6 => match parseGruppeRest f r6 with
                  | .error e => .error e
                  | .ok (ivs, r) => .ok (.groupT n ms ivs, r)

/-- The optional `nested …` tail (the `bounded e` measure rides
    printed, as in the `frist`/`quits` clauses). -/
def parseEingangNestedOpt (f : Nat)
    (toks : List Token) :
    Except String (Option String × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "nested" then match rest with
        | .wort m :: r1 =>
          if strEq m "never" || strEq m "masked" then
            .ok (some m, r1)
          else if strEq m "bounded" then match parseOr f r1 with
            | .error e => .error e
            | .ok (e, r2) => .ok (some ("bounded " ++ druck e), r2)
          else .error "nested expected"
        | _ => .error "nested expected"
      else .ok (none, toks)
    | _ => .ok (none, toks)

def parseEingangDispatch (f : Nat)
    (toks : List Token) :
    Except String ((List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | _f + 1 => match nimmWort "dispatch" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (dp, r2) => match fordereZeichen ";" r2 with
        | .error e => .error e
        | .ok r => .ok (dp, r)

def parseEingangNested (f : Nat)
    (toks : List Token) :
    Except String ((Option String × List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseEingangNestedOpt f toks with
    | .error e => .error e
    | .ok (ve, r1) => match parseEingangDispatch f r1 with
      | .error e => .error e
      | .ok (dp, r) => .ok (((ve, dp)), r)

def parseEingangRestNach (f : Nat)
    (toks : List Token) :
    Except String
      ((Option SExpr × Option String × List String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "ist" then match parseOr f rest with
        | .error e => .error e
        | .ok (e, r1) => match parseEingangNested f r1 with
          | .error e => .error e
          | .ok (((ve, dp)), r) => .ok ((((some e, ve, dp))), r)
      else match parseEingangNested f toks with
        | .error e => .error e
        | .ok (((ve, dp)), r) => .ok ((((none, ve, dp))), r)
    | _ => match parseEingangNested f toks with
      | .error e => .error e
      | .ok (((ve, dp)), r) => .ok ((((none, ve, dp))), r)

def parseEingangRest (f : Nat) (toks : List Token) :
    Except String
      ((String × Bool × Option SExpr × Option String × List String) ×
       List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "stack" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (st, r2) => match r2 with
        | .wort s :: r3 =>
          if strEq s "per" then match nimmWort "cpu" r3 with
            | .error e => .error e
            | .ok r4 => match parseEingangRestNach f r4 with
              | .error e => .error e
              | .ok (((ist, ve, dp)), r) =>
                .ok ((((st, true, ist, ve, dp))), r)
          else match parseEingangRestNach f r2 with
            | .error e => .error e
            | .ok (((ist, ve, dp)), r) =>
              .ok ((((st, false, ist, ve, dp))), r)
        | _ => match parseEingangRestNach f r2 with
          | .error e => .error e
          | .ok (((ist, ve, dp)), r) =>
            .ok ((((st, false, ist, ve, dp))), r)

def parseEingangKopf (f : Nat) (toks : List Token) :
    Except String
      ((Option SExpr × Option String × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "vector" then match parseOr f rest with
        | .error e => .error e
        | .ok (v, r1) => match parseEingangKopf f r1 with
          | .error e => .error e
          | .ok (((_, via, arch)), r) => .ok ((((some v, via, arch))), r)
      else if strEq s "via" then match nimmName rest with
        | .error e => .error e
        | .ok (m, r1) => match parseEingangKopf f r1 with
          | .error e => .error e
          | .ok (((vek, _, arch)), r) => .ok ((((vek, some m, arch))), r)
      else if strEq s "arch" then match nimmName rest with
        | .error e => .error e
        | .ok (a, r) => .ok ((((none, none, a))), r)
      else .error "arch expected"
    | _ => .error "arch expected"

/-- `entry n [vector e] [via m] arch a { regs … dispatch … }`. -/
def parseEingangTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "entry" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseEingangKopf f r2 with
        | .error e => .error e
        | .ok (((vek, via, arch)), r3) =>
          match fordereZeichen "{" r3 with
          | .error e => .error e
          | .ok r4 => match nimmWort "regs" r4 with
            | .error e => .error e
            | .ok r5 => match nimmWort "in" r5 with
              | .error e => .error e
              | .ok r6 => match parseRegBindListe f r6 with
                | .error e => .error e
                | .ok (ri, r7) => match nimmWort "regs" r7 with
                  | .error e => .error e
                  | .ok r8 => match nimmWort "out" r8 with
                    | .error e => .error e
                    | .ok r9 => match parseRegBindListe f r9 with
                      | .error e => .error e
                      | .ok (ro, r10) =>
                        match nimmWort "preserves" r10 with
                        | .error e => .error e
                        | .ok r11 =>
                          match parseNamenEingeklammert f r11 with
                          | .error e => .error e
                          | .ok (ph, r12) =>
                            match nimmWort "clobbers" r12 with
                            | .error e => .error e
                            | .ok r13 =>
                              match parseNamenEingeklammert f r13 with
                              | .error e => .error e
                              | .ok (cb, r14) =>
                                match parseEingangRest f r14 with
                                | .error e => .error e
                                | .ok (((st, cpu, ist, ve, dp)), r15) =>
                                  match fordereZeichen "}" r15 with
                                  | .error e => .error e
                                  | .ok r => .ok (.entryT
                                    ({ name := n, vektor := vek, via,
                                       arch, regIn := ri, regOut := ro,
                                       erhaelt := ph, kills := cb,
                                       stapel := st, perCpu := cpu, ist,
                                       nest := ve,
                                       dispatch := dp } : SEingang), r)

/-- The leading `fn`/`type` modifiers (`parse.rs` `item`); `const`
    is NOT among them (`const fn` splits on the next word). -/
def sammleModifikatoren : List Token → List String × List Token
  | .wort s :: rest =>
    if istMod s then
      let (ms, r) := sammleModifikatoren rest
      (s :: ms, r)
    else ([], .wort s :: rest)
  | toks => ([], toks)
