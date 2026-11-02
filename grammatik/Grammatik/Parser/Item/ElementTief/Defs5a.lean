module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs4

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

def parseFormatRest (f : Nat) (toks : List Token) :
    Except String ((Option SExpr × Option String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "@" :: rest => match rest with
      | .ident s :: r1 =>
        if strEq s "version" then match parseOr f r1 with
          | .error e => .error e
          | .ok (v, r2) => match parseFormatRest f r2 with
            | .error e => .error e
            | .ok ((_, e), r) => .ok (((some v, e)), r)
        else .error "@version expected"
      | _ => .error "@version expected"
    | .wort s :: rest =>
      if strEq s "endian" then match rest with
        | .wort m :: r1 =>
          if strEq m "little" || strEq m "big" then
            match parseFormatRest f r1 with
            | .error e => .error e
            | .ok ((v, _), r) => .ok (((v, some m)), r)
          else .error "endian expected"
        | _ => .error "endian expected"
      else .ok (((none, none)), toks)
    | _ => .ok (((none, none)), toks)

/-- `format n [@version e] [endian m] { fields }`. -/
def parseFormatTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "format" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseFormatRest f r2 with
        | .error e => .error e
        | .ok ((ver, e), r3) => match parseFeldListe f r3 with
          | .error e => .error e
          | .ok (fds, r) => .ok (.formatT n ver e fds, r)

/-- `arena n capacity lo .. hi [max m] of T [pb path blw e] ;` (`pb`/`blw` read as names: the
    sampling clause of the unbounded heap, TODO 1-B). -/
def parseArenaTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "arena" toks
    let (n, r2) ← nimmName r1
    let r3 ← nimmWort "capacity" r2
    let (lo, r4) ← parseOr f r3
    let r5 ← fordereZeichen ".." r4
    let (hi, r6) ← parseOr f r5
    let (mx, r7) ← (match r6 with
      | .wort "max" :: rest => do
        let (e, r) ← parseOr f rest
        pure (some e, r)
      | _ => pure (none, r6))
    let r8 ← nimmWort "of" r7
    let (t, r9) ← parseTyp f r8
    let (pb, r10) ← (match r9 with
      | .zeichen ";" :: _ => pure (none, r9)
      | t1 :: rest => match nameText t1 with
        | some w =>
          if strEq w "pb" then do
            let (p, ra) ← nimmPfad rest
            let (b, rb) ← nimmName ra
            if strEq b "blw" then do
              let (e, rc) ← parseOr f rb
              pure (some (p, e), rc)
            else .error "blw expected"
          else .error "wanted ;"
        | none => .error "wanted ;"
      | [] => .error "wanted ;")
    let r ← fordereZeichen ";" r10
    pure (.arenaT n lo hi mx t pb, r)

/-- `lock n protects {…} rank e [held <= e ops] [shared held <= e ops] [masks m]
    [invariant p] ;`, the clauses in this order (`parse.rs` `lockdecl`). -/
def parseSperreTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => do
    let r1 ← nimmWort "lock" toks
    let (n, r2) ← nimmName r1
    let r3 ← nimmWort "protects" r2
    let (ps, r4) ← parsePlatzListe f r3
    let r5 ← nimmWort "rank" r4
    let (rk, r6) ← parseOr f r5
    let (h, r7) ← (match r6 with
      | .wort "held" :: rest => do
        let r ← fordereZeichen "<=" rest
        let (e, ra) ← parseOr f r
        let rb ← nimmWort "ops" ra
        pure (some e, rb)
      | _ => pure (none, r6))
    let (sh, r8) ← (match r7 with
      | .wort "shared" :: rest => do
        let r0 ← nimmWort "held" rest
        let r ← fordereZeichen "<=" r0
        let (e, ra) ← parseOr f r
        let rb ← nimmWort "ops" ra
        pure (some e, rb)
      | _ => pure (none, r7))
    let (m, r9) ← (match r8 with
      | .wort "masks" :: rest => do
        let (w, r) ← nimmName rest
        pure (some w, r)
      | _ => pure (none, r8))
    let (inv, r10) ← (match r9 with
      | .wort "invariant" :: rest => do
        let (p, r) ← parsePred f rest
        pure (some p, r)
      | _ => pure (none, r9))
    let r ← fordereZeichen ";" r10
    pure (.lockT n ps rk h sh m inv, r)

def parseAxiomErg (f : Nat) (toks : List Token) :
    Except String ((Option STyp × Option SExpr) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "->" :: rest => match parseTyp f rest with
      | .error e => .error e
      | .ok (t, r1) => match r1 with
        | .wort s :: r2 =>
          if strEq s "requires" then match parsePred f r2 with
            | .error e => .error e
            | .ok (p, r) => .ok (((some t, some p)), r)
          else .ok (((some t, none)), r1)
        | _ => .ok (((some t, none)), r1)
    | .wort s :: rest =>
      if strEq s "requires" then match parsePred f rest with
        | .error e => .error e
        | .ok (p, r) => .ok (((none, some p)), r)
      else .ok (((none, none)), toks)
    | _ => .ok (((none, none)), toks)

/-- `axiom n(params) [-> T] [requires p] effects {…} klasse ;`. -/
def parseAxiomTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "axiom" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (n, r2) => match parseParams f r2 with
        | .error e => .error e
        | .ok (ps, r3) => match parseAxiomErg f r3 with
          | .error e => .error e
          | .ok ((erg, pre), r4) => match nimmWort "effects" r4 with
            | .error e => .error e
            | .ok r5 => match parseEffektBlock f r5 with
              | .error e => .error e
              | .ok (es, r6) => match parseKlasse r6 with
                | .error e => .error e
                | .ok (k, r7) => match fordereZeichen ";" r7 with
                  | .error e => .error e
                  | .ok r => .ok (.axiomT n ps erg pre es k, r)

/-- One reason case: `name = num "text"`. -/
def parseGrundFall (f : Nat) (toks : List Token) :
    Except String ((String × SExpr × String) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (c, r1) => match fordereZeichen "=" r1 with
      | .error e => .error e
      | .ok r2 => match parseOr f r2 with
        | .error e => .error e
        | .ok (num, r3) => match nimmTextTok r3 with
          | .error e => .error e
          | .ok (t, r) => .ok (((c, num, t)), r)

def parseGrundFaelle (f : Nat) (toks : List Token) :
    Except String ((List (String × SExpr × String) × Bool) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "exhaustive" then match fordereZeichen "}" rest with
        | .error e => .error e
        | .ok r => .ok ((([], true)), r)
      else match parseGrundFall f toks with
        | .error e => .error e
        | .ok ((c, num, t), r4) => match r4 with
          | .zeichen "," :: r5 => match parseGrundFaelle f r5 with
            | .error e => .error e
            | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
          | _ => match parseGrundFaelle f r4 with
            | .error e => .error e
            | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
    | .ident _ :: _ => match parseGrundFall f toks with
      | .error e => .error e
      | .ok ((c, num, t), r4) => match r4 with
        | .zeichen "," :: r5 => match parseGrundFaelle f r5 with
          | .error e => .error e
          | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
        | _ => match parseGrundFaelle f r4 with
          | .error e => .error e
          | .ok ((cs, ex), r) => .ok ((((c, num, t) :: cs, ex)), r)
    | .zeichen "}" :: rest => .ok ((([], false)), rest)
    | _ => .error "reason expected"


end Gabbro.Grammatik.Parser
