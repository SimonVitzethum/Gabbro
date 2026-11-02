module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs6

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

mutual
/-- `module path { items }`. -/
def parseModulTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "module" toks with
    | .error e => .error e
    | .ok r1 => match nimmPfad r1 with
      | .error e => .error e
      | .ok (p, r2) => match fordereZeichen "{" r2 with
        | .error e => .error e
        | .ok r3 => match parseItemsTief f r3 with
          | .error e => .error e
          | .ok (its, r4) => match fordereZeichen "}" r4 with
            | .error e => .error e
            | .ok r => .ok (.modT ("::".intercalate p) its, r)

/-- The item levels of SYNTAX.md section 1 (`item`) in depth:
    every body rides structured. Against `parse.rs` `item`: the
    `when TESTBUILD` gate, the `pub` prefix, the `const fn`
    split and the head-word dispatch match one by one; the
    `fn`/`type` modifiers ride `art`/`flags` (see CUTS). -/
def parseItemsTief (f : Nat) (toks : List Token) :
    Except String (List SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: _ => .ok ([], toks)
    | .ende :: _ => .ok ([], toks)
    | [] => .ok ([], [])
    | _ => match parseItemTief f toks with
      | .error e => .error e
      | .ok (it, rest) => match parseItemsTief f rest with
        | .error e => .error e
        | .ok (its, r) => .ok (it :: its, r)

def parseItemTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "when" then match rest with
        | t :: rest' => match nameText t with
          | some u =>
            if strEq u "TESTBUILD" then match parseItemTief f rest' with
              | .ok (it, r) => .ok (.gateT it, r)
              | .error e => .error e
            else .error "when without TESTBUILD"
          | none => .error "when without TESTBUILD"
        | _ => .error "when without TESTBUILD"
      else if strEq s "pub" then match parseItemTief f rest with
        | .ok (it, r) => .ok (.pubT it, r)
        | .error e => .error e
      else parseItemKopfTief f toks
    | _ => parseItemKopfTief f toks

def parseItemKopfTief (f : Nat) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match sammleModifikatoren toks with
    | (mods, nach) => match nach with
      | .wort s :: rest =>
        if strEq s "module" then parseModulTief f nach
        else if strEq s "use" then parseUseTief nach
        else if strEq s "fn" then
          if istAdaptKopf nach then match parseAdapt f (letzteArt mods) nach with
            | .error e => .error e
            | .ok (it, r) => .ok (it, r)
          else match parseFnSig f (letzteArt mods) nach with
          | .error e => .error e
          | .ok (sig, r) => parseFnRest f sig r        else if strEq s "translator" then parseTranslatorTief f nach
        else if strEq s "profile" then parseProfilTief f false rest
        else if strEq s "requires" then match rest with
          | .wort t :: rest' =>
            if strEq t "profile" then parseProfilTief f true rest'
            else .error "requires without profile"
          | _ => .error "requires without profile"
        else if strEq s "concurrent" then parseNebenTief f nach
        else if strEq s "type" then parseTypTief f mods nach
        else if strEq s "const" then match rest with
          | .wort t :: _ =>
            if strEq t "fn" then match parseFnSig f "const" rest with
              | .error e => .error e
              | .ok (sig, r) => parseFnRest f sig r
            else match nimmWort "const" nach with
              | .error e => .error e
              | .ok r1 => parseKonstNach f r1
          | _ => match nimmWort "const" nach with
            | .error e => .error e
            | .ok r1 => parseKonstNach f r1
        else if strEq s "static" then parseGlobTief f nach
        else if strEq s "format" then parseFormatTief f nach
        else if strEq s "table" then parseTabellenTief f nach
        else if strEq s "arena" then parseArenaTief f nach
        else if strEq s "reason" then parseGrundTief f nach
        else if strEq s "state" then parseZustandTief f nach
        else if strEq s "device" then parseGeraetTief f nach
        else if strEq s "assume" then parseAnnahmeTief nach
        else if strEq s "axiom" then parseAxiomTief f nach
        else if strEq s "check" then parsePruefungTief f nach
        else if strEq s "atomic" then parseAtomarTief f nach
        else if strEq s "lock" then parseSperreTief f nach
        else if strEq s "rcu" then parseRcuTief f nach
        else if strEq s "group" then parseGruppeTief f nach
        else if strEq s "accumulates" then parseAkkumTief f nach
        else if strEq s "walk" then parseWegTief f nach
        else if strEq s "entry" then parseEingangTief f nach
        else if strEq s "entrust" then parseAnvertrautTief f nach
        else if strEq s "boot" then parseStartTief f nach
        else if strEq s "syscall" then parseSysrufTief f nach
        else if strEq s "target" then parseGoal f nach
        else .error "item expected"
      | _ => .error "item expected"

end

/-- A whole program in depth: the token list must end here. -/
def parseTopTief (toks : List Token) : Except String (List SItemTief) :=
  match parseItemsTief (toks.length * 8 + 32) toks with
  | .ok (its, [.ende]) => .ok its
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e

/-! ### Adapters `fn … from f` (`ABSTRACTION-SYNTAX-PLAN.md` §4.1) -/

/-- Whether the tokens at depth 0 hold an adapter parameter: `..` before `,`/`)` or `-name`
    before `,`/`)`. Ordinary parameters always carry a colon, so neither occurs there; the
    variadic `...` (`..` before `.`) and negative numbers (`-` before a numeral) fall through. -/
def istAdaptSeg : List Token → Nat → Bool
  | [], _ => false
  | .zeichen "(" :: rest, tiefe => istAdaptSeg rest (tiefe + 1)
  | .zeichen "[" :: rest, tiefe => istAdaptSeg rest (tiefe + 1)
  | .zeichen "{" :: rest, tiefe => istAdaptSeg rest (tiefe + 1)
  | .zeichen ")" :: rest, tiefe =>
    if tiefe == 0 then false else istAdaptSeg rest (tiefe - 1)
  | .zeichen "]" :: rest, tiefe =>
    if tiefe == 0 then false else istAdaptSeg rest (tiefe - 1)
  | .zeichen "}" :: rest, tiefe =>
    if tiefe == 0 then false else istAdaptSeg rest (tiefe - 1)
  | .zeichen ".." :: rest, tiefe =>
    if tiefe == 0 then match rest with
      | .zeichen "," :: _ => true
      | .zeichen ")" :: _ => true
      | _ => istAdaptSeg rest tiefe
    else istAdaptSeg rest tiefe
  | .zeichen "-" :: rest, tiefe =>
    if tiefe == 0 then match rest with
      | t :: .zeichen "," :: _ => match nameText t with
        | some _ => true
        | none => istAdaptSeg rest tiefe
      | t :: .zeichen ")" :: _ => match nameText t with
        | some _ => true
        | none => istAdaptSeg rest tiefe
      | _ => istAdaptSeg rest tiefe
    else istAdaptSeg rest tiefe
  | _ :: rest, tiefe => istAdaptSeg rest tiefe

/-- Whether `fn name (` opens adapter parameters (behind the `fn`). -/
def istAdaptKopf : List Token → Bool
  | .wort _ :: rest => match rest with
    | t :: .zeichen "(" :: rest' => match nameText t with
      | some _ => istAdaptSeg rest' 0
      | none => false
    | _ => false
  | _ => false

/-- One adapter parameter: `..`, `-x`, or a new `x : T`. -/
def parseAdaptParamEinzel (f : Nat) (toks : List Token) :
    Except String (SAdaptParam × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen ".." :: rest => .ok (.alle, rest)
    | .zeichen "-" :: rest => match nimmName rest with
      | .ok (n, r) => .ok (.ohne n, r)
      | .error e => .error e
    | _ => match nimmName toks with
      | .error e => .error e
      | .ok (n, r1) => match fordereZeichen ":" r1 with
        | .error e => .error e
        | .ok r2 => match parseTyp f r2 with
          | .error e => .error e
          | .ok (t, r) => .ok (.neu n t, r)

/-- The adapter parameters after the opening `(`. -/
def parseAdaptParamFolge (f : Nat) (toks : List Token) :
    Except String (List SAdaptParam × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match parseAdaptParamEinzel f toks with
    | .error e => .error e
    | .ok (p, r1) => match r1 with
      | .zeichen "," :: r2 => match r2 with
        | .zeichen ")" :: _ => .ok ([p], r2)
        | _ => match parseAdaptParamFolge f r2 with
          | .error e => .error e
          | .ok (ps, r) => .ok (p :: ps, r)
      | _ => .ok ([p], r1)

/-- The parameter list `( … )` of an adapter head. -/
def parseAdaptParams (f : Nat) (toks : List Token) :
    Except String (List SAdaptParam × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fordereZeichen "(" toks with
    | .error e => .error e
    | .ok r => match r with
      | .zeichen ")" :: r' => .ok ([], r')
      | _ => match parseAdaptParamFolge f r with
        | .error e => .error e
        | .ok (ps, r') => match fordereZeichen ")" r' with
          | .error e => .error e
          | .ok r'' => .ok (ps, r'')

/-- The optional `=> a [else (e) block]` behind the source. -/
def parseAdaptBindung (f : Nat) (toks : List Token) :
    Except String (Option String × Option (String × SAnw) × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "=>" :: rest => match nimmName rest with
      | .error e => .error e
      | .ok (a, r1) => match r1 with
        | .wort "else" :: .zeichen "(" :: r2 => match nimmName r2 with
          | .error e => .error e
          | .ok (e, r3) => match fordereZeichen ")" r3 with
            | .error e => .error e
            | .ok r4 => match parseBlock f r4 with
              | .error e => .error e
              | .ok (b, r) => .ok (some a, some (e, b), r)
        | _ => .ok (some a, none, r1)
    | _ => .ok (none, none, toks)

/-- The prelude `[ stmts ]` (absent: no statements). -/
def parseAdaptVorspiel (f : Nat) (toks : List Token) :
    Except String (List SAnw × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "[" :: rest => parseVorFolge f rest
    | _ => .ok ([], toks)
where
  parseVorFolge : Nat → List Token → Except String (List SAnw × List Token)
    | 0, _ => .error "out of fuel"
    | f + 1, .zeichen "]" :: rest => .ok ([], rest)
    | _, [] => .error "prelude without ]"
    | _, .ende :: _ => .error "prelude without ]"
    | f + 1, toks => match parseStmt f toks with
      | .error e => .error e
      | .ok (s, rest) => match parseVorFolge f rest with
        | .error e => .error e
        | .ok (ss, r) => .ok (s :: ss, r)

/-- An adapter item: `fn name(adaptparams) [-> T] [or R] from f [=> a [else (e) block]]
    clauses [prelude] (block | ;)`. -/
def parseAdapt (f : Nat) (art : String) (toks : List Token) :
    Except String (SItemTief × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmWort "fn" toks with
    | .error e => .error e
    | .ok r1 => match nimmName r1 with
      | .error e => .error e
      | .ok (name, r2) => match parseAdaptParams f r2 with
        | .error e => .error e
        | .ok (ps, r3) => match parseErgebnis f r3 with
          | .error e => .error e
          | .ok (erg, fehler, r4) => match nimmWort "from" r4 with
            | .error e => .error e
            | .ok r5 => match nimmPfad r5 with
              | .error e => .error e
              | .ok (pfad, r6) => match r6 with
                | .zeichen "::" :: .zeichen "[" :: _ =>
                  .error "type arguments without G form"
                | _ => match parseAdaptBindung f r6 with
                  | .error e => .error e
                  | .ok (geb, sonst, r7) => match parseKlauseln f r7 with
                    | .error e => .error e
                    | .ok (ks, r8) => match parseAdaptVorspiel f r8 with
                      | .error e => .error e
                      | .ok (vor, r9) =>
                        let sig : FnSig :=
                          { art, name, params := [], res := erg, fehler, klauseln := ks }
                        let a : SAdapt :=
                          { quelle := "::".intercalate pfad, gebunden := geb, sonst, vorspiel := vor }
                        match r9 with
                        | .zeichen "{" :: _ => match parseBlock f r9 with
                          | .error e => .error e
                          | .ok (b, r) => .ok (.adaptT sig ps a (some b), r)
                        | .zeichen ";" :: rest => .ok (.adaptT sig ps a none, rest)
                        | _ => .error "adapter without body"

/-- Shape equality on program outcomes, as a `Bool`. -/
def beqTopTief : Except String (List SItemTief) →
    Except String (List SItemTief) → Bool
  | .ok a, .ok b => beqSItemTiefList a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false
