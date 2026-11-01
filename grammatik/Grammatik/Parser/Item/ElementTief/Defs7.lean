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
        else if strEq s "fn" then match parseFnSig f (letzteArt mods) nach with
          | .error e => .error e
          | .ok (sig, r) => parseFnRest f sig r
        else if strEq s "translator" then parseTranslatorTief f nach
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

/-- Shape equality on program outcomes, as a `Bool`. -/
def beqTopTief : Except String (List SItemTief) →
    Except String (List SItemTief) → Bool
  | .ok a, .ok b => beqSItemTiefList a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false
