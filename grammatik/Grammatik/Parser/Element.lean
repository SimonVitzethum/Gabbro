/-
  File:      Grammatik/Parser/Element.lean
  Subject:   T3 PART 2: Gabbro items (SYNTAX.md section 1, `item`) over
              the Lean statement reader, step 1.

  Skeleton: the surface AST `SItem`. Readers land in the next steps.
-/
import Grammatik.Parser.Anweisung

namespace Gabbro.Grammatik.Parser

/- A surface item: SYNTAX.md section 1 `item` without types, spans
    or checks. Function and translator bodies ride as `SBlock`;
    every other body is skipped balanced (see CUTS). Against
    `ast.rs` `ItemArt`: `modul` = `Modul`, `useS` = `Use`, `typS` =
    `Typ`, `konstS` = `Konst`, `statikS` = `Statisch`, `funktion` =
    `Funktion` (with a block), `protoS` = a bodiless declaration
    (`fn …;`, `spec fn … = pred;`, `= asm {…};`), `formatS` =
    `Format`, `tabelle` = `Tabelle`, `arenaS` = `Arena`, `grundS` =
    `Reason`, `zustandS` = `State`, `geraetS` = `Device`, `annahmeS` =
    `Assume`, `axiomaS` = `Axiom`, `pruefungS` = `Check`, `atomarS` =
    `Atomic`, `sperreS` = `Lock`, `rcuS` = `Rcu`, `gruppeS` =
    `Gruppe`, `nebenS` = `Concurrent`, `akkumS` = `Accumulates`,
    `wegS` = `Walk`, `eingangS` = `Entry`, `anvertrautS` =
    `Entrust`, `startS` = `Boot`, `sysrufS` = `Syscall`,
    `uebersetzerS` = `Translator`, `profilS` = `Profil` (`false`)
    / `ProfilBedarf` (`true`), `torS` = the `when TESTBUILD` gate. -/
inductive SItem
  | modul : String → List SItem → SItem
  | useS : String → SItem
  | typS : String → SItem
  | konstS : String → SItem
  | statikS : String → SItem
  | funktion : String → SBlock → SItem
  | protoS : String → SItem
  | formatS : String → SItem
  | tabelle : String → SItem
  | arenaS : String → SItem
  | grundS : String → SItem
  | zustandS : String → SItem
  | geraetS : String → SItem
  | annahmeS : String → SItem
  | axiomaS : String → SItem
  | pruefungS : String → SItem
  | atomarS : String → SItem
  | sperreS : String → SItem
  | rcuS : String → SItem
  | gruppeS : String → SItem
  | nebenS : String → SItem
  | akkumS : String → SItem
  | wegS : String → SItem
  | eingangS : String → SItem
  | anvertrautS : String → SItem
  | startS : String → SItem
  | sysrufS : String → SItem
  | uebersetzerS : String → SBlock → SItem
  | profilS : Bool → SItem
  | torS : SItem → SItem
  deriving Repr

-- Shape equality on surface items, as a `Bool` (same reason as
-- `beqSStmt`: the probes compare by kernel evaluation).
mutual
def beqSItem : SItem → SItem → Bool
  | .modul p a, .modul q b => strEq p q && beqSItemList a b
  | .useS a, .useS b => strEq a b
  | .typS a, .typS b => strEq a b
  | .konstS a, .konstS b => strEq a b
  | .statikS a, .statikS b => strEq a b
  | .funktion n b, .funktion m d => strEq n m && beqSBlock b d
  | .protoS a, .protoS b => strEq a b
  | .formatS a, .formatS b => strEq a b
  | .tabelle a, .tabelle b => strEq a b
  | .arenaS a, .arenaS b => strEq a b
  | .grundS a, .grundS b => strEq a b
  | .zustandS a, .zustandS b => strEq a b
  | .geraetS a, .geraetS b => strEq a b
  | .annahmeS a, .annahmeS b => strEq a b
  | .axiomaS a, .axiomaS b => strEq a b
  | .pruefungS a, .pruefungS b => strEq a b
  | .atomarS a, .atomarS b => strEq a b
  | .sperreS a, .sperreS b => strEq a b
  | .rcuS a, .rcuS b => strEq a b
  | .gruppeS a, .gruppeS b => strEq a b
  | .nebenS a, .nebenS b => strEq a b
  | .akkumS a, .akkumS b => strEq a b
  | .wegS a, .wegS b => strEq a b
  | .eingangS a, .eingangS b => strEq a b
  | .anvertrautS a, .anvertrautS b => strEq a b
  | .startS a, .startS b => strEq a b
  | .sysrufS a, .sysrufS b => strEq a b
  | .uebersetzerS n b, .uebersetzerS m d => strEq n m && beqSBlock b d
  | .profilS a, .profilS b => a == b
  | .torS a, .torS b => beqSItem a b
  | _, _ => false
def beqSItemList : List SItem → List SItem → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSItem x y && beqSItemList xs ys
  | _, _ => false
end

-- Raw words until one of the stoppers at depth zero (braces
-- tracked). Structural on the token list, like `nimmBisWort`.
def nimmBisStop (stopper : List String) : List Token → Nat →
    Except String (String × String × List Token)
  | [], _ => .error "item without end"
  | (.zeichen "{" :: rest), tiefe => match nimmBisStop stopper rest (tiefe + 1) with
    | .ok (g, h, r) => .ok (g, "{ " ++ h, r)
    | .error e => .error e
  | (.zeichen "}" :: rest), tiefe =>
    if tiefe == 0 then .error "item without end"
    else match nimmBisStop stopper rest (tiefe - 1) with
      | .ok (g, h, r) => .ok (g, "} " ++ h, r)
      | .error e => .error e
  | (.zeichen s :: rest), tiefe =>
    if tiefe == 0 && stopper.any (strEq · s) then
      .ok (s, "", .zeichen s :: rest)
    else match nimmBisStop stopper rest tiefe with
      | .ok (g, h, r) => .ok (g, s ++ " " ++ h, r)
      | .error e => .error e
  | (t :: rest), tiefe => match nimmBisStop stopper rest tiefe with
    | .ok (g, h, r) => .ok (g, zeigeTok t ++ " " ++ h, r)
    | .error e => .error e

/-- The pure prefix words before an item head (`parse.rs` `item`:
    `pub` plus the `fn`/`type` modifiers; `const` is NOT among them
    -- `const fn` splits on the next word, as in `parse.rs`). -/
def istMod (s : String) : Bool :=
  ["library", "spec", "impl", "raw", "divergent", "prim", "extern",
   "opaque", "linear", "ghost", "tagged"].any (strEq · s)

-- The item levels of SYNTAX.md section 1 (`item`), each with fuel.
-- Against `parse.rs` `item`: the `when TESTBUILD` gate, the `pub`
-- prefix, the `const fn` split and the head-word dispatch match one
-- by one. Function headers are skipped by `fnStart` (the `effects`
-- braces are the only header braces); every other non-module body
-- is skipped balanced by `ueberspringe` (see CUTS).
mutual
def ueberspringe (f : Nat) (toks : List Token) :
    Except String (List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "{" :: rest => match nimmBereich rest 1 with
      | .ok r => ueberspringe f r
      | .error e => .error e
    | .zeichen ";" :: rest => .ok rest
    | .ende :: _ => .error "item without ;"
    | [] => .error "item without ;"
    | _ :: rest => ueberspringe f rest
/-- Past a function header to the body `{`, the `;` or the `=`
    (`spec fn … = pred;`, `= asm {…};`). The `effects {…}` braces
    are skipped balanced; every other header clause is brace-free
    (see CUTS for the assumption). -/
def fnStart (f : Nat) (toks : List Token) : Except String (List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: .zeichen "{" :: rest =>
      if strEq s "effects" then match nimmBereich rest 1 with
        | .ok r => fnStart f r
        | .error e => .error e
      else .ok toks
    | .zeichen "{" :: _ => .ok toks
    | .zeichen ";" :: _ => .ok toks
    | .zeichen "=" :: _ => .ok toks
    | _ :: rest => fnStart f rest
    | [] => .error "fn without body"
def parseItems (f : Nat) (toks : List Token) :
    Except String (List SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .zeichen "}" :: _ => .ok ([], toks)
    | .ende :: _ => .ok ([], toks)
    | [] => .ok ([], [])
    | _ => match parseItem f toks with
      | .error e => .error e
      | .ok (it, rest) => match parseItems f rest with
        | .error e => .error e
        | .ok (its, r) => .ok (it :: its, r)
def parseItem (f : Nat) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if strEq s "when" then match rest with
        | .wort t :: rest' =>
          if strEq t "TESTBUILD" then match parseItem f rest' with
            | .ok (it, r) => .ok (.torS it, r)
            | .error e => .error e
          else .error "when without TESTBUILD"
        | _ => .error "when without TESTBUILD"
      else if strEq s "pub" then parseItemKopf f rest
      else parseItemKopf f toks
    | _ => parseItemKopf f toks
def parseItemKopf (f : Nat) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match toks with
    | .wort s :: rest =>
      if istMod s then parseItemKopf f rest
      else if strEq s "module" then parseModul f rest
      else if strEq s "use" then parseRoh f .useS rest
      else if strEq s "fn" then parseFnName f false rest
      else if strEq s "translator" then parseTranslator f rest
      else if strEq s "profile" then parseProfil f false rest
      else if strEq s "requires" then match rest with
        | .wort t :: rest' =>
          if strEq t "profile" then parseProfil f true rest'
          else .error "requires without profile"
        | _ => .error "requires without profile"
      else if strEq s "concurrent" then parseRoh f .nebenS rest
      else if strEq s "type" then parseEinfach f .typS rest
      else if strEq s "const" then match rest with
        | .wort t :: _ =>
          if strEq t "fn" then parseFnName f false rest.tail
          else parseEinfach f .konstS rest
        | _ => parseEinfach f .konstS rest
      else if strEq s "static" then parseEinfach f .statikS rest
      else if strEq s "format" then parseEinfach f .formatS rest
      else if strEq s "table" then parseEinfach f .tabelle rest
      else if strEq s "arena" then parseEinfach f .arenaS rest
      else if strEq s "reason" then parseEinfach f .grundS rest
      else if strEq s "state" then parseEinfach f .zustandS rest
      else if strEq s "device" then parseEinfach f .geraetS rest
      else if strEq s "assume" then parseEinfach f .annahmeS rest
      else if strEq s "axiom" then parseEinfach f .axiomaS rest
      else if strEq s "check" then parseEinfach f .pruefungS rest
      else if strEq s "atomic" then parseEinfach f .atomarS rest
      else if strEq s "lock" then parseEinfach f .sperreS rest
      else if strEq s "rcu" then parseEinfach f .rcuS rest
      else if strEq s "group" then parseEinfach f .gruppeS rest
      else if strEq s "accumulates" then parseEinfach f .akkumS rest
      else if strEq s "walk" then parseEinfach f .wegS rest
      else if strEq s "entry" then parseEinfach f .eingangS rest
      else if strEq s "entrust" then parseEinfach f .anvertrautS rest
      else if strEq s "boot" then parseEinfach f .startS rest
      else if strEq s "syscall" then parseEinfach f .sysrufS rest
      else .error "item expected"
    | _ => .error "item expected"
/-- `use …;`, `concurrent …;`: the raw tail until `;`. -/
def parseRoh (f : Nat) (mk : String → SItem) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmBisZeichen ";" toks 0 with
    | .error e => .error e
    | .ok (h, rest) => match fordereZeichen ";" rest with
      | .ok rest' => .ok (mk h, rest')
      | .error e => .error e
/-- A named item whose body is skipped: the first name (past an
    optional `mut`), then `ueberspringe`. -/
def parseEinfach (f : Nat) (mk : String → SItem) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 =>
    let (name, rest) := match nimmName toks with
      | .ok (n, r) =>
        if strEq n "mut" then match nimmName r with
          | .ok (m, r') => (m, r')
          | .error _ => (n, r)
        else (n, r)
      | .error _ => ("", toks)
    match ueberspringe f rest with
    | .ok r => .ok (mk name, r)
    | .error e => .error e
def parseProfil (f : Nat) (bedarf : Bool) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match ueberspringe f toks with
    | .ok r => .ok (.profilS bedarf, r)
    | .error e => .error e
def parseModul (f : Nat) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmBisZeichen "{" toks 0 with
    | .error e => .error e
    | .ok (pfad, rest) => match fordereZeichen "{" rest with
      | .error e => .error e
      | .ok rest' => match parseItems f rest' with
        | .error e => .error e
        | .ok (its, rest'') => match fordereZeichen "}" rest'' with
          | .ok rest3 => .ok (.modul pfad its, rest3)
          | .error e => .error e
def parseFnName (f : Nat) (isTrans : Bool) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (name, rest) => parseFnMit f isTrans name rest
def parseTranslator (f : Nat) (toks : List Token) :
    Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match nimmName toks with
    | .error e => .error e
    | .ok (tname, rest) => match nimmWort "for" rest with
      | .error e => .error e
      | .ok rest' => match nimmName rest' with
        | .error e => .error e
        | .ok (_, rest'') => parseFnMit f true tname rest''
def parseFnMit (f : Nat) (isTrans : Bool) (name : String)
    (toks : List Token) : Except String (SItem × List Token) :=
  match f with
  | 0 => .error "out of fuel"
  | f + 1 => match fnStart f toks with
    | .error e => .error e
    | .ok rest => match rest with
      | .zeichen "{" :: _ => match parseBlock f rest with
        | .error e => .error e
        | .ok (b, r) =>
          if isTrans then .ok (.uebersetzerS name b, r)
          else .ok (.funktion name b, r)
      | .zeichen "=" :: _ => match nimmBisZeichen ";" rest.tail 0 with
        | .error e => .error e
        | .ok (_, r) => match fordereZeichen ";" r with
          | .ok r2 => .ok (.protoS name, r2)
          | .error e => .error e
      | .zeichen ";" :: rest' => .ok (.protoS name, rest')
      | _ => .error "fn without body"
/-- A whole program: the token list must end here. -/
def parseTopItems (toks : List Token) : Except String (List SItem) :=
  match parseItems (toks.length * 8 + 32) toks with
  | .ok (its, [.ende]) => .ok its
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e
/-- Shape equality on program outcomes, as a `Bool`. -/
def beqTopItems : Except String (List SItem) → Except String (List SItem) → Bool
  | .ok a, .ok b => beqSItemList a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false
end

end Gabbro.Grammatik.Parser

/-
  CUTS: the readers land in the next steps; this skeleton only fixes
  the surface type.
-/

#print axioms Gabbro.Grammatik.Parser.SItem.modul
