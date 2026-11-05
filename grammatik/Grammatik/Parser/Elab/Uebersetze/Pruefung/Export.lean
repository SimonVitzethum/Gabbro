/- C16 inventory item 16 (elaborator half): connected export over the
    ACTUAL path.

    `uCheckIdx` resolves an elaborated check's probe and gate names to
    function indices of the elaborated unit, refusing an unknown Duty; the
    probes run on the real `elabU` output (`uCheckAufloesung`, transported from
    its complete result certificate). `elabText` chains the actual stages -- lex, parse,
    elaborate -- on source text, with one end-to-end acceptance witness and
    refusal witnesses (unknown gate, duplicate check). `checkB_leer` pins the
    empty leg, which still holds vacuously. The Duty gap is closed
    (`Ableitung.uCheckDecls`, `Zulassung.checkU_akzeptiert`). `treue_aus_entladung` connects the discharge to the
    goal leg `CheckTreueG`. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Proben
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.Generic.Signatures
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil1
public import Grammatik.Parser.Lex.Lexer.Teil1
public import Grammatik.Parser.Item.ElementTief.Defs7
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Spec.Teil4
public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Recording
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.SondeCode
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Item.ElementTief.Defs5
import all Grammatik.Parser.Item.ElementTief.Defs7
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

variable {D : Deklaration} [DecidableEq D.Fn]

/-- Resolve an elaborated check to function indices of the elaborated unit:
    the probe and every gate, with the Duty checked against the mark table.
    A gate naming no function is refused, never auto-run. -/
def uCheckIdx (u : UProg) (c : UCheck) : Except String (Fin u.fns.length × List (Fin u.fns.length)) := do
  if !(u.marken.any fun m => strEq m c.duty) then .error ("duty unknown: " ++ c.duty)
  else
    let p ← UebersetzeAllg.fnIdx u.fns c.probe
    let gs ← uSeq (c.tore.map fun gate =>
      UebersetzeAllg.fnIdx u.fns (torHuellenName c.name gate))
    .ok (p, gs)

/-- The resolution read back as names. -/
def uCheckAufloesung (u : UProg) (c : UCheck) :
    Except String (String × List String) := do
  let (p, gs) ← uCheckIdx u c
  .ok ((UebersetzeAllg.fnAt u p).name, gs.map fun g => (UebersetzeAllg.fnAt u g).name)

/-- Construct all observations on the actual successful result before transporting
    any dependent function index to a consumer. -/
private theorem probe_certificate : ∃ u : UProg,
    elabU [probenFn, .checkT probenCheck] = .ok u ∧
    (match u.checks with
      | [c] => uCheckAufloesung u c
      | _ => .error "shape") = .ok ("p#probe", ["p#tor#g"]) ∧
    (match u.checks with
      | [c] => uCheckIdx u { c with tore := ["h"] }
      | _ => .error "shape") = .error "function unknown: p#tor#h" ∧
    (match u.checks with
      | [c] => uCheckIdx u { c with duty := "q#duty" }
      | _ => .error "shape") = .error "duty unknown: q#duty" := by
  refine ⟨?unit, ?elaborated, ?observed⟩
  case elaborated => cbv <;> exact Eq.refl _
  case observed => cbv

/-- The elaborated check resolves to its generated producer and its gate. -/
example : ((elabU [probenFn, .checkT probenCheck]).bind fun u =>
    match u.checks with
    | [c] => uCheckAufloesung u c
    | _ => .error "shape") = .ok ("p#probe", ["p#tor#g"]) := by
  obtain ⟨u, elaborated, facts⟩ := probe_certificate
  rw [elaborated]
  exact facts.1

/-- A gate naming no function is refused on the resolved unit. -/
example : ((elabU [probenFn, .checkT probenCheck]).bind fun u =>
    match u.checks with
    | [c] => uCheckIdx u { c with tore := ["h"] }
    | _ => .error "shape") = .error "function unknown: p#tor#h" := by
  obtain ⟨u, elaborated, facts⟩ := probe_certificate
  rw [elaborated]
  exact facts.2.1

/-- A Duty outside the mark table is refused on the resolved unit. -/
example : ((elabU [probenFn, .checkT probenCheck]).bind fun u =>
    match u.checks with
    | [c] => uCheckIdx u { c with duty := "q#duty" }
    | _ => .error "shape") = .error "duty unknown: q#duty" := by
  obtain ⟨u, elaborated, facts⟩ := probe_certificate
  rw [elaborated]
  exact facts.2.2

/-! ## From source text through the actual stages -/

/-- The minimal check unit: one gate function, one check over one variable
    with a true body. -/
def checkText : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return true; } }"

/-- A gate naming no function is refused from source text. -/
def checkTextFremdTor : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates h can_fail { return true; } }"

/-- A duplicate check name is refused from source text, never merged. -/
def checkTextDoppelt : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return true; } } check p { claim \"d\" measures x gates g can_fail { return true; } }"

/-- Lexing with a plain error channel. -/
def lexStr (text : String) : Except String (List Token) :=
  match lex text with
  | .ok toks => .ok toks
  | .error _ => .error "lex failed"

/-- Lex, parse, elaborate: the actual source path. -/
def elabText (text : String) : Except String UProg :=
  match lexStr text with
  | .error e => .error e
  | .ok toks =>
    match parseTopTief toks with
    | .error e => .error e
    | .ok items => elabU items

/-- Transport complete phase equations without evaluating a String decoder or
    inspecting an opaque extracted unit inside a dependent match. -/
private theorem elabText_phases {text : String} {characters : List Char}
    {tokens : List Token} {items : List SItemTief}
    (source : text = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) : elabText text = elabU items := by
  rw [source]
  unfold elabText lexStr
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]

private theorem token_maps (tokens tail : List Token) :
    tokens.foldr (fun token result => Except.map (token :: ·) result)
      (.ok tail : Except LexFehler (List Token)) = .ok (tokens ++ tail) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih => simp only [List.foldr_cons, ih, Except.map, List.cons_append]

private theorem scan_compose {source rest : List Char} {fuel remaining : Nat}
    {emitted tokens : List Token} (tail : scan false rest remaining = .ok tokens)
    (head : scan false source fuel =
      emitted.foldr (fun token result => Except.map (token :: ·) result) (scan false rest remaining)) :
    scan false source fuel = .ok (emitted ++ tokens) := by
  rw [tail, token_maps] at head
  exact head

private def gateCharacters : List Char :=
  ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'g', '(', ')', ' ', '{', ' ',
    'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ']
private def gateTokens : List Token :=
  [.wort "impl", .wort "fn", .ident "g", .zeichen "(", .zeichen ")", .zeichen "{",
    .wort "return", .zeichen ";", .zeichen "}"]
private def headCharacters : List Char :=
  ['c', 'h', 'e', 'c', 'k', ' ', 'p', ' ', '{', ' ', 'c', 'l', 'a', 'i', 'm', ' ']
private def headTokens : List Token := [.wort "check", .ident "p", .zeichen "{", .wort "claim"]
private def measureCharacters (claim gate : Char) : List Char :=
  ['"', claim, '"', ' ', 'm', 'e', 'a', 's', 'u', 'r', 'e', 's', ' ', 'x', ' ',
    'g', 'a', 't', 'e', 's', ' ', gate, ' ']
private def measureTokens (claim gate : String) : List Token :=
  [.text claim, .wort "measures", .wort "x", .wort "gates", .ident gate]
private def tailCharacters : List Char :=
  ['c', 'a', 'n', '_', 'f', 'a', 'i', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n',
    ' ', 't', 'r', 'u', 'e', ';', ' ', '}', ' ']
private def tailTokens : List Token :=
  [.wort "can_fail", .zeichen "{", .wort "return", .wort "true", .zeichen ";", .zeichen "}"]

private theorem scan_gate (rest : List Char) (fuel : Nat) :
    scan false (gateCharacters ++ rest) (fuel + 15) =
      gateTokens.foldr (fun token result => Except.map (token :: ·) result) (scan false rest fuel) := by cbv
private theorem scan_head (rest : List Char) (fuel : Nat) :
    scan false (headCharacters ++ rest) (fuel + 8) =
      headTokens.foldr (fun token result => Except.map (token :: ·) result) (scan false rest fuel) := by cbv
private theorem scan_measure_cg (rest : List Char) (fuel : Nat) :
    scan false (measureCharacters 'c' 'g' ++ rest) (fuel + 10) =
      (measureTokens "c" "g").foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv
private theorem scan_measure_ch (rest : List Char) (fuel : Nat) :
    scan false (measureCharacters 'c' 'h' ++ rest) (fuel + 10) =
      (measureTokens "c" "h").foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv
private theorem scan_measure_dg (rest : List Char) (fuel : Nat) :
    scan false (measureCharacters 'd' 'g' ++ rest) (fuel + 10) =
      (measureTokens "d" "g").foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv
private theorem scan_tail (rest : List Char) (fuel : Nat) :
    scan false (tailCharacters ++ rest) (fuel + 11) =
      tailTokens.foldr (fun token result => Except.map (token :: ·) result) (scan false rest fuel) := by cbv
private theorem scan_close (rest : List Char) (fuel : Nat) :
    scan false (['}', ' '] ++ rest) (fuel + 2) =
      [.zeichen "}"].foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv
private theorem scan_end (fuel : Nat) :
    scan false ['}'] (fuel + 1) = .ok [.zeichen "}", .ende] := by cbv

private def textCharacters (claim gate : Char) : List Char :=
  gateCharacters ++ headCharacters ++ measureCharacters claim gate ++ tailCharacters ++ ['}']
private def textTokens (claim gate : String) : List Token :=
  gateTokens ++ headTokens ++ measureTokens claim gate ++ tailTokens ++ [.zeichen "}", .ende]
private def duplicateCharacters : List Char :=
  gateCharacters ++ headCharacters ++ measureCharacters 'c' 'g' ++ tailCharacters ++ ['}', ' '] ++
    headCharacters ++ measureCharacters 'd' 'g' ++ tailCharacters ++ ['}']
private def duplicateTokens : List Token :=
  gateTokens ++ headTokens ++ measureTokens "c" "g" ++ tailTokens ++ [.zeichen "}"] ++
    headTokens ++ measureTokens "d" "g" ++ tailTokens ++ [.zeichen "}", .ende]

private theorem text_lexed : lexL (textCharacters 'c' 'g') = .ok (textTokens "c" "g") := by
  change scan false (textCharacters 'c' 'g') 91 = _
  have complete := scan_compose (scan_end 46) (scan_tail ['}'] 47)
  have complete := scan_compose complete (scan_measure_cg (tailCharacters ++ ['}']) 58)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'c' 'g' ++ tailCharacters ++ ['}']) 68)
  exact scan_compose complete
    (scan_gate (headCharacters ++ measureCharacters 'c' 'g' ++ tailCharacters ++ ['}']) 76)

private theorem foreign_lexed : lexL (textCharacters 'c' 'h') = .ok (textTokens "c" "h") := by
  change scan false (textCharacters 'c' 'h') 91 = _
  have complete := scan_compose (scan_end 46) (scan_tail ['}'] 47)
  have complete := scan_compose complete (scan_measure_ch (tailCharacters ++ ['}']) 58)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'c' 'h' ++ tailCharacters ++ ['}']) 68)
  exact scan_compose complete
    (scan_gate (headCharacters ++ measureCharacters 'c' 'h' ++ tailCharacters ++ ['}']) 76)

private theorem duplicate_lexed : lexL duplicateCharacters = .ok duplicateTokens := by
  change scan false duplicateCharacters 158 = _
  let second := headCharacters ++ measureCharacters 'd' 'g' ++ tailCharacters ++ ['}']
  have complete := scan_compose (scan_end 82) (scan_tail ['}'] 83)
  have complete := scan_compose complete (scan_measure_dg (tailCharacters ++ ['}']) 94)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'd' 'g' ++ tailCharacters ++ ['}']) 104)
  have complete := scan_compose complete (scan_close second 112)
  have complete := scan_compose complete (scan_tail (['}', ' '] ++ second) 114)
  have complete := scan_compose complete
    (scan_measure_cg (tailCharacters ++ ['}', ' '] ++ second) 125)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'c' 'g' ++ tailCharacters ++ ['}', ' '] ++ second) 135)
  exact scan_compose complete
    (scan_gate (headCharacters ++ measureCharacters 'c' 'g' ++ tailCharacters ++ ['}', ' '] ++ second) 143)

private def textGate : SItemTief :=
  .fnT
    { art := "impl"
      name := "g"
      params := []
      res := none
      fehler := none
      klauseln := []
      generics := [] } (.block [] (some (.ret none)))
private def textCheck (claim gate : String) : SCheck :=
  { cname := "p"
    claim := claim
    misst := [.variable "x"]
    gates := [gate]
    canFail := .block [] (some (.ret (some .tru)))
    boden := []
    sonde := none }
private def textItems (claim gate : String) : List SItemTief :=
  [textGate, .checkT (textCheck claim gate)]
private def duplicateItems : List SItemTief :=
  [textGate, .checkT (textCheck "c" "g"), .checkT (textCheck "d" "g")]

private theorem text_source : checkText = String.ofList (textCharacters 'c' 'g') := by cbv
private theorem foreign_source : checkTextFremdTor = String.ofList (textCharacters 'c' 'h') := by cbv
private theorem duplicate_source : checkTextDoppelt = String.ofList duplicateCharacters := by cbv
private theorem text_parsed : parseTopTief (textTokens "c" "g") = .ok (textItems "c" "g") := by cbv
private theorem foreign_parsed : parseTopTief (textTokens "c" "h") = .ok (textItems "c" "h") := by cbv
private theorem duplicate_parsed : parseTopTief duplicateTokens = .ok duplicateItems := by cbv

private def TextFacts (u : UProg) : Prop :=
  u.checks.map (·.name) = ["p"] ∧
  u.fns.map (·.name) = ["g", "p#probe", "p#report#0", "p#tor#g"] ∧
  u.marken = ["p#duty"] ∧
  (match u.checks with
    | [c] => uCheckAufloesung u c
    | _ => .error "shape") = .ok ("p#probe", ["p#tor#g"])

private theorem text_elaborated : ∃ u : UProg,
    elabU (textItems "c" "g") = .ok u ∧ TextFacts u := by
  refine ⟨?unit, ?elaborated, ?observed⟩
  case elaborated => cbv <;> exact Eq.refl _
  case observed => cbv

private theorem text_certificate : ∃ u : UProg, elabText checkText = .ok u ∧ TextFacts u := by
  obtain ⟨u, elaborated, facts⟩ := text_elaborated
  exact ⟨u, (elabText_phases text_source text_lexed text_parsed).trans elaborated, facts⟩

/-- End-to-end from source text: the check elaborates with its name. -/
example : (elabText checkText).map (fun u => u.checks.map (·.name)) =
    .ok ["p"] := by
  obtain ⟨u, elaborated, facts⟩ := text_certificate
  simpa only [elaborated, Except.map] using
    congrArg (fun names : List String => (Except.ok names : Except String (List String))) facts.1

/-- End-to-end from source text: the probe and its gate wrapper travel with
    the written gate. -/
example : (elabText checkText).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#report#0", "p#tor#g"] := by
  obtain ⟨u, elaborated, facts⟩ := text_certificate
  simpa only [elaborated, Except.map] using
    congrArg (fun names : List String => (Except.ok names : Except String (List String))) facts.2.1

/-- End-to-end from source text: the mark table carries the check's Duty. -/
example : (elabText checkText).map (fun u => u.marken) = .ok ["p#duty"] := by
  obtain ⟨u, elaborated, facts⟩ := text_certificate
  simpa only [elaborated, Except.map] using
    congrArg (fun names : List String => (Except.ok names : Except String (List String))) facts.2.2.1

/-- End-to-end from source text: the elaborated check resolves. -/
example : ((elabText checkText).bind fun u =>
    match u.checks with
    | [c] => uCheckAufloesung u c
    | _ => .error "shape") = .ok ("p#probe", ["p#tor#g"]) := by
  obtain ⟨u, elaborated, facts⟩ := text_certificate
  rw [elaborated]
  exact facts.2.2.2

private theorem foreign_refused : (elabU (textItems "c" "h")).isErr = true := by cbv
private theorem duplicate_refused : (elabU duplicateItems).isErr = true := by cbv

example : (elabText checkTextFremdTor).isErr = true := by
  rw [elabText_phases foreign_source foreign_lexed foreign_parsed]
  exact foreign_refused

example : (elabText checkTextDoppelt).isErr = true := by
  rw [elabText_phases duplicate_source duplicate_lexed duplicate_parsed]
  exact duplicate_refused

/-! ## The empty leg still holds vacuously; the Duty gap is closed -/

/-- The empty admission holds vacuously: no checks, nothing to discharge. -/
theorem checkB_leer (P : Programm D) (tabs : List D.Tab) (globs : List D.Glob)
    (fns : List D.Fn) : checkB P tabs globs fns [] = true := rfl

/-- The discharge satisfies the goal leg: the consumed entry of the probe
    with the completed report names exactly one declared gate of the check. -/
theorem treue_aus_entladung {P : Programm D} {c : CheckDecl D}
    {r : CheckReport} {g : D.Fn} (h : CheckEntladung P c r g) :
    Zielsatz.CheckTreueG P [c] [⟨c.probe, r, false, some g⟩] := by
  obtain ⟨_, _, hg⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨c, List.mem_singleton_self _, rfl⟩
  · intro e he c' hc' _
    simp only [List.mem_singleton] at he hc'
    subst he
    subst hc'
    exact Or.inr ⟨rfl, g, hg, rfl⟩
  · intro c' hc' e₁ he₁ e₂ he₂ _ _ _ _
    simp only [List.mem_singleton] at hc' he₁ he₂
    subst hc'
    subst he₁
    subst he₂
    exact ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.Uebersetze
