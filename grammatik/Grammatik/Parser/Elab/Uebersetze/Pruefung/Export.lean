/- C16 inventory item 16 (elaborator half): connected export over the
    ACTUAL path.

    `uCheckIdx` resolves an elaborated check's probe and gate names to
    function indices of the elaborated unit, refusing an unknown Duty; the
    probes run on the real `elabU` output (`uCheckAufloesung`, decided by
    kernel evaluation). `elabText` chains the actual stages -- lex, parse,
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

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

variable {D : Deklaration} [DecidableEq D.Fn]

/-- Resolve an elaborated check to function indices of the elaborated unit:
    the probe and every gate, with the Duty checked against the mark table.
    A gate naming no function is refused, never auto-run. -/
def uCheckIdx (u : UProg) (c : UCheck) : Except String (Fin u.fns.length × List (Fin u.fns.length)) := do
  if !(u.marken.any fun m => strEq m c.duty) then .error ("duty unknown: " ++ c.duty)
  else
    let p ← UebersetzeAllg.fnIdx u.fns c.probe
    let gs ← uSeq (c.tore.map (UebersetzeAllg.fnIdx u.fns))
    .ok (p, gs)

/-- The resolution read back as names. -/
def uCheckAufloesung (u : UProg) (c : UCheck) :
    Except String (String × List String) := do
  let (p, gs) ← uCheckIdx u c
  .ok ((UebersetzeAllg.fnAt u p).name, gs.map fun g => (UebersetzeAllg.fnAt u g).name)

/-- The elaborated check resolves to its generated producer and its gate. -/
example : ((elabU [probenFn, .checkT probenCheck]).bind fun u =>
    match u.checks with
    | [c] => uCheckAufloesung u c
    | _ => .error "shape") = .ok ("p#probe", ["g"]) := rfl

/-- A gate naming no function is refused on the resolved unit. -/
example : ((elabU [probenFn, .checkT probenCheck]).bind fun u =>
    match u.checks with
    | [c] => uCheckIdx u { c with tore := ["h"] }
    | _ => .error "shape") = .error "function unknown: h" := rfl

/-- A Duty outside the mark table is refused on the resolved unit. -/
example : ((elabU [probenFn, .checkT probenCheck]).bind fun u =>
    match u.checks with
    | [c] => uCheckIdx u { c with duty := "q#duty" }
    | _ => .error "shape") = .error "duty unknown: q#duty" := rfl

/-! ## From source text through the actual stages -/

/-- The minimal check unit: one gate function, one check over one variable
    with a true body. -/
def checkText : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return true; } }"

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

/-- End-to-end from source text: the check elaborates with its name. -/
example : (elabText checkText).map (fun u => u.checks.map (·.name)) =
    .ok ["p"] := rfl

/-- End-to-end from source text: the probe and its gate wrapper travel with
    the written gate. -/
example : (elabText checkText).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#tor#g"] := rfl

/-- End-to-end from source text: the mark table carries the check's Duty. -/
example : (elabText checkText).map (fun u => u.marken) = .ok ["p#duty"] := rfl

/-- End-to-end from source text: the elaborated check resolves. -/
example : ((elabText checkText).bind fun u =>
    match u.checks with
    | [c] => uCheckAufloesung u c
    | _ => .error "shape") = .ok ("p#probe", ["g"]) := rfl

/-- A gate naming no function is refused from source text. -/
def checkTextFremdTor : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates h can_fail { return true; } }"

example : (elabText checkTextFremdTor).isErr = true := by decide

/-- A duplicate check name is refused from source text, never merged. -/
def checkTextDoppelt : String :=
  "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return true; } } check p { claim \"d\" measures x gates g can_fail { return true; } }"

example : (elabText checkTextDoppelt).isErr = true := by decide

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
    exact ⟨rfl, g, hg, rfl⟩
  · intro c' hc' e₁ he₁ e₂ he₂ _ _ _ _
    simp only [List.mem_singleton] at hc' he₁ he₂
    subst hc'
    subst he₁
    subst he₂
    exact ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.Uebersetze
