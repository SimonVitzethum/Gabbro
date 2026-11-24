module

public import Core.Ast.Semantik.ProgramRegistry
public import Core.Ast.Semantik.Auswertung

/-!
The program forms' control obligations belong with the instruction semantics.
Each instruction is an ideal and a concrete unit. Caller switches, tests and
back-edges are separate visible units, so none of them contributes stuttering.
The finite count of such units is stated independently of their stutter length.
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- Count semantic instructions, including a call, return or back-edge. -/
inductive Rahmen.LaufN (code : List Befehl) : Nat → Rahmen → Rahmen → Prop where
  | null : LaufN code 0 frame frame
  | step : before.stopp = none → before.rueckgabe = none →
      code[before.pc]? = some instruction →
      LaufN code n (instruction.auswerten before) after →
      LaufN code (n + 1) before after

def Rahmen.Aktiv (frame : Rahmen) : Prop := frame.stopp = none ∧ frame.rueckgabe = none

/-- Exiting a loop includes returning from its surrounding function or requesting its handler. -/
def SchleifenAusgang (first limit : Nat) (before after : Rahmen) : Prop :=
  after.stopp.isSome = true ∨ after.rueckgabe.isSome = true ∨
    after.fortsetzungen.length < before.fortsetzungen.length ∨
    (after.fortsetzungen.length = before.fortsetzungen.length ∧
      (after.pc < first ∨ limit ≤ after.pc))

def Binnen (code : List Befehl) (budget : Nat) (start : Rahmen) (goal : Rahmen → Prop) : Prop :=
  ∃ n out, n ≤ budget ∧ Rahmen.LaufN code n start out ∧ goal out

/-- A test that takes a pass consumes exactly one permit. The zero-budget
    branch requests its named handler only after the final test is true. -/
theorem pass_fortschritt (frame : Rahmen) (leaveAt : Nat) (handler : Option Identifier)
    (remaining : Nat) (count : frame.zaehler frame.pc = some remaining) :
    (frame.pass false leaveAt handler).pc = frame.pc + leaveAt ∧
    (frame.pass false leaveAt handler).zaehler frame.pc = none ∧
    (remaining = 0 →
      (frame.pass true leaveAt handler).stopp = some (.ueberlauf handler)) ∧
    (∀ n, remaining = n + 1 → (frame.pass true leaveAt handler).pc = frame.pc + 1 ∧
      (frame.pass true leaveAt handler).zaehler frame.pc = some n) := by
  -- Mirror Befehl.vollzug_genau by inverting Rahmen.pass and the counter lookup.
  sorry

/-- A target is entered with the checked positional arguments and a fresh local
    frame. Caller's locals, temporaries and loop state live in its continuation. -/
theorem directCall_fortschritt (frame : Rahmen) (site : Rufstelle) (target : Funktion)
    (lookup : Funktion.finde frame.funktionen site.name = some target)
    (typecheck : site.passt frame.funktionen = true)
    (args : List (Option Dynamisch))
    (bind : frame.rufArgumente 0 site.args target.parameter = some args)
    (recursive : target.misstAbstieg = true ∨ ∀ saved ∈ frame.fortsetzungen,
      saved.funktion.map Subtype.val ≠ some site.name.val)
    (notSelf : target.misstAbstieg = true ∨ frame.funktion.map Subtype.val ≠ some site.name.val) :
    let next := frame.ruf site.name site.args site.bind
    next.pc = target.adresse ∧ next.fortsetzungen.length = frame.fortsetzungen.length + 1 ∧
      next.funktion = some site.name ∧ next.mass = none ∧
      next.lokale = args.reverse ++ frame.globale.drop (frame.globale.length - target.konstanten) := by
  -- Mirror expr_ergebnis_typ, using the typed call lookup and the argument packet.
  sorry

theorem directCall_rueckkehr (callee : Rahmen) (saved : Fortsetzung)
    (stack : List Fortsetzung) (same : callee.fortsetzungen = saved :: stack)
    (value : Option Dynamisch) :
    let caller := callee.rueckkehr value
    caller.pc = saved.pc ∧ caller.temp = saved.temp ∧ caller.zaehler = saved.zaehler ∧
      caller.obergrenzen = saved.obergrenzen ∧ caller.funktion = saved.funktion ∧
      caller.mass = saved.mass ∧ caller.fortsetzungen = stack ∧
      caller.lokale = match saved.eingang with
        | none => saved.lokale
        | some written => value.bind (wertIn written) :: saved.lokale := by
  -- Mirror Befehl.vollzug_genau at the restored continuation.
  sorry

/-- The nearest saved activation of the same function controls a recursive entry.
    A nonnegative entry measure is checked on every re-entry, with a strict decrease. -/
theorem function_decreases (frame : Rahmen) (name : Identifier) (slot : Nat) (value : Ganzzahl)
    (saved : Fortsetzung) (old : Nat) (current : frame.funktion = some name)
    (read : frame.zahl slot = some value)
    (prior : frame.fortsetzungen.find? (fun k => (k.funktion.map Subtype.val) == some name.val)
      = some saved) (oldMeasure : saved.mass = some old) :
    (0 ≤ value.zahl.wert ∧ value.zahl.wert.toNat < old →
      (frame.setzeMass slot).mass = some value.zahl.wert.toNat ∧
      (frame.setzeMass slot).pc = frame.pc + 1) ∧
    (¬ (0 ≤ value.zahl.wert ∧ value.zahl.wert.toNat < old) →
      (frame.setzeMass slot).stopp = some (.abstieg name)) := by
  -- Mirror pass_fortschritt using the strictly decreasing call-entry measure.
  sorry

theorem function_rekursionstiefe (mass : Nat → Nat) (depth : Nat)
    (decreases : ∀ i < depth, mass (i + 1) < mass i) :
    depth ≤ mass 0 := by
  -- Mirror pass_fortschritt by induction on the number of recursive entries.
  sorry

inductive Rufpfad (table : List Funktion) : Identifier → Identifier → Prop where
  | direkt : Funktion.finde table source = some function → call ∈ function.ruft →
      Rufpfad table source call.name
  | weiter : Funktion.finde table source = some function → call ∈ function.ruft →
      Rufpfad table call.name target → Rufpfad table source target

theorem function_rekursiv_korrekt (table : List Funktion) (function : Funktion)
    (unique : (table.map (fun f => f.name.val)).Nodup)
    (member : function ∈ table) :
    Funktion.rekursiv table function = true ↔ Rufpfad table function.name function.name := by
  -- Mirror function_rekursionstiefe on simple paths after removing repeated intermediate vertices.
  sorry

/-- A program with any syntactic recursive cycle containing a function with a
    missing measure is refused at launch before it selects an entry frame. -/
theorem program_unbounded_refused (frame : Rahmen) (entry : Identifier) (bad : Funktion)
    (unique : (frame.funktionen.map (fun f => f.name.val)).Nodup)
    (firstBad : frame.funktionen.find? (fun f =>
      !f.misstAbstieg && Funktion.rekursiv frame.funktionen f) = some bad) :
    (Befehl.starte entry |>.auswerten frame).stopp = some (.unbeschraenkteRekursion bad.name) := by
  -- Mirror function_decreases at program launch and use the first graph refusal.
  sorry

/-- One successful loop body segment either exits or reaches its back-edge on the
    same stack. Its budget includes all calls and nested loop instructions. -/
def SchleifenKoerper (code : List Befehl) (origin : Rahmen) (first limit body back budget : Nat) : Prop :=
  ∀ frame, (∃ n, Rahmen.LaufN code n origin frame) → frame.Aktiv →
    frame.pc = body → frame.fortsetzungen.length = origin.fortsetzungen.length →
    Binnen code budget frame (fun out =>
      SchleifenAusgang first limit origin out ∨
        out.Aktiv ∧ out.pc = back ∧ out.fortsetzungen.length = origin.fortsetzungen.length)

/-- One closed bound evaluation and setup, at most N+1 tests, and at most N
    bodies followed by a backward jump. A final true test requests the handler. -/
theorem boundedWhile_terminiert (a : Surface.BoundedWhileArgs scope result) (frame : Rahmen)
    (env : Umgebung scope) (initial : frame.pc = 0) (active : frame.Aktiv)
    (typed : frame.traegt env)
    (checked : frame.WaechterHalten ((boundedWhileForm scope result).fragment a).code)
    (bodyBudget : Nat)
    (body : let f := (boundedWhileForm scope result).fragment a
      let test := (boundedWhileForm scope result).position a
      SchleifenKoerper f.code frame 0 f.code.length (test + 1) (f.code.length - 1) bodyBudget)
    (condition : let f := (boundedWhileForm scope result).fragment a
      let test := (boundedWhileForm scope result).position a
      ∀ atTest, (∃ n, Rahmen.LaufN f.code n frame atTest) →
        atTest.pc = test → atTest.fortsetzungen.length = frame.fortsetzungen.length →
        atTest.Aktiv → ((atTest.temp 0).bind alsBoolean).isSome = true) :
    let f := (boundedWhileForm scope result).fragment a
    let N := (a.bound.wert env).wert.toNat
    let bound := (expr 0 a.bound).code.length + 1 +
      (N + 1) * ((expr 0 a.condition).code.length + 1) + N * (bodyBudget + 1)
    Binnen f.code bound frame (SchleifenAusgang 0 f.code.length frame) := by
  -- Mirror expr_ergebnis_typ for bound and tests, then induct using pass_fortschritt.
  sorry

/-- The for setup computes the exact half-open range size from both static values.
    The two endpoint computations are separate; evaluating the upper endpoint
    does not overwrite the lower endpoint's value. -/
theorem forRange_passzahl (frame : Rahmen) (lower upper : Ganzzahl) (index : Ty .value)
    (readLower : frame.zahl 0 = some lower) (readUpper : frame.zahl 1 = some upper)
    (initial : Dynamisch) (fits : wertIn index lower.pack = some initial)
    (nonempty : lower.zahl.wert < upper.zahl.wert) (skipEmpty : Nat) :
    let next := (Befehl.forAnfang 0 1 index skipEmpty false false).auswerten frame
    next.pc = frame.pc + 1 ∧
      next.zaehler next.pc = some (upper.zahl.wert - lower.zahl.wert).toNat ∧
      next.lokale = some initial :: frame.lokale ∧ next.obergrenzen next.pc = some upper := by
  -- Mirror pass_fortschritt and unfold the initialization transfer.
  sorry

theorem forRange_leer (frame : Rahmen) (lower upper : Ganzzahl) (index : Ty .value)
    (readLower : frame.zahl 0 = some lower) (readUpper : frame.zahl 1 = some upper)
    (empty : upper.zahl.wert ≤ lower.zahl.wert) (skipEmpty : Nat) (missingHandler : Bool) :
    let next := (Befehl.forAnfang 0 1 index skipEmpty false missingHandler).auswerten frame
    next.pc = frame.pc + skipEmpty ∧ next.lokale = frame.lokale ∧ next.stopp = frame.stopp := by
  -- Mirror forRange_passzahl on the empty-range branch.
  sorry

theorem forRange_terminiert (a : Surface.ForRangeArgs scope result) (frame : Rahmen)
    (env : Umgebung scope) (initial : frame.pc = 0) (active : frame.Aktiv)
    (typed : frame.traegt env)
    (checked : frame.WaechterHalten ((forRangeForm scope result).fragment a).code)
    (bodyBudget : Nat)
    (body : let f := (forRangeForm scope result).fragment a
      let test := (forRangeForm scope result).position a
      SchleifenKoerper f.code frame 0 f.code.length (test + 1) (f.code.length - 2) bodyBudget)
    (backEdge : let f := (forRangeForm scope result).fragment a
      ∀ back, (∃ n, Rahmen.LaufN f.code n frame back) →
        back.pc = f.code.length - 2 → back.fortsetzungen.length = frame.fortsetzungen.length →
        back.Aktiv → ∀ instruction, f.code[back.pc]? = some instruction →
        (instruction.auswerten back).Aktiv) :
    let f := (forRangeForm scope result).fragment a
    let N := ((a.upper.wert env).wert - (a.lower.wert env).wert).toNat
    let bound := (expr 0 a.lower).code.length + (expr 1 a.upper).code.length + 3 + N * (bodyBudget + 2)
    Binnen f.code bound frame (SchleifenAusgang 0 f.code.length frame) := by
  -- Mirror boundedWhile_terminiert using forRange_passzahl and the generated increment.
  sorry

/-- A finite table gives a total depth bound, even when recursive functions
    call each other. The saved activations are ordered from oldest to newest. -/
theorem function_stapeltiefe (names : List (List Char)) (upper : List Char → Nat)
    (frames : List (List Char × Nat))
    (declared : ∀ f ∈ frames, f.1 ∈ names ∧ f.2 ≤ upper f.1)
    (decreases : ∀ name ∈ names,
      ((frames.filter (fun f => f.1 == name)).map Prod.snd).Pairwise (fun old next => next < old)) :
    frames.length ≤ (names.map (fun name => upper name + 1)).sum := by
  -- Mirror function_rekursionstiefe on each function's subsequence and sum over the table.
  sorry

theorem program_eintritt (frame : Rahmen) (entry : Identifier) (target : Funktion)
    (unique : (frame.funktionen.map (fun f => f.name.val)).Nodup)
    (bounded : ∀ f ∈ frame.funktionen, Funktion.rekursiv frame.funktionen f = true → f.misstAbstieg = true)
    (resolved : ∀ call ∈ frame.funktionen.flatMap Funktion.ruft, call.passt frame.funktionen = true)
    (lookup : Funktion.finde frame.funktionen entry = some target)
    (parameters : target.parameter = []) (initial : frame.funktion = none ∧ frame.fortsetzungen = []) :
    let entered := (Befehl.starte entry).auswerten frame
    entered.pc = target.adresse ∧ entered.funktion = some entry ∧
      entered.lokale = frame.globale.drop (frame.globale.length - target.konstanten) ∧
      entered.fortsetzungen.length = 1 := by
  -- Mirror directCall_fortschritt after validating the table and selecting the ordinary entry.
  sorry

theorem constant_initialisiert (a : Surface.ConstantArgs scope) (env : Umgebung scope)
    (frame : Rahmen) (active : frame.Aktiv) (typed : frame.traegt env) (initial : frame.pc = 0)
    (checked : frame.WaechterHalten ((constantForm scope).fragment a).code) :
    let code := ((constantForm scope).fragment a).code
    ∃ value, wertIn a.written.type ⟨a.type, a.value.wert env⟩ = some value ∧
      Binnen code code.length frame (fun out =>
        out.pc = code.length ∧ out.lokale = some value :: frame.lokale ∧
          out.globale = some value :: frame.globale) := by
  -- Mirror expr_ergebnis_typ, then apply wertIn_widen before committing the immutable value.
  sorry

/-- Counted transitions are public step units even when they transfer control
    backwards or across a caller boundary. A bound of zero refers to private steps. -/
theorem program_stotterLaenge (p : Fragment) (platform : Plattform) (b : Befehl) :
    (p.einheit platform).stotterLaenge b = 0 := by
  -- Mirror Quellform.EinheitAussage and unfold Fragment.einheit.
  sorry

end Gabbro.Core.Ast.Semantik
