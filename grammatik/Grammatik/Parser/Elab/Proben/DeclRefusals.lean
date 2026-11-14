module

public import Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil1
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
public import Grammatik.Parser.Namen.Oeffentlich
public import Grammatik.Parser.Profil.Auswahl

@[expose] public section

namespace Gabbro.Grammatik.Parser.DeclRefusals

open Uebersetze Auswahl Oeffentlich

/-- A bodied function head over no parameters. -/
def fnKopf (art name : String) (fehler : Option String := none)
    (klauseln : List SKlausel := []) : FnSig :=
  { art, name, params := [], res := .none, fehler, klauseln }

/-- A bodied function with an empty body. -/
def leereFn (sig : FnSig) : SItemTief :=
  .fnT sig (.block [] .none)

/-- K011/K012: a declared `deadline` bound is refused, never silently dropped. -/
theorem deadline_refused_zeuge :
    uOhneKlauselForm [.limit "deadline <= 10 ops arch x86_64 falsifier s"] =
      .error "deadline not modelled: a declared time bound the language does not check" ∧
    uOhneKlauselForm [.cost (.lit 10)] = .ok () := by
  exact ⟨rfl, rfl⟩

/-- N210: arena bounds are compile-time constants with `0 <= lo <= hi`. -/
theorem arena_schranken_zeuge :
    uArenaSchranken [] [.arenaT "A" (.lit 0) (.lit 8) .none (.atom "u32") .none] = .ok () ∧
    uArenaSchranken [] [.arenaT "A" (.lit 5) (.lit 2) .none (.atom "u32") .none] =
      .error "arena bounds without 0 <= lo <= hi: A" ∧
    uArenaSchranken [] [.arenaT "A" (.variable "n") (.lit 8) .none (.atom "u32") .none] =
      .error "arena bounds without compile-time constants: A" := by
  exact ⟨rfl, rfl, rfl⟩

/-- N042: two bodied functions never share one name in a unit. -/
theorem fn_namen_eindeutig_zeuge :
    uFnNamenEindeutig [(fnKopf "impl" "f", .block [] .none)] = .ok () ∧
    uFnNamenEindeutig [(fnKopf "impl" "f", .block [] .none),
      (fnKopf "impl" "f", .block [] .none)] =
      .error "duplicate bodied function: two functions share one name" := by
  exact ⟨rfl, rfl⟩

/-- N025: a private `reason` used outside its module is refused; the same module
    and a `pub` reason stay admitted. -/
theorem grund_sichtbar_zeuge :
    grundSichtbar [.modT "a" [.whyT "R" [] false, leereFn (fnKopf "impl" "f" (.some "R"))]] =
      .ok () ∧
    grundSichtbar [.modT "a" [.pubT (.whyT "R" [] false)],
      .modT "b" [leereFn (fnKopf "impl" "g" (.some "R"))]] = .ok () ∧
    grundSichtbar [.modT "a" [.whyT "R" [] false],
      .modT "b" [leereFn (fnKopf "impl" "g" (.some "R"))]] =
      .error "private reason used outside its module: R" := by
  exact ⟨rfl, rfl, rfl⟩

/-- G003: an item named `TESTBUILD` is refused (reserved gate word). -/
theorem reserviert_refused_zeuge :
    reserviertL [leereFn (fnKopf "impl" "TESTBUILD")] = true ∧
    reserviertL [leereFn (fnKopf "impl" "f")] = false := by
  exact ⟨rfl, rfl⟩

/-- The elaboration context inside a `by consuming` walk over `node`. -/
def consumeCtx : UCtx :=
  { names := [], kinds := [], types := [], tabs := [], locks := [], held := [], res := .none,
    fname := "sample", alias := [], lits := [], loops := ["#consume:node"] }

/-- N580: `leave`/`next` naming the binder of a `by consuming` walk is refused;
    an ordinary loop ender still elaborates. -/
theorem consuming_ender_refused_zeuge :
    uEndeStmt consumeCtx (.some (.leave "node")) =
      .error "consuming traversal forbids leave" ∧
    uEndeStmt consumeCtx (.some (.next "node")) =
      .error "consuming traversal forbids next" ∧
    uEndeStmt { consumeCtx with loops := ["i"] } (.some (.leave "i")) =
      .ok [UStmt.leave "i"] := by
  exact ⟨rfl, rfl, rfl⟩

end Gabbro.Grammatik.Parser.DeclRefusals
