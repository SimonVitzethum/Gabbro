/-
  File:      Grammatik/Gen/Druck/Druck.lean
  Subject:   THE PRINTER of a generated program: the bodies of the model (`Expr`, `Stmt`, `Block`, `Endblock`) as Gabbro
             source text. This is the missing step between the generator (which emits typed G terms) and the tools
             that read text (the Rust checker and the compiler).

  It is PARTIAL on purpose. A form it has no clause for is reported by its register name (`Expr.slot`, `Stmt.call`, ... as
  `Parser/Cover/Mitglieder.lean` names them) and the program is skipped, never printed wrongly: a printer that guesses is
  worse than one that refuses. A new constructor of the model therefore costs coverage, not the build, and the driver
  prints which forms were skipped how often (`gen-zellen`), so a gap is a number that can be closed one form at a time.

  The printer is UNTRUSTED. What it prints is checked from two sides outside it: the Lean pipeline on text
  (`uebersetzeAllg`, where the form is in the fragment of Track P) and the Rust checker, whose disagreements with the
  model's verdict are triaged as printer errors or checker errors. No Rust checker is an oracle here.

  Names: tables `T<i>`, their fields `f<j>`, statics and atomics `g<i>`, locks `L<i>`, functions `fn<i>`, foreign bodies
  `ax<i>`, local variables `v<k>` (`k` the depth at which they are bound). Every operator is parenthesised.
-/
import Grammatik.Kern.Syntax.Syntax
import Grammatik.Parser.Cover.Mitglieder

namespace Gabbro.Grammatik.Gen.Druck

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Cover.Mitglieder

/-- The names the printer gives to the entities of a declaration. -/
structure Namen (D : Deklaration) where
  tab : D.Tab → String
  feld : (t : D.Tab) → D.Feld t → String
  glob : D.Glob → String
  lock : D.Lock → String
  fn : D.Fn → String
  ax : D.Ax → String

/-- The depth of a variable: `here` is 0. -/
def varTiefe : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there v => varTiefe v + 1

/-- A literal. -/
def zahl (n : Int) : String := if n < 0 then s!"({n})" else toString n

variable {D : Deklaration}

/-- The skipped form, by its register name. -/
def nichtDruckbar (was : String) (namen : List String) : Except String String :=
  .error s!"unsupported {was}: {namen.headD "?"}"

/-- An expression as source text. -/
def druckE (nm : Namen D) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Except String String
  | .lit n => .ok (zahl n)
  | .tru => .ok "true"
  | .fls => .ok "false"
  | .var x => .ok s!"v{Γ.length - 1 - varTiefe x}"
  | .glob g _ => .ok (nm.glob g)
  | .slot t f i _ => do
      let i' ← druckE nm i
      .ok s!"{nm.tab t}.slots[{i'}].{nm.feld t f}"
  | .fnref f _ _ => .ok s!"&{nm.fn f}"
  | .widen _ _ e => druckE nm e
  | .add a b => do .ok s!"({← druckE nm a} + {← druckE nm b})"
  | .sub a b => do .ok s!"({← druckE nm a} - {← druckE nm b})"
  | .mul a b => do .ok s!"({← druckE nm a} * {← druckE nm b})"
  | .neg a => do .ok s!"(-{← druckE nm a})"
  | .lt a b => do .ok s!"({← druckE nm a} < {← druckE nm b})"
  | .le a b => do .ok s!"({← druckE nm a} <= {← druckE nm b})"
  | .eq a b => do .ok s!"({← druckE nm a} == {← druckE nm b})"
  | .and a b => do .ok s!"({← druckE nm a} && {← druckE nm b})"
  | .or a b => do .ok s!"({← druckE nm a} || {← druckE nm b})"
  | .not a => do .ok s!"(!{← druckE nm a})"
  | e => nichtDruckbar "expression" (eE e)

/-- The arguments of a call. -/
def druckA (nm : Namen D) {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} : Args D Γ Λ τs → Except String (List String)
  | .nil => .ok []
  | .cons e rest => do
      let x ← druckE nm e
      let r ← druckA nm rest
      .ok (x :: r)

/-- The result of a `return`. -/
def druckR (nm : Namen D) {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} : ErgExpr D Γ Λ o → Except String String
  | .empty => .ok "return;"
  | .val e => do .ok s!"return {← druckE nm e};"

/-- A comma list. -/
def liste (xs : List String) : String := String.intercalate ", " xs

variable (V : Vertrag D)

mutual

/-- A statement as source text, one line per simple statement, each starting with `ein`. -/
def druckS (nm : Namen D) (ein : String) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Except String String
  | .assignSlot t f i e _ _ => do
      .ok s!"{ein}{nm.tab t}.slots[{← druckE nm i}].{nm.feld t f} = {← druckE nm e};\n"
  | .assignGlob g e _ _ => do .ok s!"{ein}{nm.glob g} = {← druckE nm e};\n"
  | .publish g e payload _ _ _ => do
      let ns := payload.map nm.glob
      .ok s!"{ein}{nm.glob g} = {← druckE nm e} publishes {if ns.isEmpty then "nothing" else "{ " ++ liste ns ++ " }"};\n"
  | .ite c t e => do
      let c' ← druckE nm c
      let t' ← druckB nm (ein ++ "    ") t
      let e' ← druckB nm (ein ++ "    ") e
      .ok s!"{ein}if {c'} \{\n{t'}{ein}} else \{\n{e'}{ein}}\n"
  | .call f args _ _ => do .ok s!"{ein}{nm.fn f}({liste (← druckA nm args)});\n"
  | .locks L _ body => do
      .ok s!"{ein}locks {nm.lock L} \{\n{← druckB nm (ein ++ "    ") body}{ein}}\n"
  | .axiomCall a args _ _ _ _ _ => do .ok s!"{ein}{nm.ax a}({liste (← druckA nm args)});\n"
  | .ret e _ => do .ok s!"{ein}{← druckR nm e}\n"
  | s => (nichtDruckbar "statement" (cS s)).map id

/-- A block as source text. -/
def druckB (nm : Namen D) (ein : String) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Except String String
  | .nil => .ok ""
  | .cons s rest => do .ok ((← druckS nm ein s) ++ (← druckB nm ein rest))
  | .bind e rest => do
      .ok (s!"{ein}let v{Γ.length} = {← druckE nm e};\n" ++ (← druckB nm ein rest))
  | .bindCall f args _ _ _ rest => do
      .ok (s!"{ein}let v{Γ.length} = {nm.fn f}({liste (← druckA nm args)});\n" ++ (← druckB nm ein rest))
  | .bindAxiom a args _ _ _ _ _ rest => do
      .ok (s!"{ein}let v{Γ.length} = {nm.ax a}({liste (← druckA nm args)});\n" ++ (← druckB nm ein rest))
  | b => (nichtDruckbar "block" (cB b)).map id

/-- A block that does not fall off, as source text. -/
def druckEnd (nm : Namen D) (ein : String) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Except String String
  | .ret e _ => do .ok s!"{ein}{← druckR nm e}\n"
  | .cons s rest => do .ok ((← druckS nm ein s) ++ (← druckEnd nm ein rest))
  | .bind e rest => do
      .ok (s!"{ein}let v{Γ.length} = {← druckE nm e};\n" ++ (← druckEnd nm ein rest))
  | .bindCall f args _ _ _ rest => do
      .ok (s!"{ein}let v{Γ.length} = {nm.fn f}({liste (← druckA nm args)});\n" ++ (← druckEnd nm ein rest))
  | .bindAxiom a args _ _ _ _ _ rest => do
      .ok (s!"{ein}let v{Γ.length} = {nm.ax a}({liste (← druckA nm args)});\n" ++ (← druckEnd nm ein rest))
  | e => (nichtDruckbar "end block" (cE e)).map id

end

end Gabbro.Grammatik.Gen.Druck
