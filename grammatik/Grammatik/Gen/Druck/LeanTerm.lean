/-
  File:      Grammatik/Gen/Druck/LeanTerm.lean
  Subject:   A G term AS LEAN SOURCE, for the witness files of the cells (`Gen/Zeugen/`). The printer is NOT trusted:
             a witness file states what the kernel must check (`decide`), so a wrong print is a failed proof, never a
             wrong claim. Every proof argument is printed as `(by decide +revert)`; the index arguments are left to
             the elaborator, except where a constructor's result type does not determine them (`widen`, named).
             Forms without a clause are refused by name, like the source printer (`Druck.lean`).
-/
import Grammatik.Gen.Familie.Spez
import Grammatik.Kern.Syntax.Syntax
import Grammatik.Parser.Cover.Mitglieder

namespace Gabbro.Grammatik.Gen.LeanTerm

open Gabbro.Grammatik

/-- A proof argument: the kernel decides it. -/
def bew : String :=
  "(by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | " ++
    "exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)"

/-- An element of a finite type of the declaration, ascribed to its type in the witness file (`z` is the member there). -/
def fin (k : Nat) (art : String) : String := s!"(⟨{k}, by decide⟩ : Fin {art})"

/-- An integer literal. -/
def zahl (n : Int) : String := if n < 0 then s!"({n})" else toString n

variable {D : Deklaration}

/-- A variable. -/
def var : {Γ : Ctx} → {τ : Ty} → Var Γ τ → String
  | _, _, .here => ".here"
  | _, _, .there v => s!"(.there {var v})"

variable (tab : D.Tab → Nat) (glob : D.Glob → Nat) (fn : D.Fn → Nat) (lock : D.Lock → Nat) (ax : D.Ax → Nat)
  (feld : (t : D.Tab) → D.Feld t → Nat) (reg : D.Reg → Nat)

/-- An expression. -/
def expr {Γ : Ctx} {Λ : List (Res D)} : {τ : Ty} → Expr D Γ Λ τ → Except String String
  | _, .lit n => .ok s!"(.lit {zahl n})"
  | _, .tru => .ok ".tru"
  | _, .fls => .ok ".fls"
  | _, .var x => .ok s!"(.var {var x})"
  | _, .glob g _ => .ok s!"(Expr.glob (D := z.deklaration) {fin (glob g) "z.globs.length"} {bew})"
  | _, .slot t f i _ => do .ok s!"(.slot {fin (tab t) "z.tabs.length"} {fin (feld t f) s!"(z.tabs.get ⟨{tab t}, by decide⟩).felder.length"} {← expr i} {bew})"
  | _, .fnref f n _ => .ok s!"(.fnref {fin (fn f) "z.fns.length"} {n} {bew})"
  | .int lo' hi', .widen _ _ e => do .ok s!"(Expr.widen (lo' := {zahl lo'}) (hi' := {zahl hi'}) {bew} {bew} {← expr e})"
  | _, .add a b => do .ok s!"(.add {← expr a} {← expr b})"
  | _, .sub a b => do .ok s!"(.sub {← expr a} {← expr b})"
  | _, .mul a b => do .ok s!"(.mul {← expr a} {← expr b})"
  | _, .neg a => do .ok s!"(.neg {← expr a})"
  | _, .lt a b => do .ok s!"(.lt {← expr a} {← expr b})"
  | _, .le a b => do .ok s!"(.le {← expr a} {← expr b})"
  | _, .eq a b => do .ok s!"(.eq {← expr a} {← expr b})"
  | _, .and a b => do .ok s!"(.and {← expr a} {← expr b})"
  | _, .or a b => do .ok s!"(.or {← expr a} {← expr b})"
  | _, .not a => do .ok s!"(.not {← expr a})"
  | _, .why n r => .ok s!"(.why {n} {fin r.val "_"})"
  | _, .none n => .ok s!"(.none {zahl n})"
  | _, .some e => do .ok s!"(.some {← expr e})"
  | _, .istSome e => do .ok s!"(.istSome {← expr e})"
  | _, .forallSlots t body _ => do .ok s!"(.forallSlots {fin (tab t) "z.tabs.length"} {← expr body} {bew})"
  | _, .existsSlots t body _ => do .ok s!"(.existsSlots {fin (tab t) "z.tabs.length"} {← expr body} {bew})"
  | _, e => .error s!"Lean print: no clause for {(Parser.Cover.Mitglieder.eE e).headD "?"}"

/-- The arguments of a call. -/
def args {Γ : Ctx} {Λ : List (Res D)} : {τs : List Ty} → Args D Γ Λ τs → Except String String
  | _, .nil => .ok ".nil"
  | _, .cons e rest => do .ok s!"(.cons {← expr tab glob fn feld e} {← args rest})"

/-- The value of a `return`. -/
def erg {Γ : Ctx} {Λ : List (Res D)} : {o : Option Ty} → ErgExpr D Γ Λ o → Except String String
  | _, .empty => .ok ".empty"
  | _, .val e => do .ok s!"(.val {← expr tab glob fn feld e})"

mutual

/-- A statement. -/
def stmt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Except String String
  | .assignSlot t f i e _ _ => do
      .ok s!"(.assignSlot {fin (tab t) "z.tabs.length"} {fin (feld t f) s!"(z.tabs.get ⟨{tab t}, by decide⟩).felder.length"} {← expr tab glob fn feld i} {← expr tab glob fn feld e} {bew} {bew})"
  | .assignGlob g e _ _ => do .ok s!"(.assignGlob {fin (glob g) "z.globs.length"} {← expr tab glob fn feld e} {bew} {bew})"
  | .assignVar x e => do .ok s!"(.assignVar {var x} {← expr tab glob fn feld e})"
  | .publish g e _ _ _ _ => do .ok s!"(.publish {fin (glob g) "z.globs.length"} {← expr tab glob fn feld e} _ rfl {bew} {bew})"
  | .ite c t e => do .ok s!"(.ite {← expr tab glob fn feld c} {← block t} {← block e})"
  | .call g a _ _ => do .ok s!"(.call {fin (fn g) "z.fns.length"} {← args tab glob fn feld a} {bew} {bew})"
  | .locks L _ body => do .ok s!"(.locks {fin (lock L) "z.locks.length"} {bew} {← block body})"
  | .regWrite r _ e => do .ok s!"(.regWrite {fin (reg r) "z.regs.length"} {bew} {← expr tab glob fn feld e})"
  | .callInd p a _ _ => do .ok s!"(.callInd {← expr tab glob fn feld p} {← args tab glob fn feld a} {bew} {bew})"
  | .traverse t inv body => do
      .ok s!"(.traverse {fin (tab t) "z.tabs.length"} {← expr tab glob fn feld inv} {← block body})"
  | .axiomCall a xs _ _ _ _ _ => do .ok s!"(.axiomCall {fin (ax a) "z.axs.length"} {← args tab glob fn feld xs} {bew} {bew} {bew} {bew} {bew})"
  | .ret e _ => do .ok s!"(.ret {← erg tab glob fn feld e} {bew})"
  | .retWhy r _ => .ok s!"(.retWhy {fin r.val "_"} {bew})"
  | s => .error s!"Lean print: no clause for {(Parser.Cover.Mitglieder.cS s).headD "?"}"

/-- A block. -/
def block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Except String String
  | .nil => .ok ".nil"
  | .cons s rest => do .ok s!"(.cons {← stmt s} {← block rest})"
  | .bind e rest => do .ok s!"(.bind {← expr tab glob fn feld e} {← block rest})"
  | .bindCall g a _ _ _ rest => do
      .ok s!"(.bindCall {fin (fn g) "z.fns.length"} {← args tab glob fn feld a} {bew} {bew} {bew} {← block rest})"
  | .bindCallElse g a _ _ _ err rest => do
      .ok s!"(.bindCallElse {fin (fn g) "z.fns.length"} {← args tab glob fn feld a} {bew} {bew} {bew} {← endblock err} {← block rest})"
  | .bindAxiom a xs _ _ _ _ _ rest => do
      .ok s!"(.bindAxiom {fin (ax a) "z.axs.length"} {← args tab glob fn feld xs} {bew} {bew} {bew} {bew} {bew} {← block rest})"
  | .regRead r _ rest => do .ok s!"(.regRead {fin (reg r) "z.regs.length"} {bew} {← block rest})"
  | .regReadElse r _ zu sonst rest => do
      .ok s!"(.regReadElse {fin (reg r) "z.regs.length"} {bew} {← expr tab glob fn feld zu} {← endblock sonst} {← block rest})"
  | .bindCallInd p a _ _ _ rest => do
      .ok s!"(.bindCallInd {← expr tab glob fn feld p} {← args tab glob fn feld a} {bew} {bew} {bew} {← block rest})"
  | .awaits g _ _ _ rest => do .ok s!"(.awaits {fin (glob g) "z.globs.length"} _ rfl {bew} {← block rest})"
  | b => .error s!"Lean print: no clause for {(Parser.Cover.Mitglieder.cB b).headD "?"}"

/-- An end block. -/
def endblock {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Except String String
  | .ret e _ => do .ok s!"(.ret {← erg tab glob fn feld e} {bew})"
  | .retWhy r _ => .ok s!"(.retWhy {fin r.val "_"} {bew})"
  | .cons s rest => do .ok s!"(.cons {← stmt s} {← endblock rest})"
  | .bind e rest => do .ok s!"(.bind {← expr tab glob fn feld e} {← endblock rest})"
  | .bindCall g a _ _ _ rest => do
      .ok s!"(.bindCall {fin (fn g) "z.fns.length"} {← args tab glob fn feld a} {bew} {bew} {bew} {← endblock rest})"
  | .bindCallElse g a _ _ _ err rest => do
      .ok s!"(.bindCallElse {fin (fn g) "z.fns.length"} {← args tab glob fn feld a} {bew} {bew} {bew} {← endblock err} {← endblock rest})"
  | .bindAxiom a xs _ _ _ _ _ rest => do
      .ok s!"(.bindAxiom {fin (ax a) "z.axs.length"} {← args tab glob fn feld xs} {bew} {bew} {bew} {bew} {bew} {← endblock rest})"
  | .bindAxiomElse a xs _ _ _ _ _ _ err rest => do
      .ok s!"(.bindAxiomElse {fin (ax a) "z.axs.length"} {← args tab glob fn feld xs} {bew} {bew} {bew} {bew} {bew} {bew} {← endblock err} {← endblock rest})"
  | .regRead r _ rest => do .ok s!"(.regRead {fin (reg r) "z.regs.length"} {bew} {← endblock rest})"
  | .regReadElse r _ zu sonst rest => do
      .ok s!"(.regReadElse {fin (reg r) "z.regs.length"} {bew} {← expr tab glob fn feld zu} {← endblock sonst} {← endblock rest})"
  | .bindCallInd p a _ _ _ rest => do
      .ok s!"(.bindCallInd {← expr tab glob fn feld p} {← args tab glob fn feld a} {bew} {bew} {bew} {← endblock rest})"
  | .awaits g _ _ _ rest => do .ok s!"(.awaits {fin (glob g) "z.globs.length"} _ rfl {bew} {← endblock rest})"
  | e => .error s!"Lean print: no clause for {(Parser.Cover.Mitglieder.cE e).headD "?"}"

end

end Gabbro.Grammatik.Gen.LeanTerm
