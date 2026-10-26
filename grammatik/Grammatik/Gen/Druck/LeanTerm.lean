/-
  File:      Grammatik/Gen/Druck/LeanTerm.lean
  Subject:   A G term AS LEAN SOURCE, for the witness files of the cells (`Gen/Zeugen/`). The printer is NOT trusted:
             a witness file states what the kernel must check (`decide`), so a wrong print is a failed proof, never a
             wrong claim. Every proof argument is printed as `(by decide +revert)`; the index arguments are left to
             the elaborator, except where a constructor's result type does not determine them (`widen`, named).
             Every constructor of every term family has its clause (the clauses follow the explicit arguments of the
             constructors of `Kern/Syntax/Syntax.lean`, read off the model).
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

/-- A pair of integers (a float bound). -/
def paar (p : Int × Int) : String := s!"({zahl p.1}, {zahl p.2})"

/-- A float operator. -/
def gleit : GleitOp → String
  | .add => ".add"
  | .sub => ".sub"
  | .mul => ".mul"
  | .div => ".div"

/-- The cases of a tagged type. -/
def faelle (cs : List (Option (Int × Int))) : String :=
  "[" ++ String.intercalate ", " (cs.map fun | none => "none" | some p => s!"some {paar p}") ++ "]"

/-- The numbers of the elements of the finite types of a declaration, as the witness file names them. -/
structure Namen (D : Deklaration) where
  tab : D.Tab → Nat
  glob : D.Glob → Nat
  fn : D.Fn → Nat
  lock : D.Lock → Nat
  ax : D.Ax → Nat
  feld : (t : D.Tab) → D.Feld t → Nat
  reg : D.Reg → Nat
  marke : D.Marke → Nat
  inv : D.Inv → Nat
  annahme : D.Annahme → Nat

mutual
/-- An expression. -/
def drE (N : Namen D) {Γ : Ctx} {Λ : List (Res D)} : {τ : Ty} → Expr D Γ Λ τ → Except String String
  | _, .lit n => .ok s!"(Expr.lit (D := z.deklaration) {zahl n})"
  | _, .tru => .ok s!"(Expr.tru (D := z.deklaration))"
  | _, .fls => .ok s!"(Expr.fls (D := z.deklaration))"
  | _, .var x => .ok s!"(Expr.var (D := z.deklaration) {var x})"
  | _, .glob g _ => .ok s!"(Expr.glob (D := z.deklaration) {fin (N.glob g) "z.globs.length"} {bew})"
  | _, .slot t f i _ => do .ok s!"(Expr.slot (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {← drE N i} {bew})"
  | _, .thru p t _ f i _ => do .ok s!"(Expr.thru (D := z.deklaration) {← drE N p} {fin (N.tab t) "z.tabs.length"} {bew} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {← drE N i} {bew})"
  | _, .ptrOf t n _ rw => .ok s!"(Expr.ptrOf (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {n} {bew} {rw})"
  | _, .refEq a b => do .ok s!"(Expr.refEq (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .slotRef r t _ _ f _ => do .ok s!"(Expr.slotRef (D := z.deklaration) {← drE N r} {fin (N.tab t) "z.tabs.length"} {bew} {bew} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {bew})"
  | _, .fnref f n _ => .ok s!"(Expr.fnref (D := z.deklaration) {fin (N.fn f) "z.fns.length"} {n} {bew})"
  | _, .oldG g _ => .ok s!"(Expr.oldG (D := z.deklaration) {fin (N.glob g) "z.globs.length"} {bew})"
  | _, .oldS t f i _ => do .ok s!"(Expr.oldS (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {← drE N i} {bew})"
  | .int lo' hi', .widen _ _ e => do .ok s!"(Expr.widen (D := z.deklaration) (lo' := {zahl lo'}) (hi' := {zahl hi'}) {bew} {bew} {← drE N e})"
  | _, .add a b => do .ok s!"(Expr.add (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .sub a b => do .ok s!"(Expr.sub (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .neg a => do .ok s!"(Expr.neg (D := z.deklaration) {← drE N a})"
  | _, .mul a b => do .ok s!"(Expr.mul (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .div _ _ a b => do .ok s!"(Expr.div (D := z.deklaration) {bew} {bew} {← drE N a} {← drE N b})"
  | _, .rem _ _ a b => do .ok s!"(Expr.rem (D := z.deklaration) {bew} {bew} {← drE N a} {← drE N b})"
  | _, .sdiv _ a b => do .ok s!"(Expr.sdiv (D := z.deklaration) {bew} {← drE N a} {← drE N b})"
  | _, .srem _ a b => do .ok s!"(Expr.srem (D := z.deklaration) {bew} {← drE N a} {← drE N b})"
  | _, .getBytes t f _ n i _ _ _ => do .ok s!"(Expr.getBytes (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {bew} {n} {← drE N i} {bew} {bew} {bew})"
  | _, .band _ _ a b => do .ok s!"(Expr.band (D := z.deklaration) {bew} {bew} {← drE N a} {← drE N b})"
  | _, .bor w _ _ _ _ a b => do .ok s!"(Expr.bor (D := z.deklaration) {w} {bew} {bew} {bew} {bew} {← drE N a} {← drE N b})"
  | _, .bxor w _ _ _ _ a b => do .ok s!"(Expr.bxor (D := z.deklaration) {w} {bew} {bew} {bew} {bew} {← drE N a} {← drE N b})"
  | _, .shl w _ _ _ _ a b => do .ok s!"(Expr.shl (D := z.deklaration) {w} {bew} {bew} {bew} {bew} {← drE N a} {← drE N b})"
  | _, .shr w _ _ _ _ a b => do .ok s!"(Expr.shr (D := z.deklaration) {w} {bew} {bew} {bew} {bew} {← drE N a} {← drE N b})"
  | _, .lt a b => do .ok s!"(Expr.lt (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .le a b => do .ok s!"(Expr.le (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .eq a b => do .ok s!"(Expr.eq (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .fllt a b => do .ok s!"(Expr.fllt (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .flle a b => do .ok s!"(Expr.flle (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .and a b => do .ok s!"(Expr.and (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .or a b => do .ok s!"(Expr.or (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .not a => do .ok s!"(Expr.not (D := z.deklaration) {← drE N a})"
  | _, .none n => .ok s!"(Expr.none (D := z.deklaration) {zahl n})"
  | _, .some e => do .ok s!"(Expr.some (D := z.deklaration) {← drE N e})"
  | _, .istSome e => do .ok s!"(Expr.istSome (D := z.deklaration) {← drE N e})"
  | _, .case cs i nutz => do .ok s!"(Expr.case (D := z.deklaration) {faelle cs} {fin i.val "_"} {← drN N nutz})"
  | _, .why n r => .ok s!"(Expr.why (D := z.deklaration) {n} {fin r.val "_"})"
  | _, .forallSlots t body _ => do .ok s!"(Expr.forallSlots (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {← drE N body} {bew})"
  | _, .existsSlots t body _ => do .ok s!"(Expr.existsSlots (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {← drE N body} {bew})"
  | _, .reaches t f _ a b _ => do .ok s!"(Expr.reaches (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {bew} {← drE N a} {← drE N b} {bew})"
  | _, .arrNil => .ok "(Expr.arrNil (D := z.deklaration))"
  | _, .arrCons a b => do .ok s!"(Expr.arrCons (D := z.deklaration) {← drE N a} {← drE N b})"
  | _, .arrGet a i => do .ok s!"(Expr.arrGet (D := z.deklaration) {← drE N a} {← drE N i})"
  | _, .arrSet a i v => do .ok s!"(Expr.arrSet (D := z.deklaration) {← drE N a} {← drE N i} {← drE N v})"
  | _, .strLit bs _ =>
      .ok s!"(Expr.strLit (D := z.deklaration) [{", ".intercalate (bs.map fun b => s!"⟨{b.n}, by decide, by decide⟩")}] (by decide))"
  | _, .strLen e => do .ok s!"(Expr.strLen (D := z.deklaration) {← drE N e})"
  | _, .strCat e e' => do .ok s!"(Expr.strCat (D := z.deklaration) {← drE N e} {← drE N e'})"
  | _, .strGet e e' => do .ok s!"(Expr.strGet (D := z.deklaration) {← drE N e} {← drE N e'})"
  | _, .strEq e e' => do .ok s!"(Expr.strEq (D := z.deklaration) {← drE N e} {← drE N e'})"
  | _, .strLt e e' => do .ok s!"(Expr.strLt (D := z.deklaration) {← drE N e} {← drE N e'})"
  | _, .strWeit m e => do .ok s!"(Expr.strWeit (D := z.deklaration) {m} {← drE N e})"
  | _, .wenn c a b => do .ok s!"(Expr.wenn (D := z.deklaration) {← drE N c} {← drE N a} {← drE N b})"
  | _, .eng e lo hi s => do .ok s!"(Expr.eng (D := z.deklaration) {← drE N e} {zahl lo} {zahl hi} {← drE N s})"

/-- A payload expression. -/
def drN (N : Namen D) {Γ : Ctx} {Λ : List (Res D)} : {o : Option (Int × Int)} → NutzlastExpr D Γ Λ o → Except String String
  | _, .empty => .ok s!"(NutzlastExpr.empty (D := z.deklaration))"
  | _, .num e => do .ok s!"(NutzlastExpr.num (D := z.deklaration) {← drE N e})"

/-- The arguments of a call. -/
def drA (N : Namen D) {Γ : Ctx} {Λ : List (Res D)} : {τs : List Ty} → Args D Γ Λ τs → Except String String
  | _, .nil => .ok s!"(Args.nil (D := z.deklaration))"
  | _, .cons e rest => do .ok s!"(Args.cons (D := z.deklaration) {← drE N e} {← drA N rest})"

/-- The value of a `return`. -/
def drR (N : Namen D) {Γ : Ctx} {Λ : List (Res D)} : {o : Option Ty} → ErgExpr D Γ Λ o → Except String String
  | _, .empty => .ok s!"(ErgExpr.empty (D := z.deklaration))"
  | _, .val e => do .ok s!"(ErgExpr.val (D := z.deklaration) {← drE N e})"

/-- A statement. -/
def drS (N : Namen D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Except String String
  | .assignSlot t f i e _ _ => do .ok s!"(Stmt.assignSlot (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {← drE N i} {← drE N e} {bew} {bew})"
  | .assignThru p t _ f i e _ _ => do .ok s!"(Stmt.assignThru (D := z.deklaration) {← drE N p} {fin (N.tab t) "z.tabs.length"} {bew} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {← drE N i} {← drE N e} {bew} {bew})"
  | .assignSlotRef r t _ _ f e _ _ => do .ok s!"(Stmt.assignSlotRef (D := z.deklaration) {← drE N r} {fin (N.tab t) "z.tabs.length"} {bew} {bew} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {← drE N e} {bew} {bew})"
  | .assignGlob g e _ _ => do .ok s!"(Stmt.assignGlob (D := z.deklaration) {fin (N.glob g) "z.globs.length"} {← drE N e} {bew} {bew})"
  | .putBytes t f _ n i _ _ e _ _ => do .ok s!"(Stmt.putBytes (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {bew} {n} {← drE N i} {bew} {bew} {← drE N e} {bew} {bew})"
  | .assignVar x e => do .ok s!"(Stmt.assignVar (D := z.deklaration) {var x} {← drE N e})"
  | .shift t f _ i von nach _ _ _ _ => do .ok s!"(Stmt.shift (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {fin (N.feld t f) s!"(z.tabs.get ⟨{N.tab t}, by decide⟩).felder.length"} {bew} {← drE N i} {zahl von} {zahl nach} {bew} {bew} {bew} {bew})"
  | .ite c t e => do .ok s!"(Stmt.ite (D := z.deklaration) {← drE N c} {← drB N t} {← drB N e})"
  | .onOption o p a => do .ok s!"(Stmt.onOption (D := z.deklaration) {← drE N o} {← drB N p} {← drB N a})"
  | .onTag v arms => do .ok s!"(Stmt.onTag (D := z.deklaration) {← drE N v} {← drArms N arms})"
  | .onWhy r arms => do .ok s!"(Stmt.onWhy (D := z.deklaration) {← drE N r} {← drGArms N arms})"
  | .call f args _ _ => do .ok s!"(Stmt.call (D := z.deklaration) {fin (N.fn f) "z.fns.length"} {← drA N args} {bew} {bew})"
  | .callInd p args _ _ => do .ok s!"(Stmt.callInd (D := z.deklaration) {← drE N p} {← drA N args} {bew} {bew})"
  | .locks L _ body => do .ok s!"(Stmt.locks (D := z.deklaration) {fin (N.lock L) "z.locks.length"} {bew} {← drB N body})"
  | .breaking i body => do .ok s!"(Stmt.breaking (D := z.deklaration) {fin (N.inv i) "z.invs.length"} {← drB N body})"
  | .traverse t inv body => do .ok s!"(Stmt.traverse (D := z.deklaration) {fin (N.tab t) "z.tabs.length"} {← drE N inv} {← drB N body})"
  | .retry n bis body ueberlauf => do .ok s!"(Stmt.retry (D := z.deklaration) {n} {← drE N bis} {← drB N body} {← drB N ueberlauf})"
  | .forever a inv body => do .ok s!"(Stmt.forever (D := z.deklaration) {fin (N.annahme a) "(z.annahmen + 1)"} {← drE N inv} {← drB N body})"
  | .axiomCall a args _ _ _ _ _ => do .ok s!"(Stmt.axiomCall (D := z.deklaration) {fin (N.ax a) "z.axs.length"} {← drA N args} {bew} {bew} {bew} {bew} {bew})"
  | .regWrite r _ e => do .ok s!"(Stmt.regWrite (D := z.deklaration) {fin (N.reg r) "z.regs.length"} {bew} {← drE N e})"
  | .transition r _ m _ _ maske bits => .ok s!"(Stmt.transition (D := z.deklaration) {fin (N.reg r) "z.regs.length"} {bew} {fin (N.reg m) "z.regs.length"} {bew} {bew} {zahl maske} {zahl bits})"
  | .publish g e _ _ _ _ => do .ok s!"(Stmt.publish (D := z.deklaration) {fin (N.glob g) "z.globs.length"} {← drE N e} _ rfl {bew} {bew})"
  | .advances m a _ _ => .ok s!"(Stmt.advances (D := z.deklaration) {fin (N.marke m) "z.marken.length"} {a} {bew} {bew})"
  | .retires m s _ a => .ok s!"(Stmt.retires (D := z.deklaration) {fin (N.marke m) "z.marken.length"} {s} {bew} {fin (N.annahme a) "(z.annahmen + 1)"})"
  | .ret e _ => do .ok s!"(Stmt.ret (D := z.deklaration) {← drR N e} {bew})"
  | .retWhy r _ => .ok s!"(Stmt.retWhy (D := z.deklaration) {fin r.val "_"} {bew})"
  | .leave _ => .ok s!"(Stmt.leave (D := z.deklaration) {bew})"
  | .next _ => .ok s!"(Stmt.next (D := z.deklaration) {bew})"

/-- A block. -/
def drB (N : Namen D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Except String String
  | .nil => .ok s!"(Block.nil (D := z.deklaration))"
  | .cons s rest => do .ok s!"(Block.cons (D := z.deklaration) {← drS N s} {← drB N rest})"
  | .bind e rest => do .ok s!"(Block.bind (D := z.deklaration) {← drE N e} {← drB N rest})"
  | .bindCall f args _ _ _ rest => do .ok s!"(Block.bindCall (D := z.deklaration) {fin (N.fn f) "z.fns.length"} {← drA N args} {bew} {bew} {bew} {← drB N rest})"
  | .bindCallInd p args _ _ _ rest => do .ok s!"(Block.bindCallInd (D := z.deklaration) {← drE N p} {← drA N args} {bew} {bew} {bew} {← drB N rest})"
  | .bindCallElse f args _ _ _ err rest => do .ok s!"(Block.bindCallElse (D := z.deklaration) {fin (N.fn f) "z.fns.length"} {← drA N args} {bew} {bew} {bew} {← drEnd N err} {← drB N rest})"
  | .bindAxiom a args _ _ _ _ _ rest => do .ok s!"(Block.bindAxiom (D := z.deklaration) {fin (N.ax a) "z.axs.length"} {← drA N args} {bew} {bew} {bew} {bew} {bew} {← drB N rest})"
  | .bindAxiomElse a args _ _ _ _ _ _ err rest => do .ok s!"(Block.bindAxiomElse (D := z.deklaration) {fin (N.ax a) "z.axs.length"} {← drA N args} {bew} {bew} {bew} {bew} {bew} {bew} {← drEnd N err} {← drB N rest})"
  | .regRead r _ rest => do .ok s!"(Block.regRead (D := z.deklaration) {fin (N.reg r) "z.regs.length"} {bew} {← drB N rest})"
  | .regReadElse r _ zusage sonst rest => do .ok s!"(Block.regReadElse (D := z.deklaration) {fin (N.reg r) "z.regs.length"} {bew} {← drE N zusage} {← drEnd N sonst} {← drB N rest})"
  | .awaits g _ _ _ _ rest => do .ok s!"(Block.awaits (D := z.deklaration) {fin (N.glob g) "z.globs.length"} _ rfl {bew} {bew} {← drB N rest})"
  | .exchange g neu _ _ rest => do .ok s!"(Block.exchange (D := z.deklaration) {fin (N.glob g) "z.globs.length"} {← drE N neu} {bew} {bew} {← drB N rest})"
  | .narrow e lo' hi' sonst rest => do .ok s!"(Block.narrow (D := z.deklaration) {← drE N e} {zahl lo'} {zahl hi'} {← drEnd N sonst} {← drB N rest})"
  | .check c sonst rest => do .ok s!"(Block.check (D := z.deklaration) {← drE N c} {← drEnd N sonst} {← drB N rest})"
  | .float op a b lo hi rest => do .ok s!"(Block.float (D := z.deklaration) {gleit op} {← drE N a} {← drE N b} {paar lo} {paar hi} {← drB N rest})"
  | .floatLit q lo hi rest => do .ok s!"(Block.floatLit (D := z.deklaration) {paar q} {paar lo} {paar hi} {← drB N rest})"
  | .floatOf e lo hi rest => do .ok s!"(Block.floatOf (D := z.deklaration) {← drE N e} {paar lo} {paar hi} {← drB N rest})"
  | .floatNarrow e lo hi sonst rest => do .ok s!"(Block.floatNarrow (D := z.deklaration) {← drE N e} {paar lo} {paar hi} {← drEnd N sonst} {← drB N rest})"

/-- An end block. -/
def drEnd (N : Namen D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Except String String
  | .ret e _ => do .ok s!"(Endblock.ret (D := z.deklaration) {← drR N e} {bew})"
  | .retWhy r _ => .ok s!"(Endblock.retWhy (D := z.deklaration) {fin r.val "_"} {bew})"
  | .leave _ => .ok s!"(Endblock.leave (D := z.deklaration) {bew})"
  | .next _ => .ok s!"(Endblock.next (D := z.deklaration) {bew})"
  | .cons s rest => do .ok s!"(Endblock.cons (D := z.deklaration) {← drS N s} {← drEnd N rest})"
  | .bind e rest => do .ok s!"(Endblock.bind (D := z.deklaration) {← drE N e} {← drEnd N rest})"
  | .bindCall f args _ _ _ rest => do .ok s!"(Endblock.bindCall (D := z.deklaration) {fin (N.fn f) "z.fns.length"} {← drA N args} {bew} {bew} {bew} {← drEnd N rest})"
  | .bindCallElse f args _ _ _ err rest => do .ok s!"(Endblock.bindCallElse (D := z.deklaration) {fin (N.fn f) "z.fns.length"} {← drA N args} {bew} {bew} {bew} {← drEnd N err} {← drEnd N rest})"
  | .bindAxiom a args _ _ _ _ _ rest => do .ok s!"(Endblock.bindAxiom (D := z.deklaration) {fin (N.ax a) "z.axs.length"} {← drA N args} {bew} {bew} {bew} {bew} {bew} {← drEnd N rest})"
  | .bindAxiomElse a args _ _ _ _ _ _ err rest => do .ok s!"(Endblock.bindAxiomElse (D := z.deklaration) {fin (N.ax a) "z.axs.length"} {← drA N args} {bew} {bew} {bew} {bew} {bew} {bew} {← drEnd N err} {← drEnd N rest})"
  | .regRead r _ rest => do .ok s!"(Endblock.regRead (D := z.deklaration) {fin (N.reg r) "z.regs.length"} {bew} {← drEnd N rest})"
  | .regReadElse r _ zusage sonst rest => do .ok s!"(Endblock.regReadElse (D := z.deklaration) {fin (N.reg r) "z.regs.length"} {bew} {← drE N zusage} {← drEnd N sonst} {← drEnd N rest})"
  | .awaits g _ _ _ _ rest => do .ok s!"(Endblock.awaits (D := z.deklaration) {fin (N.glob g) "z.globs.length"} _ rfl {bew} {bew} {← drEnd N rest})"
  | .bindCallInd p args _ _ _ rest => do .ok s!"(Endblock.bindCallInd (D := z.deklaration) {← drE N p} {← drA N args} {bew} {bew} {bew} {← drEnd N rest})"
  | .narrow e lo' hi' sonst rest => do .ok s!"(Endblock.narrow (D := z.deklaration) {← drE N e} {zahl lo'} {zahl hi'} {← drEnd N sonst} {← drEnd N rest})"
  | .exchange g neu _ _ rest => do .ok s!"(Endblock.exchange (D := z.deklaration) {fin (N.glob g) "z.globs.length"} {← drE N neu} {bew} {bew} {← drEnd N rest})"
  | .ite c t e => do .ok s!"(Endblock.ite (D := z.deklaration) {← drE N c} {← drEnd N t} {← drEnd N e})"

/-- The arms of a `match` on a tagged value. -/
def drArms (N : Namen D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs → Except String String
  | _, .nil => .ok s!"(Arms.nil (D := z.deklaration))"
  | _, .cons b rest => do .ok s!"(Arms.cons (D := z.deklaration) {← drB N b} {← drArms N rest})"

/-- The arms of a `match` on a reason. -/
def drGArms (N : Namen D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : {n : Nat} → GrundArms D V l Γ Λ Λ' n → Except String String
  | _, .nil => .ok s!"(GrundArms.nil (D := z.deklaration))"
  | _, .cons b rest => do .ok s!"(GrundArms.cons (D := z.deklaration) {← drB N b} {← drGArms N rest})"

end

/-- An expression, an end block (the entry points of the witness printer). -/
def expr (N : Namen D) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) : Except String String := drE N e

def endblock (N : Namen D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    Except String String := drEnd N e

end Gabbro.Grammatik.Gen.LeanTerm
