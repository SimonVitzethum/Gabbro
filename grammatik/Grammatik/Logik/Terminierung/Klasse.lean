/-
  File:      Grammatik/Logik/Terminierung/Klasse.lean
  Subject:   T1 -- THE TERMINATION CLASS OF EVERY FUNCTION, DECIDED FROM THE SYNTAX (2026-10-22).

  An algorithm over the program text (a Bool computation over the bodies and the call graph) puts every function
  into exactly one class. The classes, strongest first:
  * `endet` -- every call returns: no `forever` in the call hull, every recursion cycle carries a measure
    (`decreases`). Bounds: T3/T4.
  * `umgebung` -- a `forever` in the hull, left by no `leave` and no `return` inside it: once control is in the
    loop, only the environment ends it (the `progress a` assumption of the loop; machine G grants its passes from
    outside). A kernel that ends only on a shutdown signal is in this class.
  * `bedingt` -- a `forever` left by a `leave` or a `return` inside it, or a tail-call cycle without a measure: it
    ends exactly when a named condition C of the program holds -- the guard of the exit, or the base path of the
    cycle. An interpreter that ends when its guest halts is in this class. An exit condition does not prove that
    the exit is reached: `Berechenbarkeit/RunsUntil.lean` states and proves the exact path and guard obligations.
    No Turing-completeness or general undecidability theorem follows from this classification.
  * `abgelehnt` -- refused: a recursion cycle with a non-tail call and no measure, or a `forever` whose pass is not
    itself of class `endet` (a pass must end, so that every service is productive).
  A function's class is the weakest local class in its call hull (`klasse`). What each class means in the model:
  `endet` -- `endet_satz` (Entscheidung.lean); `umgebung` and `bedingt` -- the exit condition of their loops
  (`forever_umgebung`, `forever_bedingt`, Ausgang.lean).
-/
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The classes -/

/-- The termination classes, strongest first. -/
inductive TermKlasse where
  | endet
  | umgebung
  | bedingt
  | abgelehnt
  deriving DecidableEq, Repr

namespace TermKlasse

/-- The order: `endet` is the strongest, `abgelehnt` the weakest. -/
def rang : TermKlasse → Nat
  | endet => 0
  | umgebung => 1
  | bedingt => 2
  | abgelehnt => 3

/-- The weaker of two classes. -/
def schwaecher (a b : TermKlasse) : TermKlasse := if b.rang ≤ a.rang then a else b

theorem rang_inj {a b : TermKlasse} (h : a.rang = b.rang) : a = b := by
  cases a <;> cases b <;> simp_all [rang]

theorem schwaecher_rang (a b : TermKlasse) : (schwaecher a b).rang = max a.rang b.rang := by
  unfold schwaecher; split <;> omega

end TermKlasse

/-! ## 2. What a body contains -/

/-- What the algorithm reads off one body (callees by name, indirect calls by signature). -/
structure Befund (D : Deklaration) where
  /-- a `forever` stands in the body -/
  ewig : Bool := false
  /-- a `leave` or a `return` leaves a `forever` -/
  austritt : Bool := false
  /-- the direct callees -/
  rufe : List D.Fn := []
  /-- the signatures of indirect calls -/
  sigs : List Nat := []
  /-- the direct callees inside a `forever` pass -/
  rufeImEwig : List D.Fn := []
  /-- the signatures of indirect calls inside a `forever` pass -/
  sigsImEwig : List Nat := []
  /-- the callees called somewhere NOT in tail position -/
  nichtEnd : List D.Fn := []

namespace Befund

/-- Two findings together. -/
def und (a b : Befund D) : Befund D :=
  ⟨a.ewig || b.ewig, a.austritt || b.austritt, a.rufe ++ b.rufe, a.sigs ++ b.sigs, a.rufeImEwig ++ b.rufeImEwig,
   a.sigsImEwig ++ b.sigsImEwig, a.nichtEnd ++ b.nichtEnd⟩

instance : Append (Befund D) := ⟨und⟩

/-- One call of `g`; `imEwig`: inside a `forever` pass; `end`: in tail position. -/
def ruf (g : D.Fn) (imEwig istEnd : Bool) : Befund D :=
  { rufe := [g], rufeImEwig := if imEwig then [g] else [], nichtEnd := if istEnd then [] else [g] }

/-- One indirect call through signature `n` (never counted as a tail call). -/
def rufInd (n : Nat) (imEwig : Bool) : Befund D :=
  { sigs := [n], sigsImEwig := if imEwig then [n] else [] }

end Befund

/-- The index of a variable. -/
def Var.idx : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

/-- The expression is the newest bound variable. -/
def Expr.istHier {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Bool
  | .var x => x.idx == 0
  | _ => false

/-- The answer expression is the newest bound variable. -/
def ErgExpr.istHier {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} : ErgExpr D Γ Λ e → Bool
  | .val x => x.istHier
  | .empty => false

/-- The answer expression is empty (`return;`). -/
def ErgExpr.istLeer {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} : ErgExpr D Γ Λ e → Bool
  | .empty => true
  | .val _ => false

section Falten

variable {V : Vertrag D}

/-- The block starts with `return x;` of the newest bound variable. -/
def Block.retHier {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .cons (.ret e _) _ => e.istHier
  | _ => false

/-- The end block is `return x;` of the newest bound variable. -/
def Endblock.retHier {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret e _ => e.istHier
  | _ => false

/-- The block starts with `return;`. -/
def Block.retLeer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .cons (.ret e _) _ => e.istLeer
  | _ => false

/-- The end block is `return;`. -/
def Endblock.retLeer {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret e _ => e.istLeer
  | _ => false

mutual

/-- What a statement contains. `ebene`: the innermost loop around it is a `forever` (a `leave` here leaves it);
    `imEwig`: it stands inside a `forever` pass; `danachLeer`: the statement is followed by `return;` (a call here
    is a tail call). -/
def befS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ebene imEwig danachLeer : Bool) :
    Stmt D V l Γ Λ Λ' → Befund D
  | .ite _ t e => befB ebene imEwig t ++ befB ebene imEwig e
  | .onOption _ p a => befB ebene imEwig p ++ befB ebene imEwig a
  | .onTag _ arms => befArms ebene imEwig arms
  | .onWhy _ arms => befGArms ebene imEwig arms
  | .call g _ _ _ => Befund.ruf g imEwig danachLeer
  | .callInd (n := n) _ _ _ _ => Befund.rufInd n imEwig
  | .locks _ _ body => befB ebene imEwig body
  | .breaking _ body => befB ebene imEwig body
  | .traverse _ _ body => befB false imEwig body
  | .retry _ _ body ueber => befB false imEwig body ++ befB ebene imEwig ueber
  | .forever _ _ body => { ewig := true } ++ befB true true body
  | .leave _ => { austritt := ebene }
  | .ret .. => { austritt := imEwig }
  | .retWhy .. => { austritt := imEwig }
  | _ => {}

def befB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ebene imEwig : Bool) :
    Block D V l Γ Λ Λ' → Befund D
  | .nil => {}
  | .cons s rest => befS ebene imEwig rest.retLeer s ++ befB ebene imEwig rest
  | .bind _ rest => befB ebene imEwig rest
  | .bindCall g _ _ _ _ rest => Befund.ruf g imEwig rest.retHier ++ befB ebene imEwig rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => Befund.rufInd n imEwig ++ befB ebene imEwig rest
  | .bindCallElse g _ _ _ _ err rest =>
      Befund.ruf g imEwig false ++ befE ebene imEwig err ++ befB ebene imEwig rest
  | .bindAxiom _ _ _ _ _ _ _ rest => befB ebene imEwig rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => befE ebene imEwig err ++ befB ebene imEwig rest
  | .regRead _ _ rest => befB ebene imEwig rest
  | .regReadElse _ _ _ sonst rest => befE ebene imEwig sonst ++ befB ebene imEwig rest
  | .awaits _ _ _ _ _ rest => befB ebene imEwig rest
  | .exchange _ _ _ _ rest => befB ebene imEwig rest
  | .narrow _ _ _ sonst rest => befE ebene imEwig sonst ++ befB ebene imEwig rest
  | .check _ sonst rest => befE ebene imEwig sonst ++ befB ebene imEwig rest
  | .float _ _ _ _ _ rest => befB ebene imEwig rest
  | .floatLit _ _ _ rest => befB ebene imEwig rest
  | .floatOf _ _ _ rest => befB ebene imEwig rest
  | .floatNarrow _ _ _ sonst rest => befE ebene imEwig sonst ++ befB ebene imEwig rest

def befArms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (ebene imEwig : Bool) :
    Arms D V l Γ Λ Λ' cs → Befund D
  | .nil => {}
  | .cons b rest => befB ebene imEwig b ++ befArms ebene imEwig rest

def befGArms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} (ebene imEwig : Bool) :
    GrundArms D V l Γ Λ Λ' n → Befund D
  | .nil => {}
  | .cons b rest => befB ebene imEwig b ++ befGArms ebene imEwig rest

def befE {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ebene imEwig : Bool) : Endblock D V l Γ Λ → Befund D
  | .ret .. => { austritt := imEwig }
  | .retWhy .. => { austritt := imEwig }
  | .leave _ => { austritt := ebene }
  | .next _ => {}
  | .cons s rest => befS ebene imEwig rest.retLeer s ++ befE ebene imEwig rest
  | .bind _ rest => befE ebene imEwig rest
  | .bindCall g _ _ _ _ rest => Befund.ruf g imEwig rest.retHier ++ befE ebene imEwig rest
  | .bindCallElse g _ _ _ _ err rest =>
      Befund.ruf g imEwig false ++ befE ebene imEwig err ++ befE ebene imEwig rest
  | .bindAxiom _ _ _ _ _ _ _ rest => befE ebene imEwig rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => befE ebene imEwig err ++ befE ebene imEwig rest
  | .regRead _ _ rest => befE ebene imEwig rest
  | .regReadElse _ _ _ sonst rest => befE ebene imEwig sonst ++ befE ebene imEwig rest
  | .awaits _ _ _ _ _ rest => befE ebene imEwig rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => Befund.rufInd n imEwig ++ befE ebene imEwig rest

end

end Falten

/-! ## 3. The class of a function -/

section Klasse

variable [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (mass : D.Fn → Bool)

/-- What the body of `f` contains. -/
def befund (f : D.Fn) : Befund D := befE false false (P.rumpf f)

/-- `f` may call `g` directly: by name, or through a signature `g` conforms to. -/
def direkt (f g : D.Fn) : Bool := (befund P f).rufe.contains g || (befund P f).sigs.any (D.passt g)

/-- `f` lies on a recursion cycle. -/
def imZyklus (f : D.Fn) : Bool := fs.any fun g => direkt P f g && reachB P fs g f

/-- Every call from `f` back into its own cycle is a tail call by name (an indirect call into the cycle is not). -/
def zyklusEndstaendig (f : D.Fn) : Bool :=
  fs.all fun g => !(reachB P fs g f) ||
    (!((befund P f).nichtEnd.contains g) && !((befund P f).sigs.any (D.passt g)))

/-- `g` may run inside a pass: no `forever`, and on no cycle without a measure. -/
def schlicht (g : D.Fn) : Bool := !(befund P g).ewig && (!(imZyklus P fs g) || mass g)

/-- Every function a `forever` pass of `f` may reach runs inside a pass. -/
def passOk (f : D.Fn) : Bool :=
  let ziele : List D.Fn := (befund P f).rufeImEwig ++
    fs.filter (fun g => (befund P f).sigsImEwig.any (D.passt g))
  ziele.all fun c => fs.all fun h => !(reachB P fs c h) || schlicht P fs mass h

/-- **The local class of `f`**: what its own body decides. -/
def lokal (f : D.Fn) : TermKlasse :=
  if !(passOk P fs mass f) then .abgelehnt
  else if imZyklus P fs f && !(mass f) then
    (if zyklusEndstaendig P fs f then .bedingt else .abgelehnt)
  else if (befund P f).austritt then .bedingt
  else if (befund P f).ewig then .umgebung
  else .endet

/-- **THE CLASS OF `f`**: the weakest local class in its call hull. -/
def klasse (f : D.Fn) : TermKlasse :=
  fs.foldl (fun k g => if reachB P fs f g then k.schwaecher (lokal P fs mass g) else k) .endet

/-- The class of a program: the weakest class of its starts. -/
def programmKlasse (ws : List D.Fn) : TermKlasse :=
  ws.foldl (fun k w => k.schwaecher (klasse P fs mass w)) .endet

end Klasse

end Gabbro.Grammatik
