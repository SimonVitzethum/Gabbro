module
public import Gabbro.Body
@[expose] public section

/-!
# Body terms in the notation of the source

The generated duty files print every Body term twice: as the Lean term the duty is stated over,
and, in a comment beside it, in a notation close to Gabbro's own, so that a person reads the
duty as their program. This printer occurs in no statement and in no proof.
-/

namespace Gabbro.Bruecke.Vorlage

open Gabbro.Body

def zeigeWert : Value → String
  | .int n => toString n
  | .bool b => toString b
  | .absent => "None"
  | .present n => "Some(" ++ toString n ++ ")"
  | .reason r => r
  | .tagged t none => t
  | .tagged t (some p) => t ++ "(" ++ toString p ++ ")"
  | .record fs => "{" ++ String.intercalate ", " (fs.attach.map fun ⟨v, _⟩ => zeigeWert v) ++ "}"

def zeigeBin (op : BinOp) : String := (repr op).pretty 1000 |>.replace "Gabbro.Body.BinOp." ""
def zeigeUn (op : UnOp) : String := (repr op).pretty 1000 |>.replace "Gabbro.Body.UnOp." ""

def zeigeExpr : Expr → String
  | .lit v => zeigeWert v
  | .name n => n
  | .place c i f => c ++ ".slots[" ++ zeigeExpr i ++ "]." ++ f
  | .global n => n
  | .un op a => zeigeUn op ++ "(" ++ zeigeExpr a ++ ")"
  | .bin op a b => "(" ++ zeigeExpr a ++ " " ++ zeigeBin op ++ " " ++ zeigeExpr b ++ ")"
  | .someOf a => "Some(" ++ zeigeExpr a ++ ")"
  | .fieldOf c n => c ++ "." ++ n
  | .forallSlots v n b => "forall " ++ v ++ " < " ++ toString n ++ " : " ++ zeigeExpr b
  | .existsSlots v n b => "exists " ++ v ++ " < " ++ toString n ++ " : " ++ zeigeExpr b
  | .reaches c s d via _ => c ++ ".slots[" ++ zeigeExpr s ++ "] reaches " ++ c ++ ".slots[" ++
      zeigeExpr d ++ "] via " ++ via
  | .chainFrom c h x via _ => zeigeExpr x ++ " in chain(" ++ zeigeExpr h ++ ", " ++ via ++ ") of " ++ c
  | .hasShape n _ => n ++ " has its declared shape"
  | .wrapTo bits s a => "wrap" ++ (if s then "i" else "u") ++ toString bits ++ "(" ++ zeigeExpr a ++ ")"
  | .tagOf t none => t
  | .tagOf t (some p) => t ++ "(" ++ zeigeExpr p ++ ")"
  | .recOf as => "{" ++ String.intercalate ", " (as.attach.map fun ⟨a, _⟩ => zeigeExpr a) ++ "}"
  | .recGet b i => zeigeExpr b ++ "." ++ toString i
  | .recSet b i v => zeigeExpr b ++ " with ." ++ toString i ++ " = " ++ zeigeExpr v

def einzug (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

def zeigeArgs (es : List Expr) : String := String.intercalate ", " (es.map zeigeExpr)

mutual
def zeigeStmt (n : Nat) : Stmt → List String
  | .assign c i f v => [einzug n ++ c ++ ".slots[" ++ zeigeExpr i ++ "]." ++ f ++ " = " ++ zeigeExpr v ++ ";"]
  | .assignField c f v => [einzug n ++ c ++ "." ++ f ++ " = " ++ zeigeExpr v ++ ";"]
  | .assignGlobal g v => [einzug n ++ g ++ " = " ++ zeigeExpr v ++ ";"]
  | .bindName x v => [einzug n ++ x ++ " := " ++ zeigeExpr v ++ ";"]
  | .ite c t e => [einzug n ++ "if " ++ zeigeExpr c ++ " {"] ++ zeigeBlock (n + 1) t ++
      [einzug n ++ "} else {"] ++ zeigeBlock (n + 1) e ++ [einzug n ++ "}"]
  | .onOption g b p a => [einzug n ++ "match " ++ zeigeExpr g ++ " { Some(" ++ b ++ ") => {"] ++
      zeigeBlock (n + 1) p ++ [einzug n ++ "} None => {"] ++ zeigeBlock (n + 1) a ++ [einzug n ++ "} }"]
  | .call f _ as _ => [einzug n ++ f ++ "(" ++ zeigeArgs as ++ ");"]
  | .bindCall x f _ as _ => [einzug n ++ x ++ " := " ++ f ++ "(" ++ zeigeArgs as ++ ");"]
  | .bindCallElse x f _ as _ e b => [einzug n ++ x ++ " := " ++ f ++ "(" ++ zeigeArgs as ++ ") else (" ++ e ++ ") {"] ++
      zeigeBlock (n + 1) b ++ [einzug n ++ "}"]
  | .onReason g arms => [einzug n ++ "match " ++ zeigeExpr g ++ " {"] ++ zeigeArme (n + 1) arms ++ [einzug n ++ "}"]
  | .onTag g arms => [einzug n ++ "match " ++ zeigeExpr g ++ " {"] ++ zeigeTagArme (n + 1) arms ++ [einzug n ++ "}"]
  | .retCall f _ as _ => [einzug n ++ "return " ++ f ++ "(" ++ zeigeArgs as ++ ");"]
  | .loop id _ b => [einzug n ++ "loop " ++ id ++ " {"] ++ zeigeBlock (n + 1) b ++ [einzug n ++ "}"]
  | .locked l b => [einzug n ++ "locks " ++ l ++ " {"] ++ zeigeBlock (n + 1) b ++ [einzug n ++ "}"]
  | .breaking is b => [einzug n ++ "breaking " ++ String.intercalate ", " is ++ " {"] ++ zeigeBlock (n + 1) b ++
      [einzug n ++ "}"]
  | .publish a v _ => [einzug n ++ a ++ " = " ++ zeigeExpr v ++ " publishes;"]
  | .awaitLoad x a _ => [einzug n ++ x ++ " := " ++ a ++ " awaits;"]
  | .exchangeWith x a v => [einzug n ++ x ++ " := " ++ a ++ " exchange " ++ zeigeExpr v ++ ";"]
  | .ret none => [einzug n ++ "return;"]
  | .ret (some e) => [einzug n ++ "return " ++ zeigeExpr e ++ ";"]
  | .exit => [einzug n ++ "next;"]
  | .leave => [einzug n ++ "leave;"]
  | .forEach x is b => [einzug n ++ "for " ++ x ++ " in " ++ toString is.length ++ " indices {"] ++
      zeigeBlock (n + 1) b ++ [einzug n ++ "}"]
  | .retry k s b o => [einzug n ++ "retry until " ++ zeigeExpr s ++ " bounded " ++ toString k ++ " {"] ++
      zeigeBlock (n + 1) b ++ [einzug n ++ "} on_exceeded {"] ++ zeigeBlock (n + 1) o ++ [einzug n ++ "}"]
def zeigeBlock (n : Nat) : List Stmt → List String
  | [] => []
  | s :: ss => zeigeStmt n s ++ zeigeBlock n ss
def zeigeArme (n : Nat) : List (String × List Stmt) → List String
  | [] => []
  | (c, b) :: rest => [einzug n ++ c ++ " => {"] ++ zeigeBlock (n + 1) b ++ [einzug n ++ "}"] ++ zeigeArme n rest
def zeigeTagArme (n : Nat) : List (String × Option String × List Stmt) → List String
  | [] => []
  | (c, bd, b) :: rest =>
    [einzug n ++ c ++ (match bd with | some x => "(" ++ x ++ ")" | none => "") ++ " => {"] ++
      zeigeBlock (n + 1) b ++ [einzug n ++ "}"] ++ zeigeTagArme n rest
end

/-- The body as comment lines (each prefixed for a Lean doc comment block). -/
def zeigeKoerper (body : List Stmt) : String :=
  String.join ((zeigeBlock 1 body).map (· ++ "\n"))

end Gabbro.Bruecke.Vorlage
