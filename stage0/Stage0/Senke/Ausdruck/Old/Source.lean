/- Bridge numeric source old(global) to the existing G constructor without changing the shared parser.
   The ordinary elaborator resolves every name and type; source/side pairs are checked structurally.
   The caller checks the restored program with the full AkzeptiertX, never the temporary program. -/
import Grammatik.Parser.Cover.Differenz

namespace Gabbro.Stage0.OldSource
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- Only these source forms participate in the numeric entry-global bridge. -/
def hasEntry : SExpr → Bool
  | .old (.variable _) => true
  | .bin _ a b => hasEntry a || hasEntry b
  | .un _ a => hasEntry a
  | _ => false

def normalize : SExpr → SExpr
  | .old (.variable g) => .variable g
  | .bin op a b => .bin op (normalize a) (normalize b)
  | .un op a => .un op (normalize a)
  | e => e

def normalizeItem : SItemTief → SItemTief
  | .fnT sig body => .fnT {sig with klauseln := sig.klauseln.map fun k => match k with
      | .gives e => .gives (normalize e)
      | k => k} body
  | item => item

def clauses (items : List SItemTief) (name : String) : List SExpr :=
  match items.find? (fun item => match item with | .fnT sig _ => sig.name == name | _ => false) with
  | some (.fnT sig _) => sig.klauseln.filterMap fun k => match k with | .gives e => some e | _ => none
  | _ => []

/-- Preserve the declared type and guard proof when selecting the existing entry-read constructor. -/
def oldGlobal {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    {τ : Ty} → Expr D Γ Λ τ → Except String (Expr D Γ Λ τ)
  | _, .glob g h => .ok (.oldG g h)
  | _, _ => .error "ir: old(global) did not resolve to a global read"

/-- Reuse the ordinary elaborator for every subtree without an entry-global occurrence. -/
def side (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    SExpr → USide → Except String (LowSide u Γ Λ)
  | src, val =>
    if !hasEntry src then lowSideEns u Γ Λ fn er val else
    match src, val with
    | .old (.variable name), .glob g => do
        if name != g then throw "ir: old(global) name mismatch"
        let s ← lowGlobSide u Γ Λ g
        let term ← oldGlobal s.term
        pure {s with term}
    | .bin "+" a b, .add x y => do
        pure (LowSide.plus (← side u Γ Λ fn er a x) (← side u Γ Λ fn er b y))
    | .bin "-" a b, .sub x y => do
        pure (LowSide.minus (← side u Γ Λ fn er a x) (← side u Γ Λ fn er b y))
    | .bin "*" a b, .mul x y => do
        pure (LowSide.times (← side u Γ Λ fn er a x) (← side u Γ Λ fn er b y))
    | _, _ => .error "ir: unsupported source expression containing old(global)"
termination_by src _ => sizeOf src

/-- Numeric comparisons and Boolean structure preserve the source occurrence of old. -/
def predicate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    SExpr → UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | src, val =>
    if !hasEntry src then lowEns u Γ Λ fn er val else
    match src, val with
    | .bin op a b, .cmp op' x y => do
        if op != op' then throw "ir: old(global) comparison mismatch"
        let a ← side u Γ Λ fn er a x
        let b ← side u Γ Λ fn er b y
        match op with
        | "==" => pure (.eq a.term b.term)
        | "!=" => pure (.not (.eq a.term b.term))
        | "<" => pure (.lt a.term b.term)
        | "<=" => pure (.le a.term b.term)
        | ">" => pure (.lt b.term a.term)
        | ">=" => pure (.le b.term a.term)
        | _ => throw "ir: unsupported old(global) comparison"
    | .bin "&&" a b, .and x y => do
        pure (.and (← predicate u Γ Λ fn er a x) (← predicate u Γ Λ fn er b y))
    | .bin "||" a b, .or x y => do
        pure (.or (← predicate u Γ Λ fn er a x) (← predicate u Γ Λ fn er b y))
    | .un "!" a, .not x => do pure (.not (← predicate u Γ Λ fn er a x))
    | _, _ => .error "ir: unsupported source postcondition containing old(global)"
termination_by src _ => sizeOf src

def predicates (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty) :
    List SExpr → List UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | [], [] => pure .tru
  | a :: rest, x :: xs => do
      pure (.and (← predicate u Γ Λ fn er a x) (← predicates u Γ Λ fn er rest xs))
  | _, _ => .error "ir: old(global) postcondition count mismatch"

def atFunction (items : List SItemTief) (u : UProg) (P : Programm (declOf u))
    (f : Fin u.fns.length) : Except String (EnsTy u f) := do
  let src := clauses items (fnAt u f).name
  if !src.any hasEntry then return P.ensures f
  let e ← predicates u (ErgCtx (ctxOf u f) ((verOf u f).erg)) (resOf u f)
    (fnAt u f) (fnAt u f).ergTy src (fnAt u f).gives
  pure (by
    unfold EnsTy
    rw [← ensCtx_eq u f, ← endeRes_eq u f]
    exact e)

/-- Evaluate a dependent family once, retaining each result at its own index. -/
def collect : (n : Nat) → (T : Fin n → Type) → ((i : Fin n) → Except String (T i)) →
    Except String ((i : Fin n) → T i)
  | 0, _, _ => pure (fun i => nomatch i)
  | n + 1, T, get => do
      let head ← get 0
      let tail ← collect n (fun i => T i.succ) (fun i => get i.succ)
      pure (Fin.cases head tail)

def restore (items : List SItemTief) (u : UProg) (P : Programm (declOf u)) :
    Except String (Programm (declOf u)) := do
  let es ← collect u.fns.length (EnsTy u) (atFunction items u P)
  pure {P with ensures := es}

/-- The full goal-theorem checker, on the final restored program and all original enumerations. -/
def accepts (u : UProg) (P : Programm (declOf u)) : Except String Bool := do
  if !sperrInvsOk u then throw "lock invariant without G form"
  haveI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
  let ws : List (declOf u).Fn := (u.roots ++ u.gestartet ++ u.gestartet).filterMap fun n => wurzelIdx u n
  let ls : List (declOf u).Lock := List.finRange u.locks.length
  let cs : List ((declOf u).Tab ⊕ (declOf u).Glob) :=
    (List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr
  pure (AkzeptiertX P (sperrFamilie u) (List.finRange u.fns.length) ls cs ws)

end Gabbro.Stage0.OldSource
