module

public import Grammatik.Gen.Text.Delab.Teil1
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

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser
variable (z : Spez) (V : Vertrag z.deklaration)
/-! ### The declaration -/

def kommaNamen (ns : List String) : List Token :=
  (ns.map fun n => [nameTok n]).intersperse [.zeichen ","] |>.flatten

/- The locks a body takes itself (`locks L { .. }`, in the order they are written), read off the model. -/
mutual

def sperrenS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Stmt z.deklaration V l Γ Λ Λ' → List z.deklaration.Lock
  | .locks L _ body => L :: sperrenB body
  | .ite _ t e => sperrenB t ++ sperrenB e
  | .traverse _ _ body => sperrenB body
  | .consumeTraverse _ _ _ _ _ _ body => sperrenB body
  | .callIndElse _ _ _ _ _ err => sperrenE err
  | _ => []

def sperrenB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Block z.deklaration V l Γ Λ Λ' → List z.deklaration.Lock
  | .cons s rest => sperrenS s ++ sperrenB rest
  | .bind _ rest => sperrenB rest
  | .bindCall _ _ _ _ _ rest => sperrenB rest
  | .bindCallElse _ _ _ _ _ err rest => sperrenE err ++ sperrenB rest
  | .bindCallIndElse _ _ _ _ _ err rest => sperrenE err ++ sperrenB rest
  | .bindCallInd _ _ _ _ _ rest => sperrenB rest
  | .regRead _ _ rest => sperrenB rest
  | .regReadElse _ _ _ sonst rest => sperrenE sonst ++ sperrenB rest
  | .awaits _ _ _ _ _ rest => sperrenB rest
  | _ => []

def sperrenE {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} :
    Endblock z.deklaration V l Γ Λ → List z.deklaration.Lock
  | .cons s rest => sperrenS s ++ sperrenE rest
  | .bind _ rest => sperrenE rest
  | .bindCall _ _ _ _ _ rest => sperrenE rest
  | .bindCallElse _ _ _ _ _ err rest => sperrenE err ++ sperrenE rest
  | .regRead _ _ rest => sperrenE rest
  | .regReadElse _ _ _ sonst rest => sperrenE sonst ++ sperrenE rest
  | .awaits _ _ _ _ _ rest => sperrenE rest
  | .bindCallInd _ _ _ _ _ rest => sperrenE rest
  | .bindCallIndElse _ _ _ _ _ err rest => sperrenE err ++ sperrenE rest
  | _ => []

end

/-- The parameters: the `j`-th of `np` is `v{np-1-j}` (the variable of depth `j` in the body). -/
def parListe (otab : Int → Option Nat) (np : Nat) : Nat → List Ty → Except String (List (String × STyp))
  | _, [] => .ok []
  | j, t :: ts => do .ok ((nVar (np - 1 - j), ← typS otab t) :: (← parListe otab np (j + 1) ts))

/-- The table an option of count `n` indexes: the first table of that count. -/
def optTab (n : Int) : Option Nat :=
  ((List.finRange z.tabs.length).find? fun t => decide ((z.tabs.get t).count = n)).map (·.val)

/-- The result type of a function. -/
def delabRes (f : Fin z.fns.length) : Except String (Option STyp) :=
  match (z.deklaration.signatur f).erg with
  | none => pure none
  | some t => do pure (some (← typS (optTab z) t))

/-- Is the predicate `true` (then no clause is printed)? -/
def istTru {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} : Expr z.deklaration Γ Λ τ → Bool
  | .tru => true
  | _ => false

/-- The `requires` clause (none for `true`). -/
def delabReq (P : Programm z.deklaration) (f : Fin z.fns.length) : Except String (List SKlausel) :=
  if istTru z (P.requires f) then pure [] else do pure [SKlausel.needs (← delabE z none (P.requires f))]

/-- The `ensures` clause (none for `true`); its result is named by its number. -/
def delabEns (P : Programm z.deklaration) (f : Fin z.fns.length) : Except String (List SKlausel) :=
  if istTru z (P.ensures f) then pure [] else do
    pure [SKlausel.gives (← delabE z ((z.deklaration.signatur f).erg.map fun _ =>
      (z.deklaration.signatur f).params.length) (P.ensures f))]

/-- The held locks, the written tables and statics, the locks the body takes: by name. -/
def heldNamen (f : Fin z.fns.length) : List String :=
  (z.deklaration.signatur f).haelt.map fun L => nLock (show Fin z.locks.length from L).val
def tNamen (f : Fin z.fns.length) : List Nat :=
  ((List.finRange z.tabs.length).filter fun t => (z.deklaration.signatur f).schreibt t).map (·.val)
def gNamen (f : Fin z.fns.length) : List Nat :=
  ((List.finRange z.globs.length).filter fun g => (z.deklaration.signatur f).gschreibt g).map (·.val)
def lNamen (P : Programm z.deklaration) (f : Fin z.fns.length) : List String :=
  ((sperrenE z (vertragVon z.deklaration f) (P.rumpf f)).map fun L => nLock (show Fin z.locks.length from L).val).eraseDups

/-- The effects of a function. -/
def effListe (P : Programm z.deklaration) (f : Fin z.fns.length) : List SEffekt :=
  (tNamen z f).map (fun i => SEffekt.writes (.field (.variable (nTab i)) "slots")) ++
    (gNamen z f).map (fun i => SEffekt.writes (.variable (nGlob i))) ++
    (lNamen z P f).map (fun l => SEffekt.locks false (.variable l))

/-- `requires Held(..)` for the held locks (none without). -/
def heldKlausel (f : Fin z.fns.length) : List SKlausel :=
  if (heldNamen z f).isEmpty then [] else [SKlausel.needs (.call "Held" ((heldNamen z f).map SExpr.variable))]

/-- `effects { .. }` (none without). -/
def effKlausel (P : Programm z.deklaration) (f : Fin z.fns.length) : List SKlausel :=
  if (effListe z P f).isEmpty then [] else [SKlausel.effs (effListe z P f)]

/-- The clauses of a function. -/
def klauselnVon (P : Programm z.deklaration) (f : Fin z.fns.length) (req ens : List SKlausel) : List SKlausel :=
  heldKlausel z f ++ req ++ ens ++ effKlausel z P f

/-- One function. -/
def delabFn (P : Programm z.deklaration) (mitGriff : Bool) (f : Fin z.fns.length) : Except String SItemTief := do
  let s := z.deklaration.signatur f
  let np := s.params.length
  let ps ← parListe (optTab z) np 0 s.params
  let ps := ps ++ (if mitGriff then [("d", .atom "Dev")] else [])
  let res ← delabRes z f
  let req ← delabReq z P f
  let ens ← delabEns z P f
  let (ss, ende) ← delabEnd z (vertragVon z.deklaration f) (P.rumpf f)
  pure (.fnT { art := "impl", name := nFn f.val, params := ps, res,
               fehler := if s.gruende = 0 then none else some (nGrund s.gruende),
               klauseln := klauselnVon z P f req ens } (SAnw.block ss ende))

/-- The reason types the unit names. -/
def gruende : List Nat :=
  (((List.finRange z.fns.length).flatMap fun f =>
    z.deklaration.gruende f :: (((z.deklaration.signatur f).params ++ (z.deklaration.signatur f).erg.toList).filterMap
      fun t => match t with
        | .why n => some n
        | _ => none)).filter (· ≠ 0)).eraseDups

def grundItem (n : Nat) : SItemTief :=
  .whyT (nGrund n) ((List.range n).map fun j => (nFall j, .lit (j + 1), s!"c{j}")) true

def delabTab (t : Fin z.tabs.length) : Except String SItemTief := do
  let tz := z.tabs.get t
  let fs ← (tz.felder.zipIdx.map fun (fz, j) => do
    pure ({ fname := nFeld j, ftyp := ← typS (optTab z) fz.typ, pos := none, bezug := none, wo := none,
            reserviert := false, byOps := false } : SFeld)).mapM id
  if tz.count < 0 then throw "table with a negative count"
  pure (.tableT (nTab t.val) none (some (.lit tz.count.toNat)) none none (z.deklaration.geteilt t) [.tSlot fs])

def anfang : Ty → SKonstWert
  | .int lo hi => .one (zahlE (if lo > 0 then lo else if hi < 0 then hi else 0))
  | .bool => .one .fls
  | _ => .one (.lit 0)

def delabGlob (g : Fin z.globs.length) : Except String SItemTief := do
  let gz := z.globs.get g
  let ty ← typS (optTab z) gz.typ
  if gz.atomar then
    let nl := z.deklaration.nutzlast g
    pure (.atomT (nGlob g.val) ty (if nl.isEmpty then none else
      some (nl.map fun h => .variable (nGlob (show Fin z.globs.length from h).val))) none none)
  else
    pure (.globT true (nGlob g.val) ty (anfang gz.typ) none none (z.deklaration.ggeteilt g))

/-- A required resource is the lock `L`. -/
def istLock (L : Fin z.locks.length) : z.deklaration.Lock ⊕ (z.deklaration.Marke × Nat) → Bool
  | .inl M => (show Fin z.locks.length from M).val == L.val
  | .inr _ => false

def delabLock (L : Fin z.locks.length) : Except String SItemTief := do
  let lz := z.locks.get L
  let schuetzt :=
    ((List.finRange z.tabs.length).filter fun t => (z.deklaration.braucht t).any (istLock z L)).map
      (fun t => SExpr.variable (nTab t.val)) ++
    ((List.finRange z.globs.length).filter fun g => (z.deklaration.gbraucht g).any (istLock z L)).map
      (fun g => SExpr.variable (nGlob g.val))
  if lz.rang < 0 then throw "lock with a negative rank"
  pure (.lockT (nLock L.val) schuetzt (.lit lz.rang.toNat) none none (if lz.maskiert then some "irqs" else none) none)

def klasseWort : Regklasse → String
  | .r => "r"
  | .w => "w"
  | .rw => "rw"
  | .w1c => "w1c"
  | .rc => "rc"

def delabReg (r : Fin z.regs.length) : Except String SGerTeil := do
  let rz := z.regs.get r
  let ty ← match rz.typ with
    | .int lo hi => pure (STyp.range (.atom (if 0 ≤ lo then "u64" else "i64")) (zahlE lo) (zahlE hi) false)
    | .bool => pure (STyp.atom "bool")
    | _ => throw "register of a type without a spelling"
  pure (.reg { name := nReg r.val, rtyp := ty, addr := .lit (4 * r.val),
               klasse := klasseWort rz.klasse,
               stage := [], felder := [], voraus := if rz.zusage then none else some .fls, elseF := none,
               abhaengt := (rz.traeger.filter (· < z.tabs.length)).map fun t => [nTab t] })

def delabDev : Except String (List SItemTief) := do
  if z.regs.isEmpty then return []
  let rs ← (List.finRange z.regs.length).mapM (delabReg z)
  let spiegel := (List.finRange z.regs.length).filterMap fun r =>
    ((z.regs.get r).spiegel.filter (· < z.regs.length)).map fun m => SGerTeil.copy (.variable (nReg r.val)) (.variable (nReg m))
  pure [.devT "Dev" [] "mmio" (spiegel ++ rs)]

def delabInv (P : Programm z.deklaration) (i : Fin z.invs.length) : Except String SItemTief := do
  let ts := (z.traeger i).map fun t => nTab t.val
  let p ← delabE z none (P.invariante i)
  pure (.groupT ("G" ++ toString i.val) ts [{ name := "I" ++ toString i.val, kosten := .lit 1, online := false, proof := none, pred := p }])

end Gabbro.Grammatik.Gen.Text
