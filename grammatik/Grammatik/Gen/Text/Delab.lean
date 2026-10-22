/-
  File:      Grammatik/Gen/Text/Delab.lean
  Subject:   DELABORATION: a program of the generator (a member `z : Spez`, its program `P`, its declared starts
             `ws`) as surface items (`List SItemTief`), in the spellings the Lean front end (`elabU`, `lowerAllg`)
             maps back to the model's forms.

  One `module m` with, in order: the tables (`table Ti count n [shared] { slot { fj : T, .. } }`), the statics and
  atomics (`static mut gi : T = v [shared];`, `atomic gi : T [publishes { .. }];`), the locks (`lock Li protects
  { .. } rank r [masks irqs];`), one device `Dev` with the registers (`reg ri : u64 in lo .. hi @i class k
  [requires false] [depends { .. }]`, `mirrors`), the reasons (`reason Rn { C0 = 1 "c0", .. exhaustive }`), one
  `group` per invariant, the functions, `concurrent { .. }` for the declared starts and one `entry .. via idt`
  per function the hardware enters.

  A function: its parameters (`vk`), a device handle `d : Dev` when the unit has registers (the front end erases
  it), its result and reason channel, `requires Held(..)` for the locks its signature holds, its `requires` and
  `ensures` when they are not `true`, `effects { writes .., locks .. }`, and the body. Bodies: `let`, calls,
  `p = &f; p(..)` for an indirect call (the model's pointer expression is bound first), `locks`, `if`,
  assignments, `publishes`, `awaits`, register reads and writes through `d`, `return`.

  Partial: a form without a spelling is an error naming it; the delaborator prints every form it accepts as
  itself, never a substitute (`awaits` needs an atomic static in the model, as in the language).
-/
import Grammatik.Gen.Zeugen.Schluss
import Grammatik.Parser.Round.RundlaufProgramm
import Grammatik.Parser.Cover.Mitglieder

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser

/-! ### Names -/

def nTab (i : Nat) : String := s!"T{i}"
def nFeld (j : Nat) : String := s!"f{j}"
def nGlob (i : Nat) : String := s!"g{i}"
def nLock (i : Nat) : String := s!"L{i}"
def nFn (i : Nat) : String := s!"fn{i}"
def nReg (i : Nat) : String := s!"r{i}"
def nVar (k : Nat) : String := s!"v{k}"
def nZeiger (k : Nat) : String := s!"p{k}"
def nGrund (n : Nat) : String := s!"R{n}"
def nFall (j : Nat) : String := s!"C{j}"

/-- The depth of a variable: `here` is 0. -/
def tiefe : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there v => tiefe v + 1

/-- A literal. -/
def zahlE (n : Int) : SExpr := if 0 ≤ n then .lit n.toNat else .un "-" (.lit (-n).toNat)

/-- A type. -/
def typS : Ty → Except String STyp
  | .int lo hi => .ok (.range (.atom (if 0 ≤ lo then "u64" else "i64")) (zahlE lo) (zahlE hi) false)
  | .bool => .ok (.atom "bool")
  | .why n => .ok (.atom (nGrund n))
  | _ => .error "type without a spelling"

variable (z : Spez)

/-! ### Expressions -/

/-- An expression; `kopf` is the number of the result variable in an `ensures` (the head of `ErgCtx`, named
    `result`), counted like every variable from the bottom of the context so that a binder below it does not
    move it. -/
def delabE (kopf : Option Nat) {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} :
    Expr z.deklaration Γ Λ τ → Except String SExpr
  | .lit n => .ok (zahlE n)
  | .tru => .ok .tru
  | .fls => .ok .fls
  | .var x => .ok (if kopf = some (Γ.length - 1 - tiefe x) then .res else .variable (nVar (Γ.length - 1 - tiefe x)))
  | .glob g _ => .ok (.variable (nGlob (show Fin z.globs.length from g).val))
  | .slot t f i _ => do
      let i' ← delabE kopf i
      .ok (.field (.index (.field (.variable (nTab (show Fin z.tabs.length from t).val)) "slots") i')
        (nFeld (show Fin _ from f).val))
  | .fnref f _ _ => .ok (.fnref (nFn (show Fin z.fns.length from f).val))
  | .widen _ _ e => delabE kopf e
  | .add a b => do .ok (.bin "+" (← delabE kopf a) (← delabE kopf b))
  | .sub a b => do .ok (.bin "-" (← delabE kopf a) (← delabE kopf b))
  | .mul a b => do .ok (.bin "*" (← delabE kopf a) (← delabE kopf b))
  | .neg a => do
      let a' ← delabE kopf a
      -- `-(n)` for a numeral (`-n` is the literal `-n`); every other operand prints `-x`/`-(x)`
      .ok (match a' with
        | .lit m => .un "-()" (.lit m)
        | x => .un "-" x)
  | .lt a b => do .ok (.bin "<" (← delabE kopf a) (← delabE kopf b))
  | .le a b => do .ok (.bin "<=" (← delabE kopf a) (← delabE kopf b))
  | .eq a b => do .ok (.bin "==" (← delabE kopf a) (← delabE kopf b))
  | .and a b => do .ok (.bin "&&" (← delabE kopf a) (← delabE kopf b))
  | .or a b => do .ok (.bin "||" (← delabE kopf a) (← delabE kopf b))
  | .not a => do .ok (.un "!" (← delabE kopf a))
  | .why n r => .ok (.why (nGrund n) (nFall r.val))
  | .forallSlots t body _ => do
      .ok (.ext .all [nVar Γ.length, "slots"] [.variable (nTab (show Fin z.tabs.length from t).val), ← delabE kopf body])
  | .existsSlots t body _ => do
      .ok (.ext .any [nVar Γ.length, "slots"] [.variable (nTab (show Fin z.tabs.length from t).val), ← delabE kopf body])
  | e => .error ("expression without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.eE e))

def delabA {Γ : Ctx} {Λ : List (Res z.deklaration)} {τs : List Ty} :
    Args z.deklaration Γ Λ τs → Except String (List SExpr)
  | .nil => .ok []
  | .cons e rest => do .ok ((← delabE z none e) :: (← delabA rest))

def delabR {Γ : Ctx} {Λ : List (Res z.deklaration)} {o : Option Ty} :
    ErgExpr z.deklaration Γ Λ o → Except String (Option SExpr)
  | .empty => .ok none
  | .val e => do .ok (some (← delabE z none e))

/-- A payload as the statement reader keeps it: the names, comma separated, or `nothing`. -/
def nutzText (gs : List z.deklaration.Glob) : String :=
  if gs.isEmpty then "nothing"
  else renderText (gs.map (fun g => [nameTok (nGlob (show Fin z.globs.length from g).val)]) |>.intersperse
    [.zeichen ","] |>.flatten)

/-- The payload of an `awaits` (braces around nothing are the empty text). -/
def nutzTextA (gs : List z.deklaration.Glob) : String :=
  if gs.isEmpty then "" else nutzText z gs

/-- The register `r` read or written through the device handle. -/
def regOrt (r : z.deklaration.Reg) : SExpr := .field (.variable "d") (nReg (show Fin z.regs.length from r).val)

/-! ### Statements and blocks -/

variable (V : Vertrag z.deklaration)

mutual

def delabS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Stmt z.deklaration V l Γ Λ Λ' → Except String (List SAnw)
  | .assignSlot t f i e _ _ => do
      .ok [.set (.field (.index (.field (.variable (nTab (show Fin z.tabs.length from t).val)) "slots")
        (← delabE z none i)) (nFeld (show Fin _ from f).val)) "=" (← delabE z none e)]
  | .assignGlob g e _ _ => do .ok [.set (.variable (nGlob (show Fin z.globs.length from g).val)) "=" (← delabE z none e)]
  | .publish g e payload _ _ _ => do
      .ok [.emit (.variable (nGlob (show Fin z.globs.length from g).val)) (← delabE z none e) (nutzText z payload)]
  | .ite c t e => do
      let c' ← delabE z none c
      let t' ← delabB t
      let e' ← delabB e
      .ok [.cond c' (.block t' none) [] (if e'.isEmpty then none else some (.block e' none))]
  | .call f args _ _ => do .ok [.call (nFn (show Fin z.fns.length from f).val) (← delabA z args)]
  | .callInd p args _ _ => do
      let as ← delabA z args
      match p with
      | .fnref f _ _ =>
        .ok [.bind false (nZeiger Γ.length) none (.fnref (nFn (show Fin z.fns.length from f).val)),
             .call (nZeiger Γ.length) as]
      | .var x => .ok [.call (nVar (Γ.length - 1 - tiefe x)) as]
      | _ => .error "indirect call through an expression without a spelling"
  | .locks L _ body => do
      .ok [.locks false (.variable (nLock (show Fin z.locks.length from L).val)) (.block (← delabB body) none)]
  | .regWrite r _ e => do .ok [.set (regOrt z r) "=" (← delabE z none e)]
  | .traverse t inv body => do
      let i' ← match inv with
        | .tru => pure none
        | i => do pure (some (← delabE z none i))
      .ok [.each (nVar Γ.length) none "slots" (.variable (nTab (show Fin z.tabs.length from t).val)) "unvisited" ""
        i' (.block (← delabB body) none)]
  | .ret e _ => do .ok [.ret (← delabR z e)]
  | .retWhy r _ => .ok [.ret (some (.why (nGrund V.gruende) (nFall r.val)))]
  | s => .error ("statement without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.cS s))

def delabB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Block z.deklaration V l Γ Λ Λ' → Except String (List SAnw)
  | .nil => .ok []
  | .cons s rest => do .ok ((← delabS s) ++ (← delabB rest))
  | .bind e rest => do .ok (.bind false (nVar Γ.length) none (← delabE z none e) :: (← delabB rest))
  | .bindCall f args _ _ _ rest => do
      .ok (.bind false (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) (← delabA z args)) ::
        (← delabB rest))
  | .bindCallElse f args _ _ _ err rest => do
      let (es, ende) ← delabEnd err
      .ok (.bindElse (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) (← delabA z args))
        (nVar Γ.length) (.block es ende) :: (← delabB rest))
  | .bindCallInd p args _ _ _ rest => do
      let as ← delabA z args
      match p with
      | .fnref f _ _ =>
        .ok (.bind false (nZeiger Γ.length) none (.fnref (nFn (show Fin z.fns.length from f).val)) ::
          .bind false (nVar Γ.length) none (.call (nZeiger Γ.length) as) :: (← delabB rest))
      | .var x => .ok (.bind false (nVar Γ.length) none (.call (nVar (Γ.length - 1 - tiefe x)) as) :: (← delabB rest))
      | _ => .error "indirect call through an expression without a spelling"
  | .regRead r _ rest => do .ok (.bind false (nVar Γ.length) none (regOrt z r) :: (← delabB rest))
  | .regReadElse r _ _ sonst rest => do
      let (es, ende) ← delabEnd sonst
      .ok (.bindElse (nVar Γ.length) none (regOrt z r) (nVar Γ.length) (.block es ende) :: (← delabB rest))
  | .awaits g payload _ _ _ rest => do
      .ok (.await (nVar Γ.length) (.variable (nGlob (show Fin z.globs.length from g).val)) (nutzTextA z payload) ::
        (← delabB rest))
  | b => .error ("block without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.cB b))

def delabEnd {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} :
    Endblock z.deklaration V l Γ Λ → Except String (List SAnw × Option SEnde)
  | .ret e _ => do .ok ([], some (.ret (← delabR z e)))
  | .retWhy r _ => .ok ([], some (.ret (some (.why (nGrund V.gruende) (nFall r.val)))))
  | .cons s rest => do
      let ss ← delabS s
      let (rs, e) ← delabEnd rest
      .ok (ss ++ rs, e)
  | .bind e rest => do
      let x ← delabE z none e
      let (rs, en) ← delabEnd rest
      .ok (.bind false (nVar Γ.length) none x :: rs, en)
  | .bindCall f args _ _ _ rest => do
      let as ← delabA z args
      let (rs, en) ← delabEnd rest
      .ok (.bind false (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) as) :: rs, en)
  | .bindCallElse f args _ _ _ err rest => do
      let as ← delabA z args
      let (es, ee) ← delabEnd err
      let (rs, en) ← delabEnd rest
      .ok (.bindElse (nVar Γ.length) none (.call (nFn (show Fin z.fns.length from f).val) as) (nVar Γ.length)
        (.block es ee) :: rs, en)
  | .regRead r _ rest => do
      let (rs, en) ← delabEnd rest
      .ok (.bind false (nVar Γ.length) none (regOrt z r) :: rs, en)
  | .awaits g payload _ _ _ rest => do
      let (rs, en) ← delabEnd rest
      .ok (.await (nVar Γ.length) (.variable (nGlob (show Fin z.globs.length from g).val)) (nutzTextA z payload) ::
        rs, en)
  | .bindCallInd p args _ _ _ rest => do
      let as ← delabA z args
      let (rs, en) ← delabEnd rest
      match p with
      | .fnref f _ _ =>
        .ok (.bind false (nZeiger Γ.length) none (.fnref (nFn (show Fin z.fns.length from f).val)) ::
          .bind false (nVar Γ.length) none (.call (nZeiger Γ.length) as) :: rs, en)
      | .var x => .ok (.bind false (nVar Γ.length) none (.call (nVar (Γ.length - 1 - tiefe x)) as) :: rs, en)
      | _ => .error "indirect call through an expression without a spelling"
  | e => .error ("end block without a spelling: " ++ String.intercalate " " (Gabbro.Grammatik.Parser.Cover.Mitglieder.cE e))

end

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
  | _ => []

def sperrenB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Block z.deklaration V l Γ Λ Λ' → List z.deklaration.Lock
  | .cons s rest => sperrenS s ++ sperrenB rest
  | .bind _ rest => sperrenB rest
  | .bindCall _ _ _ _ _ rest => sperrenB rest
  | .bindCallElse _ _ _ _ _ err rest => sperrenE err ++ sperrenB rest
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
  | _ => []

end

/-- The parameters: the `j`-th of `np` is `v{np-1-j}` (the variable of depth `j` in the body). -/
def parListe (np : Nat) : Nat → List Ty → Except String (List (String × STyp))
  | _, [] => .ok []
  | j, t :: ts => do .ok ((nVar (np - 1 - j), ← typS t) :: (← parListe np (j + 1) ts))

/-- The result type of a function. -/
def delabRes (f : Fin z.fns.length) : Except String (Option STyp) :=
  match (z.deklaration.signatur f).erg with
  | none => pure none
  | some t => do pure (some (← typS t))

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
  let ps ← parListe np 0 s.params
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
    pure ({ fname := nFeld j, ftyp := ← typS fz.typ, pos := none, bezug := none, wo := none,
            reserviert := false, byOps := false } : SFeld)).mapM id
  if tz.count < 0 then throw "table with a negative count"
  pure (.tableT (nTab t.val) (some (.lit tz.count.toNat)) none none (z.deklaration.geteilt t) [.tSlot fs])

def anfang : Ty → SKonstWert
  | .int lo hi => .one (zahlE (if lo > 0 then lo else if hi < 0 then hi else 0))
  | .bool => .one .fls
  | _ => .one (.lit 0)

def delabGlob (g : Fin z.globs.length) : Except String SItemTief := do
  let gz := z.globs.get g
  let ty ← typS gz.typ
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

/-- The entry of a function the hardware enters. -/
def eintritt (i : Nat) : SItemTief :=
  .entryT { name := "ent" ++ toString i, vektor := some (.lit (32 + i)), regIn := [], regOut := [],
            erhaelt := [], kills := [], perCpu := true, ist := none, dispatch := ["m", nFn i],
            «via» := some "idt", arch := "x86_64", stapel := "stk" ++ toString i, nest := some "never" }

/-- **The delaborator**: a program of the generator as the items of one module. -/
def delab (P : Programm z.deklaration) (ws : List z.deklaration.Fn) : Except String (List SItemTief) := do
  if !z.marken.isEmpty then throw "marks without a spelling"
  if !z.axs.isEmpty then throw "foreign bodies outside the test sets"
  let tabs ← (List.finRange z.tabs.length).mapM (delabTab z)
  let globs ← (List.finRange z.globs.length).mapM (delabGlob z)
  let locks ← (List.finRange z.locks.length).mapM (delabLock z)
  let dev ← delabDev z
  let invs ← (List.finRange z.invs.length).mapM (delabInv z P)
  let fns ← (List.finRange z.fns.length).mapM (delabFn z P (!z.regs.isEmpty))
  let starts := if ws.isEmpty then [] else
    [SItemTief.concT (ws.map fun f => ["m", nFn (show Fin z.fns.length from f).val])]
  let eintritte := ((List.finRange z.fns.length).filter fun f => P.unterbricht f).map fun f => eintritt f.val
  pure [.modT "m" (tabs ++ globs ++ locks ++ dev ++ (gruende z).map grundItem ++ invs ++ fns ++ starts ++ eintritte)]

end Gabbro.Grammatik.Gen.Text
