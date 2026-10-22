/-
  File:      Grammatik/Gen/Text/Invers/Anweisung.lean
  Subject:   THE ELABORATOR INVERTS THE DELABORATOR ON STATEMENTS AND BLOCKS (Tier 2.1, step 2): the flat
             statement list the elaborator builds (`uAnwReihe`, then `uEnde` for the ender) from the printed body
             is the plain data `uOfBl`/`uOfEnd` computes from the model's body itself.

  Fragment of this step: `let` of a number or a truth value, slot and static writes, `if`, `locks`, `traverse`
  (with its invariant), `return` and `return R::C`. Calls, registers and atomics follow.

  The context is `SInv`, against the accessors of the declaration: `EInv`'s scope description, plus the lock
  side (a lock that guards a table is one of the table's required locks, `D.braucht`; every lock held in `Λ`
  is in `ctx.held`), the result kind of the contract `V`, and the reasons.
-/
import Grammatik.Gen.Text.Invers.Ausdruck

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

variable (z : Spez)

abbrev lN (L : z.deklaration.Lock) : Nat := (show Fin z.locks.length from L).val
abbrev rN (r : z.deklaration.Reg) : Nat := (show Fin z.regs.length from r).val

/-- The return value the elaborator reads (`uEnde` on `return v`). -/
def uOfR (art : Nat → UParamArt) {Γ : Ctx} {Λ : List (Res z.deklaration)} :
    {o : Option Ty} → ErgExpr z.deklaration Γ Λ o → Option URet
  | _, .empty => some .empty
  | _, .val (τ := .bool) e => (uOfB z art none e).map .bool
  | _, .val (τ := .int _ _) e => (uOfS z art none e).map .val
  | _, .val _ => none

abbrev fN (f : z.deklaration.Fn) : Nat := (show Fin z.fns.length from f).val

/-- The kind of a value of type `τ` in a scope (a parameter or a binding): a number or a truth value. -/
def artErg : Ty → Option UParamArt
  | .bool => some .bool
  | .int _ _ => some .int
  | _ => none

/-- The arguments the elaborator reads (`uArgs` against the callee's kinds). -/
def uOfArgs (art : Nat → UParamArt) {Γ : Ctx} {Λ : List (Res z.deklaration)} :
    {τs : List Ty} → Args z.deklaration Γ Λ τs → Option (List UArg)
  | _, .nil => some []
  | _, .cons (τ := .bool) e rest => do some (.bval (← uOfB z art none e) :: (← uOfArgs art rest))
  | _, .cons (τ := .int _ _) e rest => do some (.val (← uOfS z art none e) :: (← uOfArgs art rest))
  | _, .cons _ _ => none

variable (V : Vertrag z.deklaration) (gNr : Nat → Nat)

mutual

/-- The statements the elaborator builds for one statement. -/
def uOfSt (art : Nat → UParamArt) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Stmt z.deklaration V l Γ Λ Λ' → Option (List UStmt)
  | .assignSlot t f i e _ _ => do
      let ix ← uOfIdx z art none (tN z t) (z.deklaration.count t) i
      if z.deklaration.typ t f = .bool then
        some [.assignTabB (nTab (tN z t)) (nFeld (show Fin _ from f).val) ix (← uOfB z art none e)]
      else
        some [.assignTab (nTab (tN z t)) (nFeld (show Fin _ from f).val) ix (← uOfS z art none e)]
  | .assignGlob g e _ _ =>
      if z.deklaration.atomar g then none
      else if z.deklaration.gtyp g = .bool then (uOfB z art none e).map fun b => [.assignGlobB (nGlob (gN z g)) b]
      else (uOfS z art none e).map fun u => [.assignGlob (nGlob (gN z g)) u]
  | .ite c t e => do
      some ([.ifBeg (← uOfB z art none c)] ++ (← uOfBl art t) ++ [.ifElse] ++ (← uOfBl art e) ++ [.blkEnd])
  | .locks L _ body => do
      some ([.lockBeg (nLock (lN z L))] ++ (← uOfBl art body) ++ [.blkEnd])
  | .traverse (Γ := Γ) t inv body => do
      some ([.loopBeg (nVar Γ.length) (nTab (tN z t)) (← uOfB z art none inv)] ++
        (← uOfBl (artAuf (.index (tN z t)) art) body) ++ [.blkEnd])
  | .ret e _ => (uOfR z art e).map fun r => [.ret r]
  | .retWhy r _ => some [.ret (.why r.val)]
  | .regWrite r _ e =>
      if z.deklaration.rtyp r = .bool then (uOfB z art none e).map fun b => [.regWriteB "Dev" (nReg (rN z r)) b]
      else (uOfS z art none e).map fun u => [.regWrite "Dev" (nReg (rN z r)) u]
  | .publish g e _ _ _ _ =>
      if z.deklaration.atomar g then
        if z.deklaration.gtyp g = .bool then (uOfB z art none e).map fun b => [.storeAtomB (nGlob (gN z g)) b]
        else (uOfS z art none e).map fun u => [.storeAtom (nGlob (gN z g)) u]
      else none
  | .call f args _ _ => (uOfArgs z art args).map fun xs => [.call (nFn (fN z f)) xs]
  | .callInd (Γ := Γ) (n := n) p args _ _ =>
      match p with
      | .fnref f _ _ => if n = z.deklaration.sig f then (uOfArgs z art args).map fun xs =>
        [.bindFnref (nZeiger Γ.length) (nFn (fN z f)) n, .callInd (nZeiger Γ.length) (nFn (fN z f)) xs]
        else none
      | _ => none
  | _ => none

/-- The statements the elaborator builds for a block. -/
def uOfBl (art : Nat → UParamArt) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} :
    Block z.deklaration V l Γ Λ Λ' → Option (List UStmt)
  | .nil => some []
  | .cons s rest => do some ((← uOfSt art s) ++ (← uOfBl art rest))
  | .bind (Γ := Γ) (τ := τ) e rest =>
      if τ = .bool then do
        some (.bindB (nVar Γ.length) (← uOfB z art none e) :: (← uOfBl (artAuf .bool art) rest))
      else do
        some (.bind (nVar Γ.length) none (← uOfS z art none e) :: (← uOfBl (artAuf .int art) rest))
  | .regRead (Γ := Γ) r _ rest => do
      let a ← artErg (z.deklaration.rtyp r)
      some (.regRead (nVar Γ.length) "Dev" (nReg (rN z r)) :: (← uOfBl (artAuf a art) rest))
  | .awaits (Γ := Γ) g _ _ _ _ rest => do
      let a ← artErg (z.deklaration.gtyp g)
      some (.awaitBind (nVar Γ.length) (nGlob (gN z g)) :: (← uOfBl (artAuf a art) rest))
  | .bindCall (Γ := Γ) (τ := τ) f args _ _ _ rest => do
      let a ← artErg τ
      some (.bindCall (nVar Γ.length) (nFn (fN z f)) (← uOfArgs z art args) :: (← uOfBl (artAuf a art) rest))
  | .bindCallElse (Γ := Γ) (τ := τ) f args _ _ _ err rest => do
      let a ← artErg τ
      let xs ← uOfArgs z art args
      let (es, er) ← uOfEnd (artAuf (.why (gNr (z.deklaration.gruende f))) art) err
      some ([.bindElse (nVar Γ.length) (nFn (fN z f)) xs (nVar Γ.length)] ++ es ++ [.ret er, .blkEnd] ++
        (← uOfBl (artAuf a art) rest))
  | .bindCallInd (Γ := Γ) (n := n) (τ := τ) p args _ _ _ rest => do
      let a ← artErg τ
      let xs ← uOfArgs z art args
      let rs ← uOfBl (artAuf a art) rest
      match p with
      | .fnref f _ _ =>
        if n = z.deklaration.sig f then
          some ([.bindFnref (nZeiger Γ.length) (nFn (fN z f)) n,
            .bindCallInd (nVar Γ.length) (nZeiger Γ.length) (nFn (fN z f)) xs] ++ rs)
        else none
      | _ => none
  | _ => none

/-- The statements and the trailing return the elaborator builds for an end block. -/
def uOfEnd (art : Nat → UParamArt) {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} :
    Endblock z.deklaration V l Γ Λ → Option (List UStmt × URet)
  | .ret e _ => (uOfR z art e).map fun r => ([], r)
  | .retWhy r _ => some ([], .why r.val)
  | .cons s rest => do
      let ss ← uOfSt art s
      let (rs, r) ← uOfEnd art rest
      some (ss ++ rs, r)
  | .bind (Γ := Γ) (τ := τ) e rest =>
      if τ = .bool then do
        let b ← uOfB z art none e
        let (rs, r) ← uOfEnd (artAuf .bool art) rest
        some (.bindB (nVar Γ.length) b :: rs, r)
      else do
        let u ← uOfS z art none e
        let (rs, r) ← uOfEnd (artAuf .int art) rest
        some (.bind (nVar Γ.length) none u :: rs, r)
  | .bindCall (Γ := Γ) (τ := τ) f args _ _ _ rest => do
      let a ← artErg τ
      let xs ← uOfArgs z art args
      let (rs, r) ← uOfEnd (artAuf a art) rest
      some (.bindCall (nVar Γ.length) (nFn (fN z f)) xs :: rs, r)
  | .bindCallElse (Γ := Γ) (τ := τ) f args _ _ _ err rest => do
      let a ← artErg τ
      let xs ← uOfArgs z art args
      let (es, er) ← uOfEnd (artAuf (.why (gNr (z.deklaration.gruende f))) art) err
      let (rs, r) ← uOfEnd (artAuf a art) rest
      some ([.bindElse (nVar Γ.length) (nFn (fN z f)) xs (nVar Γ.length)] ++ es ++ [.ret er, .blkEnd] ++ rs, r)
  | _ => none

end

/-- **The statement context**, against the accessors of the declaration and the contract `V`. -/
structure SInv (ctx : UCtx) (Γ : Ctx) (Λ : List (Res z.deklaration)) (art : Nat → UParamArt) : Prop where
  var : ∀ d, d < Γ.length → ∃ j, uParamNr ctx (nVar (Γ.length - 1 - d)) = .ok j ∧ uArtBei ctx.kinds j = .ok (art d)
  namen : ∀ n ∈ ctx.names, RumpfName n
  lits : ctx.lits = []
  glob : ∀ g : z.deklaration.Glob, ∃ gl, ctx.globs.find? (fun x => strEq x.name (nGlob (gN z g))) = some gl ∧
    (gl.ty = .bool ↔ z.deklaration.gtyp g = .bool) ∧ gl.var = !z.deklaration.atomar g ∧
    gl.atomic = z.deklaration.atomar g ∧ gl.nutzlast = (z.deklaration.nutzlast g).map fun h => nGlob (gN z h)
  tab : ∀ t : z.deklaration.Tab, ∃ tb, ctx.tabs.find? (fun x => strEq x.name (nTab (tN z t))) = some tb ∧
    tb.name = nTab (tN z t) ∧ tb.arena = false ∧ tb.count = z.deklaration.count t ∧ tb.opts = [] ∧
    (∀ f : z.deklaration.Feld t, tb.cols.any (fun (g, _) => strEq g (nFeld (show Fin _ from f).val)) = true) ∧
    (∀ f : z.deklaration.Feld t,
      tb.bools.any (fun g => strEq g (nFeld (show Fin _ from f).val)) = decide (z.deklaration.typ t f = .bool))
  tabNr : ∀ t : z.deklaration.Tab, uTabNrAux ctx.tabs 0 (nTab (tN z t)) = .ok (tN z t, z.deklaration.count t)
  tabIdx : ∀ t : z.deklaration.Tab, ctx.tabs.findIdx? (fun x => strEq x.name (nTab (tN z t))) = some (tN z t)
  tabNamen : ∀ tb ∈ ctx.tabs, ∃ i, tb.name = nTab i
  lockFind : ∀ L : z.deklaration.Lock, ∃ lk, ctx.locks.find? (fun x => strEq x.name (nLock (lN z L))) = some lk
  lockGuard : ∀ lk ∈ ctx.locks, ∀ t : z.deklaration.Tab, lk.guard.any (strEq · (nTab (tN z t))) = true →
    ∃ L, lk.name = nLock (lN z L) ∧ Sum.inl L ∈ z.deklaration.braucht t
  held : ∀ L : z.deklaration.Lock, Res.held L ∈ Λ → ctx.held.any (strEq · (nLock (lN z L))) = true
  muts : ctx.muts = []
  sums : ctx.sums = []
  resOpt : ctx.resOpt = none
  resSum : ctx.resSum = none
  resWhy : ctx.resWhy = none
  ergNone : V.erg = none → ctx.res = none ∧ ctx.resBool = false
  ergBool : V.erg = some .bool → ctx.res = none ∧ ctx.resBool = true
  ergInt : ∀ lo hi, V.erg = some (.int lo hi) → ctx.res.isSome ∧ ctx.resBool = false
  kanal0 : V.gruende = 0 → ctx.kanal = none
  griff : ∀ r : z.deklaration.Reg, ctx.griffe.find? (fun p => strEq p.1 "d") = some ("d", "Dev")
  reg : ∀ r : z.deklaration.Reg, ∃ g, ctx.regs.find? (fun g => strEq g.dev "Dev" && strEq g.name (nReg (rN z r))) = some g ∧
    g.dev = "Dev" ∧ g.name = nReg (rN z r) ∧ g.pruefung = none ∧ some g.art = artErg (z.deklaration.rtyp r) ∧
    (g.bool = true ↔ z.deklaration.rtyp r = .bool)
  kanal : V.gruende ≠ 0 → ∃ k w, ctx.kanal = some (k, V.gruende) ∧
    ctx.whys.findIdx? (fun x => strEq x.name (nGrund V.gruende)) = some k ∧ ctx.whys[k]? = some w ∧
    ∀ r, r < V.gruende → w.cases.findIdx? (strEq · (nFall r)) = some r
  /-- every function's own signature number (its head number) lies below the pointer-type base -/
  zb : ∀ f : z.deklaration.Fn, z.deklaration.sig f < ctx.zeigerBasis

variable {z V}

theorem SInv.einv {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) : EInv z ctx Γ Λ art where
  var d hd _ := H.var d hd
  namen := H.namen
  lits := H.lits
  glob g := by
    obtain ⟨gl, h1, h2, _⟩ := H.glob g
    exact ⟨gl, h1, h2⟩
  tab := H.tab
  tabNr := H.tabNr
  waechter t hL := by
    have hall : ((ctx.locks.filterMap (fun l => if l.guard.any (strEq · (nTab (tN z t))) then some l.name else none)).all
        (fun b => ctx.held.any (strEq · b))) = true := by
      simp only [List.all_eq_true, List.mem_filterMap]
      rintro b ⟨lk, hlk, hb⟩
      split at hb
      · rename_i hg
        simp only [Option.some.injEq] at hb
        subst hb
        obtain ⟨L, hn, hL'⟩ := H.lockGuard lk hlk t hg
        rw [hn]
        exact H.held L (hL _ hL')
      · simp at hb
    simp only [uHaeltWaechter, hall, ite_true]

/-- A plain statement (`uAnw1`) at the head of a run. -/
theorem anw_set (tabs : List UTab) (koepfe : List UFnKopf) (f : Nat) (ctx : UCtx) (ziel : SExpr) (op : String)
    (w : SExpr) (rest : List SAnw) :
    uAnwReihe tabs koepfe (f + 1) ctx (.set ziel op w :: rest) =
      match uAnw1 ctx tabs koepfe (.set ziel op w) with
      | .error e => .error e
      | .ok st =>
        match uAnwReihe tabs koepfe f ctx rest with
        | .error e => .error e
        | .ok (xs, cE) => .ok (st :: xs, cE) := by
  rw [uAnwReihe] <;> first | rfl | (intros; simp_all)

/-- A slot write `T.slots[i].f = e;`. -/
theorem anw1_slot {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) (t : z.deklaration.Tab)
    (f : z.deklaration.Feld t) (i' w : SExpr) (ix : UIdx) (hi : uIndex ctx (nTab (tN z t)) (tN z t) i' = .ok ix)
    (hL : darf z.deklaration t Λ) :
    (z.deklaration.typ t f = .bool → ∀ v, uBool ctx w = .ok v →
      uAnw1 ctx tabs koepfe (.set (slotS (nTab (tN z t)) (nFeld (show Fin _ from f).val) i') "=" w) =
        .ok (.assignTabB (nTab (tN z t)) (nFeld (show Fin _ from f).val) ix v)) ∧
    (z.deklaration.typ t f ≠ .bool → ∀ v, uWertBody ctx w = .ok v →
      uAnw1 ctx tabs koepfe (.set (slotS (nTab (tN z t)) (nFeld (show Fin _ from f).val) i') "=" w) =
        .ok (.assignTab (nTab (tN z t)) (nFeld (show Fin _ from f).val) ix v)) := by
  have hz := zugriff_slot H.einv t f i' ix hi hL
  have hs : strEq "=" "=" = true := by decide
  simp only [slotS] at hz
  refine ⟨fun hb v hw => ?_, fun hb v hw => ?_⟩ <;>
  · simp only [uAnw1, uSetze, hs, ite_true, slotS, uRegOrt, uSetzePlatz, hz, H.einv.optFeld t f,
      H.einv.boolFeld t f, Option.isSome_none, Bool.false_eq_true, ite_false, hb, hw, decide_true, decide_false]

/-- A static write `g = e;` at a static that is no atomic. -/
theorem anw1_glob {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) (g : z.deklaration.Glob)
    (ha : z.deklaration.atomar g = false) (w : SExpr) :
    (z.deklaration.gtyp g = .bool → ∀ v, uBool ctx w = .ok v →
      uAnw1 ctx tabs koepfe (.set (.variable (nGlob (gN z g))) "=" w) = .ok (.assignGlobB (nGlob (gN z g)) v)) ∧
    (z.deklaration.gtyp g ≠ .bool → ∀ v, uWertBody ctx w = .ok v →
      uAnw1 ctx tabs koepfe (.set (.variable (nGlob (gN z g))) "=" w) = .ok (.assignGlob (nGlob (gN z g)) v)) := by
  obtain ⟨gl, hf, hb, hv, hat, _⟩ := H.glob g
  have hs : strEq "=" "=" = true := by decide
  refine ⟨fun hg v hw => ?_, fun hg v hw => ?_⟩
  · have : gl.ty = .bool := hb.2 hg
    simp only [uAnw1, uRegOrt, uSetze, hs, ite_true, H.muts, List.any_nil, Bool.false_eq_true, ite_false,
      uSetzePlatz, uZugriff, uGlobSchreib, hf, hv, hat, ha, Bool.not_true, Bool.not_false, this, hw]
  · cases h : gl.ty with
    | bool => exact absurd (hb.1 h) hg
    | int _ _ =>
      simp only [uAnw1, uRegOrt, uSetze, hs, ite_true, H.muts, List.any_nil, Bool.false_eq_true, ite_false,
        uSetzePlatz, uZugriff, uGlobSchreib, hf, hv, hat, ha, Bool.not_true, Bool.not_false, h, hw]

/-! ### The run reader, one head at a time -/

section Reihe
variable (tabs : List UTab) (koepfe : List UFnKopf)

theorem reihe_nil (f : Nat) (ctx : UCtx) : uAnwReihe tabs koepfe (f + 1) ctx [] = .ok ([], ctx) := by
  rw [uAnwReihe]

theorem reihe_anw1 (f : Nat) (ctx : UCtx) (ziel w : SExpr) (rest : List SAnw) (st : UStmt) (xs : List UStmt)
    (cE : UCtx) (h1 : uAnw1 ctx tabs koepfe (.set ziel "=" w) = .ok st)
    (h2 : uAnwReihe tabs koepfe f ctx rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.set ziel "=" w :: rest) = .ok (st :: xs, cE) := by
  rw [anw_set, h1]
  simp only [h2]

theorem reihe_bind (f : Nat) (ctx ctx' : UCtx) (x : String) (w : SExpr) (rest : List SAnw) (st : UStmt)
    (xs : List UStmt) (cE : UCtx) (h1 : uBindWert ctx tabs koepfe false x none w = .ok (st, ctx'))
    (h2 : uAnwReihe tabs koepfe f ctx' rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.bind false x none w :: rest) = .ok (st :: xs, cE) := by
  rw [uAnwReihe]
  simp only [h1, h2]

theorem reihe_ret (f : Nat) (ctx : UCtx) (v : Option SExpr) (rest : List SAnw) (r : URet) (xs : List UStmt)
    (cE : UCtx) (h1 : uEnde ctx (some (.ret v)) = .ok r) (h2 : uAnwReihe tabs koepfe f ctx rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.ret v :: rest) = .ok (.ret r :: xs, cE) := by
  rw [uAnwReihe] <;> first | (simp only [h1, h2]) | (intros; simp_all)

theorem reihe_locks (f : Nat) (ctx : UCtx) (L : String) (ss rest : List SAnw) (lk : ULock) (body xs : List UStmt)
    (cB cE : UCtx) (hl : ctx.locks.find? (fun x => strEq x.name L) = some lk)
    (h1 : uAnwReihe tabs koepfe f { ctx with held := L :: ctx.held } ss = .ok (body, cB))
    (h2 : uAnwReihe tabs koepfe f ctx rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.locks false (.variable L) (.block ss none) :: rest) =
      .ok ([.lockBeg L] ++ body ++ [.blkEnd] ++ xs, cE) := by
  rw [uAnwReihe] <;> first | (simp only [hl, h1, h2, Bool.false_eq_true, ite_false]) | (intros; simp_all)

theorem reihe_cond (f : Nat) (ctx : UCtx) (c : SExpr) (ss : List SAnw) (els : Option SAnw) (rest : List SAnw)
    (cv : UEns) (body elseS xs : List UStmt) (cB cE : UCtx) (hc : uBool ctx c = .ok cv)
    (h1 : uAnwReihe tabs koepfe f ctx ss = .ok (body, cB))
    (hE : (els = none ∧ elseS = []) ∨ ∃ ss2 c2, els = some (.block ss2 none) ∧ uAnwReihe tabs koepfe f ctx ss2 = .ok (elseS, c2))
    (h2 : uAnwReihe tabs koepfe f ctx rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.cond c (.block ss none) [] els :: rest) =
      .ok ([.ifBeg cv] ++ body ++ [.ifElse] ++ elseS ++ [.blkEnd] ++ xs, cE) := by
  rcases hE with ⟨rfl, rfl⟩ | ⟨ss2, c2, rfl, he⟩
  · rw [uAnwReihe] <;> first | (simp [hc, h1, h2, uEndeStmt]) | (intros; simp_all)
  · rw [uAnwReihe] <;> first | (simp [hc, h1, h2, he, uEndeStmt]) | (intros; simp_all)

theorem reihe_each (f : Nat) (ctx ctxS : UCtx) (bnd : String) (s : SExpr) (inv : Option SExpr) (ss rest : List SAnw)
    (tab : String) (iv : UEns) (body xs : List UStmt) (cB cE : UCtx)
    (hk : uSchleifenKopf ctx bnd none "slots" s "unvisited" inv = .ok (tab, iv, ctxS))
    (h1 : uAnwReihe tabs koepfe f ctxS ss = .ok (body, cB))
    (h2 : uAnwReihe tabs koepfe f ctx rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.each bnd none "slots" s "unvisited" "" inv (.block ss none) :: rest) =
      .ok ([.loopBeg bnd tab iv] ++ body ++ [.blkEnd] ++ xs, cE) := by
  rw [uAnwReihe] <;> first | (simp [hk, h1, h2, uEndeStmt]) | (intros; simp_all)

end Reihe

/-! ### The context under a binder and under a lock -/

/-- The scope after a binder `x` of kind `a` (the shape every binding of the elaborator has). -/
def ctxMit (ctx : UCtx) (x : String) (a : UParamArt) (ty : Ty) (b : Nat) (ms ls : List String) : UCtx :=
  { ctx with names := x :: ctx.names, kinds := a :: ctx.kinds, types := ty :: ctx.types, bits := b :: ctx.bits,
             muts := ms, loops := ls }

theorem SInv.push {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (τ : Ty) (a : UParamArt) (ty : Ty) (b : Nat) (ms ls : List String) (hms : ms = []) :
    SInv z V (ctxMit ctx (nVar Γ.length) a ty b ms ls) (τ :: Γ) Λ (artAuf a art) where
  var d hd := by
    cases d with
    | zero =>
      refine ⟨0, ?_, rfl⟩
      simp [uParamNr, ctxMit, uParamNrAux]
    | succ d =>
      simp only [List.length_cons] at hd
      obtain ⟨j, hj, ha⟩ := H.var d (by omega)
      refine ⟨j + 1, ?_, ha⟩
      have hne : strEq (nVar Γ.length) (nVar (Γ.length + 1 - 1 - (d + 1))) = false := by
        simp only [strEq_nVar, beq_eq_false_iff_ne]; omega
      simp only [uParamNr, ctxMit, List.length_cons, uParamNrAux, hne, Bool.false_eq_true, ite_false]
      have : Γ.length + 1 - 1 - (d + 1) = Γ.length - 1 - d := by omega
      rw [this]
      exact uParamNrAux_succ _ 0 _ j hj
  namen n hn := by
    simp only [ctxMit, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact Or.inl ⟨_, rfl⟩
    · exact H.namen n hn
  lits := H.lits
  glob := H.glob
  tab := H.tab
  tabNr := H.tabNr
  tabIdx := H.tabIdx
  tabNamen := H.tabNamen
  lockFind := H.lockFind
  lockGuard := H.lockGuard
  held := H.held
  muts := hms
  sums := H.sums
  resOpt := H.resOpt
  resSum := H.resSum
  resWhy := H.resWhy
  ergNone := H.ergNone
  ergBool := H.ergBool
  ergInt := H.ergInt
  kanal0 := H.kanal0
  griff := H.griff
  reg := H.reg
  kanal := H.kanal
  zb := H.zb

theorem SInv.lock {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (L : z.deklaration.Lock) :
    SInv z V { ctx with held := nLock (lN z L) :: ctx.held } Γ (.held L :: Λ) art where
  var := H.var
  namen := H.namen
  lits := H.lits
  glob := H.glob
  tab := H.tab
  tabNr := H.tabNr
  tabIdx := H.tabIdx
  tabNamen := H.tabNamen
  lockFind := H.lockFind
  lockGuard := H.lockGuard
  held M hM := by
    simp only [List.mem_cons] at hM
    rcases hM with hM | hM
    · cases hM; simp
    · simp only [List.any_cons, H.held M hM, Bool.or_true]
  muts := H.muts
  sums := H.sums
  resOpt := H.resOpt
  resSum := H.resSum
  resWhy := H.resWhy
  ergNone := H.ergNone
  ergBool := H.ergBool
  ergInt := H.ergInt
  kanal0 := H.kanal0
  griff := H.griff
  reg := H.reg
  kanal := H.kanal
  zb := H.zb

/-! ### Values of a `let`: a truth value is never read as a number -/

theorem wert_fehler_blatt {ctx : UCtx} (s : SExpr) (hz : ∃ e, uZugriff ctx s = .error e) (hg : uGrenzwort ctx s = none)
    (h1 : ∀ v, s ≠ .lit v) (h2 : ∀ p, s ≠ .variable p) : ∃ e, uWertBlatt ctx s = .error e := by
  obtain ⟨e, he⟩ := hz
  cases s with
  | lit v => exact absurd rfl (h1 v)
  | «variable» p => exact absurd rfl (h2 p)
  | _ => simp only [uWertBlatt, hg, he]; exact ⟨_, rfl⟩

theorem wert_bin_fehler (ctx : UCtx) (op : String) (a b : SExpr)
    (hop : op = "<" ∨ op = "<=" ∨ op = "==" ∨ op = "&&" ∨ op = "||") : ∃ e, uWertBody ctx (.bin op a b) = .error e := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, by simp [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff, strEq_eq]; rfl⟩

/-- **A printed truth value is no number**: `uWertBody` refuses it (so `let x = p;` binds a truth value). -/
theorem wert_bool_fehler {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : UEns)
    (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) : ∃ err, uWertBody ctx s = .error err := by
  cases e with
  | tru =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff]
  | fls =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i h; simp at h
    · rename_i hk
      obtain ⟨j, hj, ha⟩ := H.var (tiefe x) (tiefe_lt x) (by simp)
      split at hu
      · rename_i hb
        simp [hk, uWertBody, uRechne, uWertBlatt, hj, ha, hb]
      · simp at hu
  | glob g hL =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i hg
      obtain ⟨err, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
      obtain ⟨gl, hf, hb⟩ := H.glob g
      have : gl.ty = .bool := hb.2 hg
      simp [uWertBody, uRechne, uWertBlatt, he, H.lits, uGlobLies, hf, this]
    · simp at hu
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z none i with
    | error _ => simp [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfB] at hu
      split at hu
      · rename_i hb
        cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i with
        | none => simp [hx] at hu
        | some ix =>
          have hz := zugriff_slot H t f i' ix (idx_ok H t (sizeOf i + 1) i (by omega) i' ix hi hx) hL
          simp only [slotS] at hz
          simp [uWertBody, uRechne, uWertBlatt, uGrenzwort, hz, H.boolFeld t f, hb]
      · simp at hu
  | lt a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp)
  | le a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp)
  | eq a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp)
  | and a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp)
  | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp)
  | not a =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;>
      simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact ⟨_, by simp [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff]; rfl⟩
  | forallSlots t body hL | existsSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z none body <;>
      simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact ⟨_, by simp [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff]; rfl⟩
  | _ => simp [uOfB] at hu

/-- The head of a printed value: no register place, no function reference, no call. -/
def kopfOk : SExpr → Bool
  | .field (.variable _) _ => false
  | .field (.field _ _) _ => false
  | .fnref _ => false
  | .call _ _ => false
  | .why _ _ => false
  | _ => true

theorem kopfOk_delab {Γ : Ctx} {Λ : List (Res z.deklaration)} (art : Nat → UParamArt) (k : Option Nat) (n : Nat) :
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ (s : SExpr), delabE z k e = .ok s →
      ((uOfS z art k e).isSome = true ∨ (uOfB z art k e).isSome = true) → kopfOk s = true := by
  induction n with
  | zero => intro _ _ h; omega
  | succ n ih =>
  intro τ e hn s hd hf
  cases e with
  | lit n => simp only [delabE, Except.ok.injEq] at hd; subst hd; simp only [zahlE]; split <;> rfl
  | tru | fls => simp only [delabE, Except.ok.injEq] at hd; subst hd; rfl
  | var x => simp only [delabE, Except.ok.injEq] at hd; subst hd; split <;> rfl
  | glob g hL => simp only [delabE, Except.ok.injEq] at hd; subst hd; rfl
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z k i <;> simp only [hi, bind, Except.bind, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | fnref f m h => simp [uOfS, uOfB] at hf
  | widen h1 h2 e =>
    simp only [delabE] at hd
    simp only [uOfS, uOfB] at hf
    exact ih e (by simp at hn; omega) s hd (Or.inl (by simpa using hf))
  | add a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | sub a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | mul a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | lt a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | le a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | eq a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | and a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | neg a | not a =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; (try split) <;> rfl
  | forallSlots t body hL | existsSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z k body <;> simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | why m r => simp [uOfS, uOfB] at hf
  | div _ _ a b | rem _ _ a b | sdiv _ a b | srem _ a b | band _ _ a b | bor _ _ _ _ _ a b | bxor _ _ _ _ _ a b
  | shl _ _ _ _ _ a b | shr _ _ _ _ _ a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | oldG g hL => simp only [delabE, Except.ok.injEq] at hd; subst hd; rfl
  | oldS t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z k i <;> simp only [hi, bind, Except.bind, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | none m => simp [uOfS, uOfB] at hf
  | some e => simp [uOfS, uOfB] at hf
  | _ => simp [delabE] at hd

theorem regOrt_kopfOk (ctx : UCtx) (s : SExpr) (h : kopfOk s = true) : uRegOrt ctx s = none := by
  cases s with
  | field a r =>
    cases a with
    | «variable» _ => simp [kopfOk] at h
    | field _ _ => simp [kopfOk] at h
    | _ => simp [uRegOrt]
  | _ => simp [uRegOrt]

/-- A `let` without a type of a printed value is the general value reader. -/
theorem bindWert_allg (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (x : String) (s : SExpr)
    (h : kopfOk s = true) : uBindWert ctx tabs koepfe false x none s = uBindWertAllg ctx false x none s := by
  have hr := regOrt_kopfOk ctx s h
  cases s with
  | fnref _ => simp [kopfOk] at h
  | call _ _ => simp [kopfOk] at h
  | why _ _ => simp [kopfOk] at h
  | _ => simp only [uBindWert, hr]

/-- `let v = e;` of a number. -/
theorem bindWert_int {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) {τ : Ty} (e : Expr z.deklaration Γ Λ τ)
    (s : SExpr) (u : USide) (hd : delabE z none e = .ok s) (hu : uOfS z art none e = some u) :
    uBindWert ctx tabs koepfe false (nVar Γ.length) none s =
      .ok (.bind (nVar Γ.length) none u, ctxMit ctx (nVar Γ.length) .int (.int 0 0) 0 [] ctx.loops) := by
  rw [bindWert_allg ctx tabs koepfe _ s (kopfOk_delab art none (sizeOf e + 1) e (by omega) s hd (Or.inl (by simp [hu])))]
  simp only [uBindWertAllg, wert_ok H.einv e s u hd hu, uBindKopf, H.muts, List.filter_nil, Bool.false_eq_true,
    ite_false]
  rfl

/-- `let v = p;` of a truth value. -/
theorem bindWert_bool {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) {τ : Ty} (e : Expr z.deklaration Γ Λ τ)
    (s : SExpr) (u : UEns) (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) :
    uBindWert ctx tabs koepfe false (nVar Γ.length) none s =
      .ok (.bindB (nVar Γ.length) u, ctxMit ctx (nVar Γ.length) .bool .bool 0 [] ctx.loops) := by
  rw [bindWert_allg ctx tabs koepfe _ s (kopfOk_delab art none (sizeOf e + 1) e (by omega) s hd (Or.inr (by simp [hu])))]
  obtain ⟨err, he⟩ := wert_bool_fehler H.einv e s u hd hu
  simp only [uBindWertAllg, he, bool_ok H.einv e s u hd hu, H.muts, List.filter_nil]
  rfl

/-- The header of a printed `traverse`. -/
theorem schleifenKopf_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (t : z.deklaration.Tab) (inv : Option SExpr) (iv : UEns)
    (hi : (inv = none ∧ iv = .tru) ∨ ∃ p, inv = some p ∧ uBool ctx p = .ok iv) :
    ∃ cnt, uSchleifenKopf ctx (nVar Γ.length) none "slots" (.variable (nTab (tN z t))) "unvisited" inv =
      .ok (nTab (tN z t), iv, ctxMit ctx (nVar Γ.length) (.index (tN z t)) (.index cnt) 0 ctx.muts
        (nVar Γ.length :: ctx.loops)) := by
  have h1 : strEq "slots" "slots" = true := by decide
  have h2 : strEq "unvisited" "unvisited" = true := by decide
  rcases hi with ⟨rfl, rfl⟩ | ⟨p, rfl, hp⟩
  · exact ⟨_, by simp only [uSchleifenKopf, Option.isSome_none, h1, h2, H.tabIdx t]; rfl⟩
  · exact ⟨_, by simp only [uSchleifenKopf, Option.isSome_none, h1, h2, H.tabIdx t, hp]; rfl⟩

/-- **`return v;`** -/
theorem ende_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) {o : Option Ty} (ho : o = V.erg) (e : ErgExpr z.deklaration Γ Λ o)
    (v : Option SExpr) (r : URet) (hd : delabR z e = .ok v) (hu : uOfR z art e = some r) :
    uEnde ctx (some (.ret v)) = .ok r := by
  cases e with
  | empty =>
    simp only [delabR, Except.ok.injEq] at hd; subst hd
    simp only [uOfR, Option.some.injEq] at hu; subst hu
    obtain ⟨h1, h2⟩ := H.ergNone ho.symm
    simp [uEnde, h1, h2, H.resOpt, H.resSum, H.resWhy]
  | val e =>
    simp only [delabR] at hd
    cases hs : delabE z none e with
    | error _ => simp [hs, bind, Except.bind] at hd
    | ok s =>
      simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      rename_i τ
      cases τ with
      | bool =>
        simp only [uOfR] at hu
        cases hb : uOfB z art none e with
        | none => simp [hb] at hu
        | some b =>
          simp only [hb, Option.map_some, Option.some.injEq] at hu; subst hu
          have hk := kopfOk_delab art none (sizeOf e + 1) e (by omega) s hs (Or.inr (by simp [hb]))
          obtain ⟨h1, h2⟩ := H.ergBool ho.symm
          have hw : ∀ a c, s ≠ .why a c := fun a c h => by subst h; simp [kopfOk] at hk
          cases s with
          | why a c => exact absurd rfl (hw a c)
          | _ => simp [uEnde, h1, h2, H.resOpt, H.resSum, H.resWhy, bool_ok H.einv e _ b hs hb]
      | int lo hi =>
        simp only [uOfR] at hu
        cases hb : uOfS z art none e with
        | none => simp [hb] at hu
        | some b =>
          simp only [hb, Option.map_some, Option.some.injEq] at hu; subst hu
          have hk := kopfOk_delab art none (sizeOf e + 1) e (by omega) s hs (Or.inl (by simp [hb]))
          obtain ⟨h1, h2⟩ := H.ergInt lo hi ho.symm
          have hw : ∀ a c, s ≠ .why a c := fun a c h => by subst h; simp [kopfOk] at hk
          obtain ⟨rg, hrg⟩ := Option.isSome_iff_exists.1 h1
          cases s with
          | why a c => exact absurd rfl (hw a c)
          | _ => simp [uEnde, hrg, h2, H.resOpt, H.resSum, H.resWhy, wert_ok H.einv e _ b hs hb]
      | _ => simp [uOfR] at hu

/-- **`return R::C;`** -/
theorem ende_why {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (r : Fin V.gruende) :
    uEnde ctx (some (.ret (some (.why (nGrund V.gruende) (nFall r.val))))) = .ok (.why r.val) := by
  obtain ⟨k, w, hk, hj, hw, hc⟩ := H.kanal (by have := r.isLt; omega)
  simp [uEnde, uEndeKanal, H.resWhy, hk, hj, hw, hc r.val r.isLt]

end Gabbro.Grammatik.Gen.Text