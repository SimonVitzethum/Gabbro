/-
  File:      Grammatik/Korrespondenz.lean
  Subject:   T2 GENERAL: correspondence certificates as FORM FAMILIES.

  `Korrespondenz104.lean` certifies ONE program: its rows are cut to 104's
  exact shapes. Here a row is a member of a form family over the existing
  T4 judgements (`CFormenI.lean`, `CFormenM.lean`): slot store of any
  expression, plain and compound local assignment, `let`, `if`/`else`,
  direct call of any function with parameter arguments, `return` of an
  expression, `(void)x`, and the `for`-over-`traverse` form
  (`scorr_traverse`). `gbodyOk` is the decidable validity check; the
  flagship soundness theorem `gcert_sound` builds `EndSem` from the T4
  lemmas (nothing re-proved). `Korrespondenz104.lean` keeps building
  unchanged.
-/
import Grammatik.CFormenZeuge

namespace Gabbro.Grammatik

/-- One emitted-C statement as certificate data: a member of a form
    family over the T4 judgements. Expressions ride along as `CX` (plain
    data); their `ExprCorr` (from the T4 expression lemmas) is a premise
    of the row derivation (`RBlock`/`REnd`), not data. -/
inductive GRow where
  | void (x : Nat)
  | storeSlot (kp : Nat) (ci : CX) (n ss off : Nat) (tc : CTy) (ce : CX)
  | storeNamed (tn : Nat) (ci : CX) (n ss off : Nat) (tc : CTy) (ce : CX)
  | storeGlob (g : Nat) (tc : CTy) (ce : CX)
  | setVar (x : Nat) (tc : CTy) (ce : CX)
  | setOp (x : Nat) (tc : CTy) (op : CBinOp) (t : CIT) (ce : CX)
  | bindLet (x : Nat) (tc : CTy) (ce : CX)
  | ite (cc : CX) (t e : List GRow)
  | call (fc : Nat) (cargs : List CX) (dst : Option (Nat × CTy))
  | ret (cr : Option (CTy × CX))
  | forTrav (x : Nat) (t : CIT) (hi : CX) (body : List GRow) (m : Nat)
  /-- `(*(volatile uintN_t *)(cp)) = e;` -- a store to a DEVICE REGISTER
      (H10, `CFormenH.lean`). `cp` is the register's address expression;
      which register it is, is decided against the certificate's device
      table (`GerTafel`, KorrespondenzAllg.lean), never guessed. -/
  | storeReg (cp : CX) (w : CWidth) (ce : CX)
  /-- `T x = (*(volatile uintN_t *)(cp));` -- a DEVICE REGISTER READ (H9),
      binding the machine's answer to a fresh C local. -/
  | loadReg (x : Nat) (tc : CTy) (cp : CX) (w : CWidth)
  /-- `T x = (*(volatile uintN_t *)(cp)); if (!(c)) { return e; }` -- a
      register read whose declared promise is CHECKED in the program
      (`let x = R else (e) { … }`). A broken device promise is a BRANCH
      here, not a stop. -/
  | loadRegElse (x : Nat) (tc : CTy) (cp : CX) (w : CWidth) (cc : CX)
      (cr : Option (CTy × CX))
  deriving Repr

mutual
/-- Elaboration of one row to its C statement. -/
def growRow : GRow → CS
  | .void x => .expr (.var x)
  | .storeSlot kp ci n ss off tc ce => .store (.slotA (.var kp) ci n ss off) tc ce
  | .storeNamed tn ci n ss off tc ce => .store (.slotA (.addr (.tab tn)) ci n ss off) tc ce
  | .storeGlob g tc ce => .store (.addr (.glob g)) tc ce
  | .setVar x tc ce => .set x tc ce
  | .setOp x tc op t ce => .set x tc (.bin op t (.var x) ce)
  | .bindLet x tc ce => .set x tc ce
  | .ite cc t e => .ite cc (growsCS t .skip) (growsCS e .skip)
  | .call fc cargs dst => .call fc cargs dst
  | .ret cr => .ret cr
  | .forTrav x t hi body m => CS.forUp x t (.lit 0) hi (growsCS body .skip) m
  | .storeReg cp w ce => .vstore cp (.int false w) ce
  | .loadReg x tc cp w => .set x tc (.vld cp (.int false w))
  | .loadRegElse x tc cp w cc cr =>
      .seq (.set x tc (.vld cp (.int false w))) (.ite (.lnot cc) (.ret cr) .skip)
/-- Elaboration of a row list: sequencing, ending in `tl`. -/
def growsCS : List GRow → CS → CS
  | [], tl => tl
  | r :: rs, tl => .seq (growRow r) (growsCS rs tl)
end

/-- The supported expression families (the T4 expression lemmas):
    literals, locals, `+`/`-`/`*`, comparisons, slot loads (through a
    parameter pointer or a named table), plain globals. Everything else
    is a named refusal at the printer, never a row. -/
def exprOk : CX → Bool
  | .lit _ => true
  | .var _ => true
  | .bin op _ l r =>
    (decide (op = .add) || decide (op = .sub) || decide (op = .mul)) &&
      exprOk l && exprOk r
  | .cmp op _ l r =>
    (decide (op = .lt) || decide (op = .le) || decide (op = .eq) || decide (op = .gt)) &&
      exprOk l && exprOk r
  | .ld (.slotA (.var _) idx _ _ _) _ => exprOk idx
  | .ld (.slotA (.addr (.tab _)) idx _ _ _) _ => exprOk idx
  | .ld (.addr (.glob _)) _ => true
  | _ => false

mutual
/-- Every expression a row carries. -/
def rowCXs : GRow → List CX
  | .void _ => []
  | .storeSlot _ ci _ _ _ _ ce => [ci, ce]
  | .storeNamed _ ci _ _ _ _ ce => [ci, ce]
  | .storeGlob _ _ ce => [ce]
  | .setVar _ _ ce => [ce]
  | .setOp _ _ _ _ ce => [ce]
  | .bindLet _ _ ce => [ce]
  | .ite cc t e => cc :: (rowsCXs t ++ rowsCXs e)
  | .call _ args _ => args
  | .ret none => []
  | .ret (some (_, ce)) => [ce]
  | .forTrav _ _ hi body _ => hi :: rowsCXs body
  | .storeReg cp _ ce => [cp, ce]
  | .loadReg _ _ cp _ => [cp]
  | .loadRegElse _ _ cp _ cc none => [cp, cc]
  | .loadRegElse _ _ cp _ cc (some (_, ce)) => [cp, cc, ce]
def rowsCXs : List GRow → List CX
  | [] => []
  | r :: rs => rowCXs r ++ rowsCXs rs
end

/-- All carried expressions are in the supported families. -/
def rowsExprOk (rs : List GRow) : Bool := (rowsCXs rs).all exprOk

mutual
/-- Slot-layout sanity of one row: a table with no records, zero-size
    records, or a field outside its record is printer garbage. -/
def rowLayOk : GRow → Bool
  | .storeSlot _ _ n ss off _ _ => decide (0 < n) && decide (0 < ss) && decide (off < ss)
  | .storeNamed _ _ n ss off _ _ => decide (0 < n) && decide (0 < ss) && decide (off < ss)
  | .ite _ t e => rowLaysOk t && rowLaysOk e
  | .forTrav _ _ _ body _ => rowLaysOk body
  | _ => true
/-- Slot-layout sanity of a row list. -/
def rowLaysOk : List GRow → Bool
  | [] => true
  | r :: rs => rowLayOk r && rowLaysOk rs
end

/-- One function body as certificate data: the rows in emission
    order plus the raw local/parameter map (`vm` value locals, `pp`
    pointer locals, `ks` fixed locals -- the `EnvRel` data with the
    table names erased; the proof side reconnects them by equality). -/
structure GBody where
  rows : List GRow
  vm : List Nat
  pp : List Nat
  ks : List (Nat × Int)
  deriving Repr

/-- A `let` (or call-bound) local is fresh: outside the locals so far
    and outside the parameter map. Mirrors `CEnvLay.freshB`. -/
def freshRaw (pp : List Nat) (ks : List (Nat × Int)) (acc : List Nat) (x : Nat) : Bool :=
  !(acc.contains x) && pp.all (· != x) && ks.all (fun q => q.1 != x)

/-- The bound locals one row introduces (arm and loop bodies are
    their own scopes, so only the spine binders thread). -/
def rowFreshAcc : List Nat → GRow → List Nat
  | acc, .bindLet x _ _ => x :: acc
  | acc, .call _ _ (some (x, _)) => x :: acc
  | acc, .loadReg x _ _ _ => x :: acc
  | acc, .loadRegElse x _ _ _ _ _ => x :: acc
  | acc, _ => acc

mutual
/-- Freshness of the binder one row carries, if any. Mirrors
    `CEnvLay.freshB` through `freshRaw_ok`. -/
def rowFreshOk (pp : List Nat) (ks : List (Nat × Int)) (acc : List Nat) : GRow → Bool
  | .bindLet x _ _ => freshRaw pp ks acc x
  | .call _ _ (some (x, _)) => freshRaw pp ks acc x
  | .call _ _ none => true
  | .loadReg x _ _ _ => freshRaw pp ks acc x
  | .loadRegElse x _ _ _ _ _ => freshRaw pp ks acc x
  | .forTrav x _ _ body _ =>
    freshRaw pp ks acc x && rowsFresh pp ks (x :: acc) body
  | .ite _ t e => rowsFresh pp ks acc t && rowsFresh pp ks acc e
  | _ => true
/-- Freshness of every bound local, threading the spine binders
    (`acc`, starting at `vm`). -/
def rowsFresh : List Nat → List (Nat × Int) → List Nat → List GRow → Bool
  | _, _, _, [] => true
  | pp, ks, acc, r :: rs => rowFreshOk pp ks acc r && rowsFresh pp ks (rowFreshAcc acc r) rs
end

mutual
/-- Traverse hygiene of one row: a loop body that writes its loop
    variable is refused (the `hw` premise of `scorr_traverse`, decided
    on the elaborated rows). -/
def rowTravOk : GRow → Bool
  | .forTrav x _ _ body _ => decide ((growsCS body .skip).writesV x = false) && rowsTravOk body
  | .ite _ t e => rowsTravOk t && rowsTravOk e
  | _ => true
/-- Traverse hygiene of a row list. -/
def rowsTravOk : List GRow → Bool
  | [] => true
  | r :: rs => rowTravOk r && rowsTravOk rs
end

/-- The hygiene the soundness theorem consumes: bound-local freshness
    plus traverse hygiene. -/
def gbodyHygiene (b : GBody) : Bool :=
  rowsFresh b.pp b.ks b.vm b.rows && rowsTravOk b.rows

/-- THE DECIDABLE VALIDITY CHECK: supported expression families,
    slot-layout sanity, and the consumed hygiene. -/
def gbodyOk (b : GBody) : Bool :=
  rowsExprOk b.rows && rowLaysOk b.rows && gbodyHygiene b

theorem gbodyOk_hygiene (b : GBody) (h : gbodyOk b = true) : gbodyHygiene b = true := by
  unfold gbodyOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, -⟩, hH⟩ := h
  exact hH

/-- Raw freshness is `CEnvLay.freshB` under the map equalities. -/
theorem freshRaw_ok {D : Deklaration} {Γ : Ctx} {K : CEnvLay D Γ}
    {pp : List Nat} {ks : List (Nat × Int)} {acc : List Nat} {x : Nat}
    (hvm : K.vm = acc) (hpp : K.pp.map Prod.fst = pp) (hks : K.ks = ks)
    (h : freshRaw pp ks acc x = true) : K.freshB x = true := by
  unfold freshRaw at h
  unfold CEnvLay.freshB
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, bne_iff_ne, ne_eq] at h ⊢
  obtain ⟨⟨hacc, hpp'⟩, hks'⟩ := h
  have hmem : x ∉ K.vm := by rw [hvm]; exact hacc
  refine ⟨⟨hmem, ?_⟩, ?_⟩
  · intro q hq
    have hfst : q.1 ∈ pp := by rw [← hpp]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
    exact hpp' q.1 hfst
  · intro q hq
    have hmem' : q ∈ ks := by rw [← hks]; exact hq
    exact hks' q hmem'

/-- THE ROW DERIVATION for a block: statement by statement, each row
    a form family over a T4 judgement. `consStmt` is the escape hatch
    for the plain families (local/slot/global store, compound
    assignment) whose `StmtCorr` the per-family builders discharge;
    `bindLet`/`preVoid` mirror `BlockCorr.bind`/`pre` (freshness comes
    from `rowsFresh`, not from a premise); `consCall`/`consBindCall`
    are `scorr_call`/`bsem_bindCall`; `consIte`/`consTrav` carry their
    arm/body row derivations (`scorr_traverse`'s `hw` comes from
    `rowsTravOk`, not from a premise). -/
inductive RBlock {D : Deklaration} (X : TVCtx D) {V : Vertrag D} :
    (m : Nat) → (l : Bool) → {Γ : Ctx} → {Λ Λ' : List (Res D)} → CEnvLay D Γ →
    Block D V l Γ Λ Λ' → List GRow → CS → Prop where
  | nil {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} :
      RBlock X m l K (Block.nil (Λ := Λ)) [] .skip
  | consSetVar {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {τ : Ty}
      {x : Var Γ τ} {e : Expr D Γ Λ τ} {ce : CX} {τc : CTy}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (he : ExprCorr X K ce e) (hd : declOk τ τc = true)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.assignVar x e) rest)
        ((.setVar (K.loc x) τc ce) :: rs) (.seq (.set (K.loc x) τc ce) cr)
  | consSetOpAdd {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {lo hi lo' hi' : Int} {x : Var Γ (.int lo hi)} {e : Expr D Γ Λ (.int lo' hi')}
      {ce : CX} {t : CIT} {τc : CTy}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi)
      (he : ExprCorr X K ce e) (hta : t.holds lo hi) (htb : t.holds lo' hi')
      (htr : t.holds (lo + lo') (hi + hi')) (hd : declOk (.int lo hi) τc = true)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.plusGleich x e h1 h2) rest)
        ((.setOp (K.loc x) τc .add t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .add t (.var (K.loc x)) ce)) cr)
  | consSetOpSub {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {lo hi lo' hi' : Int} {x : Var Γ (.int lo hi)} {e : Expr D Γ Λ (.int lo' hi')}
      {ce : CX} {t : CIT} {τc : CTy}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h1 : lo ≤ lo - hi') (h2 : hi - lo' ≤ hi)
      (he : ExprCorr X K ce e) (hta : t.holds lo hi) (htb : t.holds lo' hi')
      (htr : t.holds (lo - hi') (hi - lo')) (hd : declOk (.int lo hi) τc = true)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.minusGleich x e h1 h2) rest)
        ((.setOp (K.loc x) τc .sub t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .sub t (.var (K.loc x)) ce)) cr)
  | consSetOpAnd {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {hi lo' hi' : Int} {x : Var Γ (.int 0 hi)} {e : Expr D Γ Λ (.int lo' hi')}
      {ce : CX} {t : CIT} {τc : CTy}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h0' : 0 ≤ lo')
      (he : ExprCorr X K ce e) (hta : t.holds 0 hi) (htb : t.holds lo' hi')
      (hd : declOk (.int 0 hi) τc = true)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.undGleich x e h0') rest)
        ((.setOp (K.loc x) τc .band t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .band t (.var (K.loc x)) ce)) cr)
  | consSetOpOr {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {w : Nat} {lo' hi' : Int} {x : Var Γ (.int 0 (2 ^ w - 1))}
      {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} {t : CIT} {τc : CTy}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h0' : 0 ≤ lo') (hw' : hi' < 2 ^ w)
      (he : ExprCorr X K ce e) (hta : t.holds 0 (2 ^ w - 1)) (htb : t.holds lo' hi')
      (hd : declOk (.int 0 (2 ^ w - 1)) τc = true)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.oderGleich w x e h0' hw') rest)
        ((.setOp (K.loc x) τc .bor t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .bor t (.var (K.loc x)) ce)) cr)
  | consStoreSlotParam {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {kp : Nat} {t : D.Tab} {f : D.Feld t} {hgt : D.geist t = false}
      {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
      {ci : CX} {n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hk : (kp, t) ∈ K.pp)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K ci i) (he : ExprCorr X K ce e)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeSlot kp ci n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.var kp) ci n ss off) τc ce) cr)
  | consStoreSlotNamed {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {t : D.Tab} {f : D.Feld t} {hgt : D.geist t = false}
      {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
      {tn : Nat} {ci : CX} {n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (htn : tn = X.EL.tnr t)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K ci i) (he : ExprCorr X K ce e)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeNamed tn ci n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.addr (.tab tn)) ci n ss off) τc ce) cr)
  | consStoreGlob {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {g : D.Glob} {hgg : D.ggeist g = false} {hat : D.atomar g = false}
      {e : Expr D Γ Λ (D.gtyp g)} {gn : Nat} {τc : CTy} {ce : CX}
      {hw : V.gschreibt g = true} {hL : gdarf D g Λ}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hgn : gn = X.EL.gnr g) (hty : τc = X.EL.gty g)
      (he : ExprCorr X K ce e)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.assignGlob (l := l) g e hw hL) rest)
        ((.storeGlob gn τc ce) :: rs)
        (.seq (.store (.addr (.glob gn)) τc ce) cr)
  | bindLet {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {τ : Ty}
      {e : Expr D Γ Λ τ} {rest : Block D V l (τ :: Γ) Λ Λ'}
      {x : Nat} {τc : CTy} {ce : CX} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (he : ExprCorr X K ce e) (hd : declOk τ τc = true)
      (hr : RBlock X m l (K.push τ x) rest rs cr) :
      RBlock X m l K (.bind e rest) ((.bindLet x τc ce) :: rs) (.seq (.set x τc ce) cr)
  | preVoid {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ}
      {b : Block D V l Γ Λ Λ'} {τ0 : Ty} {e0 : Expr D Γ Λ τ0} {x : Nat}
      {rs : List GRow} {cr : CS}
      (he : ExprCorr X K (.var x) e0) (hr : RBlock X m l K b rs cr) :
      RBlock X m l K b ((.void x) :: rs) (.seq (.expr (.var x)) cr)
  | consCall {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {f : D.Fn}
      {args : Args D Γ Λ (D.params f)} {hp : RufPasst D V (D.signatur f) Λ}
      {hrp : D.gruende f = 0} {rest : Block D V l Γ (nach D f Λ) Λ'}
      {fc : Nat} {cargs : List CX} {ps : List (Nat × CTy)} {Kf : CEnvLay D (D.params f)}
      {rs : List GRow} {cr : CS}
      (hF : FnCorr X.EL X.R X.CR f fc ps Kf) (hA : ArgsTo X K args cargs ps Kf)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.call (l := l) f args hp hrp) rest)
        ((.call fc cargs none) :: rs) (.seq (.call fc cargs none) cr)
  | consBindCall {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {f : D.Fn} {τ : Ty}
      {args : Args D Γ Λ (D.params f)} {heq : D.erg f = some τ}
      {hp : RufPasst D V (D.signatur f) Λ} {hrp : D.gruende f = 0}
      {rest : Block D V l (τ :: Γ) (nach D f Λ) Λ'}
      {fc : Nat} {cargs : List CX} {x : Nat} {τc : CTy}
      {ps : List (Nat × CTy)} {Kf : CEnvLay D (D.params f)} {rs : List GRow} {cr : CS}
      (hF : FnCorr X.EL X.R X.CR f fc ps Kf) (hA : ArgsTo X K args cargs ps Kf)
      (hK : K.okB = true) (hd : declOk τ τc = true)
      (hr : RBlock X m l (K.push τ x) rest rs cr) :
      RBlock X m l K (Block.bindCall f args heq hp hrp rest)
        ((.call fc cargs (some (x, τc))) :: rs) (.seq (.call fc cargs (some (x, τc))) cr)
  | consIte {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {K : CEnvLay D Γ}
      {c : Expr D Γ Λ .bool} {t e : Block D V l Γ Λ Λ'}
      {rest : Block D V l Γ Λ' Λ''} {cc : CX} {tRows eRows : List GRow}
      {rs : List GRow} {cr : CS}
      (hc : ExprCorr X K cc c)
      (ht : RBlock X m l K t tRows (growsCS tRows .skip))
      (he : RBlock X m l K e eRows (growsCS eRows .skip))
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.ite c t e) rest)
        ((.ite cc tRows eRows) :: rs) (.seq (growRow (.ite cc tRows eRows)) cr)
  | consTrav {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {tb : D.Tab}
      {t : CIT} {hN0 : 0 ≤ D.count tb} {hN : t.holds 0 (D.count tb)} {hiC : CX}
      {hhi : ∀ st ρ, ev X.EL.lay X.orc X.fr hiC st ρ = some (.int (D.count tb), st)}
      {inv : Expr D Γ Λ .bool} {body : Block D V true (.index (D.count tb) :: Γ) Λ Λ}
      {bodyRows : List GRow} {rest : Block D V l Γ Λ Λ}
      {m' : Nat} {x : Nat} {rs : List GRow} {cr : CS}
      (hK : K.okB = true)
      (hb : RBlock X m' true (K.push (.index (D.count tb)) x) body bodyRows
        (growsCS bodyRows .skip))
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.traverse (l := l) tb inv body) rest)
        ((.forTrav x t hiC bodyRows m') :: rs)
        (.seq (CS.forUp x t (.lit 0) hiC (growsCS bodyRows .skip) m') cr)

/-- THE BLOCK THEOREM: a row derivation elaborates to a `BlockCorr`
    -- hence (by `cCorr_block`) to `BlockSem`. Freshness comes from
    -- `rowsFresh` (via `freshRaw_ok`), traverse hygiene from
    -- `rowsTravOk`; every other premise is a T4 judgement. -/
theorem rblock_sound {D : Deklaration} {V : Vertrag D} (X : TVCtx D)
    {m : Nat} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ}
    {b : Block D V l Γ Λ Λ'} {rs : List GRow} {cb : CS}
    {pp : List Nat} {ks : List (Nat × Int)}
    (hpp : K.pp.map Prod.fst = pp) (hks : K.ks = ks)
    (hFresh : rowsFresh pp ks K.vm rs = true) (hTrav : rowsTravOk rs = true)
    (hR : RBlock X m l K b rs cb) : BlockCorr X m K b cb := by
  revert hpp hks hFresh hTrav
  induction hR with
  | @nil _ _ _ _ _ => intro hpp hks hFresh hTrav; exact BlockCorr.nil
  | @consSetVar _ _ m _ _ K _ _ _ _ _ _ _ _ _ hK he hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact BlockCorr.cons (scorr_assignVar X _ K hK _ he hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpAdd _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact BlockCorr.cons (scorr_plusGleich X _ K hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpSub _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact BlockCorr.cons (scorr_minusGleich X _ K hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpAnd _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ hK h0' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact BlockCorr.cons (scorr_undGleich X _ K hK _ _ h0' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpOr _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ hK h0' hw' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact BlockCorr.cons (scorr_oderGleich X _ K hK _ _ _ h0' hw' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @consStoreSlotParam _ _ m _ _ K _ _ _ hgt _ _ _ _ _ _ _ _ hw hL _ _ _ _ hk hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      refine BlockCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hn, hss, hoff, hty]
      exact scorr_assignSlotParam X K _ hk _ hgt hw hL hi he
  | @consStoreSlotNamed _ _ m _ _ K _ _ hgt _ _ _ _ _ _ _ _ _ hw hL _ _ _ _ htn hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      refine BlockCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [htn, hn, hss, hoff, hty]
      exact scorr_assignSlotNamed X _ K _ _ hgt hw hL hi he
  | @consStoreGlob _ _ m _ _ K _ hgg hat _ _ _ _ hw hL _ _ _ _ hgn hty he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      refine BlockCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hgn, hty]
      exact scorr_assignGlob X _ K _ hgg hat hw hL he
  | @bindLet _ m _ _ _ K τ _ _ x _ _ _ _ hK he hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      obtain ⟨hfresh, hFresh'⟩ := hFresh
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hpp' : (K.push τ x).pp.map Prod.fst = pp := by simp [CEnvLay.push, hpp]
      have hks' : (K.push τ x).ks = ks := by simp [CEnvLay.push, hks]
      exact BlockCorr.bind hK hf he hd (ih hpp' hks' hFresh' hTrav)
  | @preVoid _ m _ _ _ K _ _ _ _ _ _ he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact BlockCorr.pre he (ih hpp hks hFresh hTrav)
  | @consCall _ m _ _ _ K _ _ _ _ _ _ _ _ _ _ _ hF hA _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact BlockCorr.cons (scorr_call X K _ _ _ _ _ hF hA)
        (ih hpp hks hFresh hTrav)
  | @consBindCall _ m _ _ _ K _ τ _ _ _ _ _ _ _ x _ _ _ _ _ hF hA hK hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      obtain ⟨hfresh, hFresh'⟩ := hFresh
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hpp' : (K.push τ x).pp.map Prod.fst = pp := by simp [CEnvLay.push, hpp]
      have hks' : (K.push τ x).ks = ks := by simp [CEnvLay.push, hks]
      exact BlockCorr.sem (bsem_bindCall X _ _ _ _ _ _ _ _ hF hA hK hf hd
        (cCorr_block X _ (ih hpp' hks' hFresh' hTrav)))
  | @consIte _ m _ _ _ _ K _ _ _ _ _ _ _ _ _ hc ht he hr ihHt ihHe ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, rowTravOk, Bool.and_eq_true] at hTrav
      obtain ⟨⟨hFreshT, hFreshE⟩, hFreshR⟩ := hFresh
      obtain ⟨⟨hTravT, hTravE⟩, hTravR⟩ := hTrav
      have hT := cCorr_block X _ (ihHt hpp hks hFreshT hTravT)
      have hE := cCorr_block X _ (ihHe hpp hks hFreshE hTravE)
      exact BlockCorr.cons (scorr_ite X _ _ hc hT hE)
        (ihRest hpp hks hFreshR hTravR)
  | @consTrav _ m _ _ K tb t hN0 hN hiC hhi inv _ _ _ _ x _ _ hK hb hr ihHb ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, rowTravOk, Bool.and_eq_true] at hTrav
      obtain ⟨⟨hfresh, hFreshB⟩, hFreshR⟩ := hFresh
      obtain ⟨⟨hwb, hTravB⟩, hTravR⟩ := hTrav
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hw : (growsCS _ .skip).writesV _ = false := of_decide_eq_true hwb
      have hpp' : (K.push (.index (D.count tb)) x).pp.map Prod.fst = pp := by
        simp [CEnvLay.push, hpp]
      have hks' : (K.push (.index (D.count tb)) x).ks = ks := by simp [CEnvLay.push, hks]
      have hB := cCorr_block X _ (ihHb hpp' hks' hFreshB hTravB)
      exact BlockCorr.cons (scorr_traverse X _ _ _ hK hf tb t hN0 hN hiC hhi inv _ _ hB hw)
        (ihRest hpp hks hFreshR hTravR)

/-- THE ROW DERIVATION for a terminal block (`Endblock`, a function
    body): the same form families as `RBlock`, ending in `ret`/`retEnd`.
    There is no `bindCall` row: `Endblock` has no `bindCall`, so a
    trailing call-with-result is a named refusal (see CUTS). -/
inductive REnd {D : Deklaration} (X : TVCtx D) {V : Vertrag D} (top : Bool) :
    (m : Nat) → (l : Bool) → {Γ : Ctx} → {Λ : List (Res D)} → CEnvLay D Γ →
    Endblock D V l Γ Λ → List GRow → CS → Prop where
  | retEnd {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {r : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
      (htop : top = true) (hV : V.erg = none) :
      REnd X top m l K (.ret r hΛ) [] .skip
  | ret {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {r : ErgExpr D Γ Λ V.erg} {cr : Option (CTy × CX)}
      (hΛ : Λ.Perm V.ende) (h : ErgCorr X K r cr) :
      REnd X top m l K (.ret r hΛ) [.ret cr] (.ret cr)
  | eConsSetVar {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {τ : Ty}
      {x : Var Γ τ} {e : Expr D Γ Λ τ} {ce : CX} {τc : CTy}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (he : ExprCorr X K ce e) (hd : declOk τ τc = true)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.assignVar x e) rest)
        ((.setVar (K.loc x) τc ce) :: rs) (.seq (.set (K.loc x) τc ce) cr)
  | eConsSetOpAdd {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {lo hi lo' hi' : Int} {x : Var Γ (.int lo hi)} {e : Expr D Γ Λ (.int lo' hi')}
      {ce : CX} {t : CIT} {τc : CTy}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi)
      (he : ExprCorr X K ce e) (hta : t.holds lo hi) (htb : t.holds lo' hi')
      (htr : t.holds (lo + lo') (hi + hi')) (hd : declOk (.int lo hi) τc = true)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.plusGleich x e h1 h2) rest)
        ((.setOp (K.loc x) τc .add t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .add t (.var (K.loc x)) ce)) cr)
  | eConsSetOpSub {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {lo hi lo' hi' : Int} {x : Var Γ (.int lo hi)} {e : Expr D Γ Λ (.int lo' hi')}
      {ce : CX} {t : CIT} {τc : CTy}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h1 : lo ≤ lo - hi') (h2 : hi - lo' ≤ hi)
      (he : ExprCorr X K ce e) (hta : t.holds lo hi) (htb : t.holds lo' hi')
      (htr : t.holds (lo - hi') (hi - lo')) (hd : declOk (.int lo hi) τc = true)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.minusGleich x e h1 h2) rest)
        ((.setOp (K.loc x) τc .sub t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .sub t (.var (K.loc x)) ce)) cr)
  | eConsSetOpAnd {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {hi lo' hi' : Int} {x : Var Γ (.int 0 hi)} {e : Expr D Γ Λ (.int lo' hi')}
      {ce : CX} {t : CIT} {τc : CTy}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h0' : 0 ≤ lo')
      (he : ExprCorr X K ce e) (hta : t.holds 0 hi) (htb : t.holds lo' hi')
      (hd : declOk (.int 0 hi) τc = true)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.undGleich x e h0') rest)
        ((.setOp (K.loc x) τc .band t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .band t (.var (K.loc x)) ce)) cr)
  | eConsSetOpOr {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {w : Nat} {lo' hi' : Int} {x : Var Γ (.int 0 (2 ^ w - 1))}
      {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} {t : CIT} {τc : CTy}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (h0' : 0 ≤ lo') (hw' : hi' < 2 ^ w)
      (he : ExprCorr X K ce e) (hta : t.holds 0 (2 ^ w - 1)) (htb : t.holds lo' hi')
      (hd : declOk (.int 0 (2 ^ w - 1)) τc = true)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.oderGleich w x e h0' hw') rest)
        ((.setOp (K.loc x) τc .bor t ce) :: rs)
        (.seq (.set (K.loc x) τc (.bin .bor t (.var (K.loc x)) ce)) cr)
  | eConsStoreSlotParam {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {kp : Nat} {t : D.Tab} {f : D.Feld t} {hgt : D.geist t = false}
      {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
      {ci : CX} {n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hk : (kp, t) ∈ K.pp)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K ci i) (he : ExprCorr X K ce e)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeSlot kp ci n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.var kp) ci n ss off) τc ce) cr)
  | eConsStoreSlotNamed {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {t : D.Tab} {f : D.Feld t} {hgt : D.geist t = false}
      {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
      {tn : Nat} {ci : CX} {n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (htn : tn = X.EL.tnr t)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K ci i) (he : ExprCorr X K ce e)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeNamed tn ci n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.addr (.tab tn)) ci n ss off) τc ce) cr)
  | eConsStoreGlob {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {g : D.Glob} {hgg : D.ggeist g = false} {hat : D.atomar g = false}
      {e : Expr D Γ Λ (D.gtyp g)} {gn : Nat} {τc : CTy} {ce : CX}
      {hw : V.gschreibt g = true} {hL : gdarf D g Λ}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hgn : gn = X.EL.gnr g) (hty : τc = X.EL.gty g)
      (he : ExprCorr X K ce e)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.assignGlob (l := l) g e hw hL) rest)
        ((.storeGlob gn τc ce) :: rs)
        (.seq (.store (.addr (.glob gn)) τc ce) cr)
  | eBindLet {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {τ : Ty}
      {e : Expr D Γ Λ τ} {rest : Endblock D V l (τ :: Γ) Λ}
      {x : Nat} {τc : CTy} {ce : CX} {rs : List GRow} {cr : CS}
      (hK : K.okB = true) (he : ExprCorr X K ce e) (hd : declOk τ τc = true)
      (hr : REnd X top m l (K.push τ x) rest rs cr) :
      REnd X top m l K (.bind e rest) ((.bindLet x τc ce) :: rs)
        (.seq (.set x τc ce) cr)
  | ePreVoid {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {b : Endblock D V l Γ Λ} {τ0 : Ty} {e0 : Expr D Γ Λ τ0} {x : Nat}
      {rs : List GRow} {cr : CS}
      (he : ExprCorr X K (.var x) e0) (hr : REnd X top m l K b rs cr) :
      REnd X top m l K b ((.void x) :: rs) (.seq (.expr (.var x)) cr)
  | eConsCall {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {f : D.Fn}
      {args : Args D Γ Λ (D.params f)} {hp : RufPasst D V (D.signatur f) Λ}
      {hrp : D.gruende f = 0} {rest : Endblock D V l Γ (nach D f Λ)}
      {fc : Nat} {cargs : List CX} {ps : List (Nat × CTy)} {Kf : CEnvLay D (D.params f)}
      {rs : List GRow} {cr : CS}
      (hF : FnCorr X.EL X.R X.CR f fc ps Kf) (hA : ArgsTo X K args cargs ps Kf)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.call (l := l) f args hp hrp) rest)
        ((.call fc cargs none) :: rs) (.seq (.call fc cargs none) cr)
  | eConsIte {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ}
      {c : Expr D Γ Λ .bool} {t e : Block D V l Γ Λ Λ'}
      {rest : Endblock D V l Γ Λ'} {cc : CX}
      {tRows eRows : List GRow} {rs : List GRow} {cr : CS}
      (hc : ExprCorr X K cc c)
      (ht : RBlock X m l K t tRows (growsCS tRows .skip))
      (he : RBlock X m l K e eRows (growsCS eRows .skip))
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.ite c t e) rest)
        ((.ite cc tRows eRows) :: rs) (.seq (growRow (.ite cc tRows eRows)) cr)
  | eConsTrav {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {tb : D.Tab}
      {t : CIT} {hN0 : 0 ≤ D.count tb} {hN : t.holds 0 (D.count tb)} {hiC : CX}
      {hhi : ∀ st ρ, ev X.EL.lay X.orc X.fr hiC st ρ = some (.int (D.count tb), st)}
      {inv : Expr D Γ Λ .bool} {body : Block D V true (.index (D.count tb) :: Γ) Λ Λ}
      {bodyRows : List GRow} {rest : Endblock D V l Γ Λ}
      {m' x : Nat} {rs : List GRow} {cr : CS}
      (hK : K.okB = true)
      (hb : RBlock X m' true (K.push (.index (D.count tb)) x) body bodyRows
        (growsCS bodyRows .skip))
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.traverse (l := l) tb inv body) rest)
        ((.forTrav x t hiC bodyRows m') :: rs)
        (.seq (CS.forUp x t (.lit 0) hiC (growsCS bodyRows .skip) m') cr)

/-- THE TERMINAL THEOREM: a terminal row derivation elaborates to an
    `EndCorr`. Arm/body derivations go through `rblock_sound`. -/
theorem rend_corr {D : Deklaration} {V : Vertrag D} (X : TVCtx D)
    {m : Nat} {top : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
    {b : Endblock D V l Γ Λ} {rs : List GRow} {cb : CS}
    {pp : List Nat} {ks : List (Nat × Int)}
    (hpp : K.pp.map Prod.fst = pp) (hks : K.ks = ks)
    (hFresh : rowsFresh pp ks K.vm rs = true) (hTrav : rowsTravOk rs = true)
    (hR : REnd X top m l K b rs cb) : EndCorr X m top K b cb := by
  revert hpp hks hFresh hTrav
  induction hR with
  | @retEnd _ _ _ _ _ _ _ htop hV =>
      intro hpp hks hFresh hTrav
      exact EndCorr.retEnd _ htop hV
  | @ret _ _ _ _ _ _ _ hΛ h =>
      intro hpp hks hFresh hTrav
      exact EndCorr.ret hΛ h
  | @eConsSetVar _ _ _ _ _ _ _ _ _ _ _ _ _ hK he hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact EndCorr.cons (scorr_assignVar X _ _ hK _ he hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpAdd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact EndCorr.cons (scorr_plusGleich X _ _ hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpSub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact EndCorr.cons (scorr_minusGleich X _ _ hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpAnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h0' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact EndCorr.cons (scorr_undGleich X _ _ hK _ _ h0' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpOr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h0' hw' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact EndCorr.cons (scorr_oderGleich X _ _ hK _ _ _ h0' hw' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @eConsStoreSlotParam _ _ _ _ _ _ _ _ hgt _ _ _ _ _ _ _ _ hw hL _ _ _ hk hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      refine EndCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hn, hss, hoff, hty]
      exact scorr_assignSlotParam X _ _ hk _ hgt hw hL hi he
  | @eConsStoreSlotNamed _ _ _ _ _ _ _ hgt _ _ _ _ _ _ _ _ _ hw hL _ _ _ htn hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      refine EndCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [htn, hn, hss, hoff, hty]
      exact scorr_assignSlotNamed X _ _ _ _ hgt hw hL hi he
  | @eConsStoreGlob _ _ _ _ _ _ hgg hat _ _ _ _ hw hL _ _ _ hgn hty he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      refine EndCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hgn, hty]
      exact scorr_assignGlob X _ _ _ hgg hat hw hL he
  | @eBindLet _ _ _ _ K τ _ _ x _ _ _ _ hK he hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      obtain ⟨hfresh, hFresh'⟩ := hFresh
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hpp' : (K.push τ x).pp.map Prod.fst = pp := by simp [CEnvLay.push, hpp]
      have hks' : (K.push τ x).ks = ks := by simp [CEnvLay.push, hks]
      exact EndCorr.bind hK hf he hd (ih hpp' hks' hFresh' hTrav)
  | @ePreVoid _ _ _ _ _ _ _ _ _ _ _ he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact EndCorr.pre he (ih hpp hks hFresh hTrav)
  | @eConsCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hA _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc] at hFresh
      simp only [rowsTravOk, rowTravOk] at hTrav
      exact EndCorr.cons (scorr_call X _ _ _ _ _ _ hF hA)
        (ih hpp hks hFresh hTrav)
  | @eConsIte _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc ht he hr ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, rowTravOk, Bool.and_eq_true] at hTrav
      obtain ⟨⟨hFreshT, hFreshE⟩, hFreshR⟩ := hFresh
      obtain ⟨⟨hTravT, hTravE⟩, hTravR⟩ := hTrav
      have hT := cCorr_block X _ (rblock_sound X hpp hks hFreshT hTravT ht)
      have hE := cCorr_block X _ (rblock_sound X hpp hks hFreshE hTravE he)
      exact EndCorr.cons (scorr_ite X _ _ hc hT hE)
        (ihRest hpp hks hFreshR hTravR)
  | @eConsTrav _ _ _ _ K tb t hN0 hN hiC hhi inv _ _ _ _ x _ _ hK hb hr ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, rowFreshOk, rowFreshAcc, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, rowTravOk, Bool.and_eq_true] at hTrav
      obtain ⟨⟨hfresh, hFreshB⟩, hFreshR⟩ := hFresh
      obtain ⟨⟨hwb, hTravB⟩, hTravR⟩ := hTrav
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hw : (growsCS _ .skip).writesV _ = false := of_decide_eq_true hwb
      have hpp' : (K.push (.index (D.count tb)) x).pp.map Prod.fst = pp := by
        simp [CEnvLay.push, hpp]
      have hks' : (K.push (.index (D.count tb)) x).ks = ks := by simp [CEnvLay.push, hks]
      have hB := cCorr_block X _ (rblock_sound X hpp' hks' hFreshB hTravB hb)
      exact EndCorr.cons (scorr_traverse X _ _ _ hK hf tb t hN0 hN hiC hhi inv _ _ hB hw)
        (ihRest hpp hks hFreshR hTravR)

/-- THE SOUNDNESS THEOREM: from a valid row derivation (freshness
    and traverse hygiene decided by `gbodyHygiene`), the emitted body
    has a run related to the Gabbro body's outcome -- through
    `cCorr_end`/`cCorr_block`'s judgements, built from the existing T4
    lemmas and nothing re-proved. -/
theorem gcert_sound {D : Deklaration} {V : Vertrag D} (X : TVCtx D)
    {m : Nat} {top : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
    {b : Endblock D V l Γ Λ} {rs : List GRow} {cb : CS}
    {pp : List Nat} {ks : List (Nat × Int)}
    (hpp : K.pp.map Prod.fst = pp) (hks : K.ks = ks)
    (hFresh : rowsFresh pp ks K.vm rs = true) (hTrav : rowsTravOk rs = true)
    (hR : REnd X top m l K b rs cb) : EndSem X m top K b cb :=
  cCorr_end X m top (rend_corr X hpp hks hFresh hTrav hR)

/-! ## The general certificate at work: `beispiele/104` re-derived.

`einzahlen_zeuge_cert` (Korrespondenz104.lean) goes through the
104-cut rows; here the same end-to-end proposition goes through the
general form families (`gcert_sound`). -/

/-- `einzahlen`'s rows in the general syntax: `(void)b`, the slot
    store of the literal `100`, the call of `lies` on parameters. -/
def einRowsG : List GRow :=
  [.void 2, .storeSlot 0 (.var 1) 2 4 0 cU32 (.lit 100), .call 1 [.var 0, .var 1] none]

/-- `lies`' rows: the return of the slot load. -/
def liesRowsG : List GRow :=
  [.ret (some (cU32, .ld cStand cU32))]

theorem einRowsG_elab : growsCS einRowsG .skip = cEinBody := rfl

/-- The `lies` row elaborates to the emitted body (a terminal row is
    not sequenced: `growRow`, not `growsCS`). -/
theorem liesRow_elab : growRow (.ret (some (cU32, .ld cStand cU32))) = cLiesBody := rfl

/-- The layout numbers the rows carry are the emitter's (`kontoLay`). -/
theorem einLay_n : (2 : Nat) = (xEin.EL.trec ()).count := rfl

theorem einLay_ss : (4 : Nat) = (xEin.EL.trec ()).ssize := rfl

theorem einLay_off : (0 : Nat) = (xEin.EL.trec ()).off (xEin.EL.fnr () ()) := rfl

theorem einLay_ty : cU32 = xEin.EL.slotTy () () := rfl

/-- `einzahlen`'s body as a general row derivation: the T4 premises
    are exactly `ein_void`/`ein_write`/`ein_call`'s, through the form
    families. -/
theorem ein_rend :
    REnd xEin true 0 false kEin (refP.rumpf refEin) einRowsG cEinBody := by
  have hi : ExprCorr xEin kEin (.var 1) refIdxEin :=
    ecorr_fest xEin kEin kEin_ks refIdxEin (fun _ _ => rfl)
  have he : ExprCorr xEin kEin (.lit 100) refHundert :=
    ecorr_weiter xEin kEin _ _ (ecorr_lit xEin kEin 100)
  exact REnd.ePreVoid ein_void (REnd.eConsStoreSlotParam (hgt := rfl) kEin_pp einLay_n
    einLay_ss einLay_off einLay_ty hi he
    (REnd.eConsCall lies_fn ein_args (REnd.retEnd rfl rfl)))

/-- `lies`' body as a general row derivation. -/
theorem lies_rend :
    REnd xLies true 0 false kLies (refP.rumpf refLies) liesRowsG cLiesBody := by
  have hi : ExprCorr xLies kLies (.var 1) refIdxBodyLies :=
    ecorr_fest xLies kLies kLies_ks refIdxBodyLies (fun _ _ => rfl)
  have he := ecorr_slotParam xLies kLies kLies_pp () rfl refDarfBodyLies hi
  show REnd xLies true 0 _ kLies (refP.rumpf refLies)
    [.ret (some (cU32, .ld cStand cU32))] cLiesBody
  exact REnd.ret (by rfl) ⟨cU32, _, rfl, he, rfl⟩

/-- `einzahlen`'s general body: rows, map, all decided. -/
def einBodyG : GBody := ⟨einRowsG, [2], [0], [(1, 0)]⟩

/-- `lies`' general body. -/
def liesBodyG : GBody := ⟨liesRowsG, [], [0], [(1, 0)]⟩

theorem einBodyG_ok : gbodyOk einBodyG = true := by decide

theorem liesBodyG_ok : gbodyOk liesBodyG = true := by decide

/-- `einzahlen`'s body correspondence, through the general certificate. -/
theorem ein_end_general :
    EndSem xEin 0 true kEin (refP.rumpf refEin) cEinBody := by
  have hFresh : rowsFresh [0] [(1, 0)] kEin.vm einRowsG = true := by decide
  have hTrav : rowsTravOk einRowsG = true := by decide
  have hpp : kEin.pp.map Prod.fst = [0] := rfl
  have hks : kEin.ks = [(1, 0)] := rfl
  have h := gcert_sound xEin hpp hks hFresh hTrav ein_rend
  exact h

/-- `lies`' body correspondence, through the general certificate. -/
theorem lies_end_general :
    EndSem xLies 0 true kLies (refP.rumpf refLies) cLiesBody :=
  gcert_sound xLies rfl rfl (by decide) (by decide) lies_rend

/-- THE CALLEE RELATION of `einzahlen`, through the general certificate
    (same shape as `ein_fn`, whose `ein_end 0` is replaced by
    `ein_end_general`). -/
theorem ein_fn_general : FnCorr refEL (rufAt refP refO 0 2) (CallAt refEL.lay tvOrc tvXR refCProg 2)
    refEin 0 cEin.params kEin :=
  cCorr_ruf refEL tvOrc tvXR refP refO 0 1 refCProg refEin 0 cEin rfl kEin 0
    ein_end_general

/-- THE CALLEE RELATION of `lies`, through the general certificate. -/
theorem lies_fn_general : FnCorr refEL (rufAt refP refO 0 1) (CallAt refEL.lay tvOrc tvXR refCProg 1)
    refLies 1 cLies.params kLies :=
  cCorr_ruf refEL tvOrc tvXR refP refO 0 0 refCProg refLies 1 cLies rfl kLies 0
    lies_end_general

/-- WITNESS, `einzahlen` END TO END through the general certificate:
    the same proposition `einzahlen_zeuge` (and `einzahlen_zeuge_cert`)
    proves -- the Gabbro call `einzahlen(7)` from `refSp0` and the
    emitted C `einzahlen(k, 0, 7)` from the zero state both finish; the
    C call returns nothing; the final states are related; the slot moved
    from `0` to `100` on both sides. -/
theorem einzahlen_zeuge_general :
    ∃ (σ' : World refD) (st' : CSt),
      rufAt refP refO 0 2 refEin refW0 refRho7 = .ok σ' () ∧
      CallAt refEL.lay tvOrc tvXR refCProg 2 0 refSt0 einArgs st' none ∧
      corrW refEL σ' st' ∧
      (refW0.slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧ st'.mem (.tab 0) 0 = .int 100 := by
  have hR : rufAt refP refO 0 2 refEin refW0 refRho7 = .ok _ () := rfl
  obtain ⟨st', rv, hC, hO⟩ := ein_fn_general refW0 refSt0 refRho7 einArgs _ refW0_corr ein_bind
    ein_envRel (by rw [hR]; rfl)
  rw [hR] at hO
  obtain ⟨hc, hret⟩ := hO
  have hrv : rv = none := hret
  subst hrv
  refine ⟨_, st', rfl, hC, hc, rfl, rfl, rfl, ?_⟩
  exact (hc.1 () rfl).2 0 () (by decide) (by decide)

/-! ## Corpus pins: printed certificates accepted by `decide`.

Each body below is pasted from `gabbro corr-lean` (general section)
and checked by `gbodyOk`. There is no Lean model of these programs, so
these pins check shape and hygiene -- the printer holds the
printer-to-emission agreement, tested in `corrlean.rs`. -/

/-- `beispiele/16`, `stand`: return of the slot load. -/
def printed16_stand : GBody :=
  { rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.var 0) (.var 1) 8 5 1) (.int false .w32))))],
    vm := [], pp := [0], ks := [(1, 0)] }

theorem printed16_stand_ok : gbodyOk printed16_stand = true := by decide

/-- `beispiele/16`, `belegen`: slot store of `true`. -/
def printed16_belegen : GBody :=
  { rows := [GRow.storeSlot 0 (.var 1) 8 5 0 (.int false .w8) (.lit 1)],
    vm := [], pp := [0], ks := [(1, 0)] }

theorem printed16_belegen_ok : gbodyOk printed16_belegen = true := by decide

/-- `beispiele/118`, `gib`: two slot stores at literal index `0`. -/
def printed118_gib : GBody :=
  { rows := [GRow.storeSlot 0 (.lit 0) 2 4 0 (.int false .w32) (.lit 30),
      GRow.storeSlot 1 (.lit 0) 2 4 0 (.int false .w32) (.lit 70)],
    vm := [], pp := [0, 1], ks := [] }

theorem printed118_gib_ok : gbodyOk printed118_gib = true := by decide

/-- `beispiele/118`, `nimm`. -/
def printed118_nimm : GBody :=
  { rows := [GRow.storeSlot 0 (.lit 0) 2 4 0 (.int false .w32) (.lit 10),
      GRow.storeSlot 1 (.lit 0) 2 4 0 (.int false .w32) (.lit 90)],
    vm := [], pp := [0, 1], ks := [] }

theorem printed118_nimm_ok : gbodyOk printed118_nimm = true := by decide

/-- `beispiele/15`, `uebernehmen`: store `true`, return the slot. -/
def printed15 : GBody :=
  { rows := [GRow.storeSlot 0 (.var 1) 8 1 0 (.int false .w8) (.lit 1),
      GRow.ret (some ((.int false .w8), (.ld (.slotA (.var 0) (.var 1) 8 1 0) (.int false .w8))))],
    vm := [], pp := [0], ks := [(1, 0)] }

theorem printed15_ok : gbodyOk printed15 = true := by decide

/-- `beispiele/25`, `byte_legen`: store of a parameter at a parameter index. -/
def printed25 : GBody :=
  { rows := [GRow.storeSlot 0 (.var 1) 4096 1 0 (.int false .w8) (.var 2)],
    vm := [1, 2], pp := [0], ks := [] }

theorem printed25_ok : gbodyOk printed25 = true := by decide

/-
CUTS: what is not proved here, by name.
- The row-to-statement link is proof-level: a `GRow` pins the C side
  (checked by `gbodyOk`); which Gabbro statement it maps to is carried
  by the `RBlock`/`REnd` derivation's T4 premises, not by data. A
  machine-checked elaboration of Gabbro surface syntax to rows (the
  printer-to-emitter agreement) is future work; the printer
  (`corrlean.rs`) holds that side, tested there.
- `exprOk`/`rowLaysOk` are pins, not consumed premises: the soundness
  theorems consume freshness (`rowsFresh`, via `freshRaw_ok`) and
  traverse hygiene (`rowsTravOk`, as `scorr_traverse`'s `hw`).
  Enforcement of the expression/layout families in a derivation is by
  provability (the T4 `ExprCorr` premises exist only for those shapes).
- `ks` values stay model data (as in lane 164): the printer proves the
  position and the kind, Lean decides the quoted value.
- No `Endblock.bindCall` exists, so a trailing call-with-result has no
  row derivation (named refusal at the printer); mid-body `bindCall`
  goes through `RBlock.consBindCall`/`bsem_bindCall`.
- The named-table store row (`storeNamed`) and the compound/global rows
  have full derivations but no corpus instantiation yet; the traverse
  row family exists in Lean (`scorr_traverse` wrapper) while the
  printer still refuses `traverse` by name.
-/

#print axioms freshRaw_ok
#print axioms gbodyOk_hygiene
#print axioms rblock_sound
#print axioms rend_corr
#print axioms gcert_sound
#print axioms einRowsG_elab
#print axioms liesRow_elab
#print axioms einBodyG_ok
#print axioms liesBodyG_ok
#print axioms ein_rend
#print axioms lies_rend
#print axioms ein_end_general
#print axioms lies_end_general
#print axioms ein_fn_general
#print axioms lies_fn_general
#print axioms einzahlen_zeuge_general
#print axioms printed16_stand_ok
#print axioms printed16_belegen_ok
#print axioms printed118_gib_ok
#print axioms printed118_nimm_ok
#print axioms printed15_ok
#print axioms printed25_ok

end Gabbro.Grammatik
