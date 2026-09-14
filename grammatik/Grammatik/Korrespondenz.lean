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
  | storeSlot (kp ip n ss off : Nat) (tc : CTy) (ce : CX)
  | storeNamed (tn ip n ss off : Nat) (tc : CTy) (ce : CX)
  | storeGlob (g : Nat) (tc : CTy) (ce : CX)
  | setVar (x : Nat) (tc : CTy) (ce : CX)
  | setOp (x : Nat) (tc : CTy) (op : CBinOp) (t : CIT) (ce : CX)
  | bindLet (x : Nat) (tc : CTy) (ce : CX)
  | ite (cc : CX) (t e : List GRow)
  | call (fc : Nat) (cargs : List CX) (dst : Option (Nat × CTy))
  | ret (cr : Option (CTy × CX))
  | forTrav (x : Nat) (t : CIT) (hi : CX) (body : List GRow) (m : Nat)
  deriving Repr

mutual
/-- Elaboration of one row to its C statement. -/
def growRow : GRow → CS
  | .void x => .expr (.var x)
  | .storeSlot kp ip n ss off tc ce => .store (.slotA (.var kp) (.var ip) n ss off) tc ce
  | .storeNamed tn ip n ss off tc ce => .store (.slotA (.addr (.tab tn)) (.var ip) n ss off) tc ce
  | .storeGlob g tc ce => .store (.addr (.glob g)) tc ce
  | .setVar x tc ce => .set x tc ce
  | .setOp x tc op t ce => .set x tc (.bin op t (.var x) ce)
  | .bindLet x tc ce => .set x tc ce
  | .ite cc t e => .ite cc (growsCS t .skip) (growsCS e .skip)
  | .call fc cargs dst => .call fc cargs dst
  | .ret cr => .ret cr
  | .forTrav x t hi body m => CS.forUp x t (.lit 0) hi (growsCS body .skip) m
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
    (decide (op = .lt) || decide (op = .le) || decide (op = .eq)) &&
      exprOk l && exprOk r
  | .ld (.slotA (.var _) idx _ _ _) _ => exprOk idx
  | .ld (.slotA (.addr (.tab _)) idx _ _ _) _ => exprOk idx
  | .ld (.addr (.glob _)) _ => true
  | _ => false

/-- Every expression a row carries. -/
def rowCXs : GRow → List CX
  | .void _ => []
  | .storeSlot _ _ _ _ _ _ ce => [ce]
  | .storeNamed _ _ _ _ _ _ ce => [ce]
  | .storeGlob _ _ ce => [ce]
  | .setVar _ _ ce => [ce]
  | .setOp _ _ _ _ ce => [ce]
  | .bindLet _ _ ce => [ce]
  | .ite cc t e => cc :: (t.flatMap rowCXs ++ e.flatMap rowCXs)
  | .call _ args _ => args
  | .ret none => []
  | .ret (some (_, ce)) => [ce]
  | .forTrav _ _ hi body _ => hi :: body.flatMap rowCXs

/-- All carried expressions are in the supported families. -/
def rowsExprOk (rs : List GRow) : Bool := (rs.flatMap rowCXs).all exprOk

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

/-- Freshness of every bound local, threading the bound locals (`acc`,
    starting at `vm`); arm and loop bodies are their own scopes. -/
def rowsFresh (pp : List Nat) (ks : List (Nat × Int)) (acc : List Nat) : List GRow → Bool
  | [] => true
  | .void _ :: rs => rowsFresh pp ks acc rs
  | .storeSlot _ _ _ _ _ _ _ :: rs => rowsFresh pp ks acc rs
  | .storeNamed _ _ _ _ _ _ _ :: rs => rowsFresh pp ks acc rs
  | .storeGlob _ _ _ :: rs => rowsFresh pp ks acc rs
  | .setVar _ _ _ :: rs => rowsFresh pp ks acc rs
  | .setOp _ _ _ _ _ :: rs => rowsFresh pp ks acc rs
  | .bindLet x _ _ :: rs => freshRaw pp ks acc x && rowsFresh pp ks (x :: acc) rs
  | .ite _ t e :: rs => rowsFresh pp ks acc t && rowsFresh pp ks acc e && rowsFresh pp ks acc rs
  | .call _ _ none :: rs => rowsFresh pp ks acc rs
  | .call _ _ (some (x, _)) :: rs =>
    freshRaw pp ks acc x && rowsFresh pp ks (x :: acc) rs
  | .ret _ :: rs => rowsFresh pp ks acc rs
  | .forTrav x _ _ body _ :: rs =>
    freshRaw pp ks acc x && rowsFresh pp ks (x :: acc) body && rowsFresh pp ks acc rs

/-- Traverse hygiene of a row list: no loop body writes its loop
    variable (the `hw` premise of `scorr_traverse`, decided on the
    elaborated rows). -/
def rowsTravOk : List GRow → Bool
  | [] => true
  | .void _ :: rs => rowsTravOk rs
  | .storeSlot _ _ _ _ _ _ _ :: rs => rowsTravOk rs
  | .storeNamed _ _ _ _ _ _ _ :: rs => rowsTravOk rs
  | .storeGlob _ _ _ :: rs => rowsTravOk rs
  | .setVar _ _ _ :: rs => rowsTravOk rs
  | .setOp _ _ _ _ _ :: rs => rowsTravOk rs
  | .bindLet _ _ _ :: rs => rowsTravOk rs
  | .ite _ t e :: rs => rowsTravOk t && rowsTravOk e && rowsTravOk rs
  | .call _ _ _ :: rs => rowsTravOk rs
  | .ret _ :: rs => rowsTravOk rs
  | .forTrav x _ _ body _ :: rs =>
    decide ((growsCS body .skip).writesV x = false) && rowsTravOk body && rowsTravOk rs

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
      {ip n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (hk : (kp, t) ∈ K.pp)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K (.var ip) i) (he : ExprCorr X K ce e)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeSlot kp ip n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.var kp) (.var ip) n ss off) τc ce) cr)
  | consStoreSlotNamed {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {t : D.Tab} {f : D.Feld t} {hgt : D.geist t = false}
      {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
      {tn ip n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Block D V l Γ Λ Λ'} {Λ' : List (Res D)} {rs : List GRow} {cr : CS}
      (htn : tn = X.EL.tnr t)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K (.var ip) i) (he : ExprCorr X K ce e)
      (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeNamed tn ip n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.addr (.tab tn)) (.var ip) n ss off) τc ce) cr)
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
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact BlockCorr.cons (scorr_assignVar X _ K hK _ he hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpAdd _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact BlockCorr.cons (scorr_plusGleich X _ K hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpSub _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact BlockCorr.cons (scorr_minusGleich X _ K hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpAnd _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ hK h0' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact BlockCorr.cons (scorr_undGleich X _ K hK _ _ h0' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @consSetOpOr _ _ m _ _ K _ _ _ _ _ _ _ _ _ _ _ _ hK h0' hw' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact BlockCorr.cons (scorr_oderGleich X _ K hK _ _ _ h0' hw' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @consStoreSlotParam _ _ m _ _ K _ _ _ hgt _ _ _ _ _ _ _ _ hw hL _ _ _ _ hk hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      refine BlockCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hn, hss, hoff, hty]
      exact scorr_assignSlotParam X K _ hk _ hgt hw hL hi he
  | @consStoreSlotNamed _ _ m _ _ K _ _ hgt _ _ _ _ _ _ _ _ _ hw hL _ _ _ _ htn hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      refine BlockCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [htn, hn, hss, hoff, hty]
      exact scorr_assignSlotNamed X _ K _ _ hgt hw hL hi he
  | @consStoreGlob _ _ m _ _ K _ hgg hat _ _ _ _ hw hL _ _ _ _ hgn hty he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      refine BlockCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hgn, hty]
      exact scorr_assignGlob X _ K _ hgg hat hw hL he
  | @bindLet _ m _ _ _ K τ _ _ x _ _ _ _ hK he hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk] at hTrav
      obtain ⟨hfresh, hFresh'⟩ := hFresh
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hpp' : (K.push τ x).pp.map Prod.fst = pp := by simp [CEnvLay.push, hpp]
      have hks' : (K.push τ x).ks = ks := by simp [CEnvLay.push, hks]
      exact BlockCorr.bind hK hf he hd (ih hpp' hks' hFresh' hTrav)
  | @preVoid _ m _ _ _ K _ _ _ _ _ _ he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact BlockCorr.pre he (ih hpp hks hFresh hTrav)
  | @consCall _ m _ _ _ K _ _ _ _ _ _ _ _ _ _ _ hF hA _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact BlockCorr.cons (scorr_call X K _ _ _ _ _ hF hA)
        (ih hpp hks hFresh hTrav)
  | @consBindCall _ m _ _ _ K _ τ _ _ _ _ _ _ _ x _ _ _ _ _ hF hA hK hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk] at hTrav
      obtain ⟨hfresh, hFresh'⟩ := hFresh
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hpp' : (K.push τ x).pp.map Prod.fst = pp := by simp [CEnvLay.push, hpp]
      have hks' : (K.push τ x).ks = ks := by simp [CEnvLay.push, hks]
      exact BlockCorr.sem (bsem_bindCall X _ _ _ _ _ _ _ _ hF hA hK hf hd
        (cCorr_block X _ (ih hpp' hks' hFresh' hTrav)))
  | @consIte _ m _ _ _ _ K _ _ _ _ _ _ _ _ _ hc ht he hr ihHt ihHe ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, Bool.and_eq_true] at hTrav
      obtain ⟨⟨hFreshT, hFreshE⟩, hFreshR⟩ := hFresh
      obtain ⟨⟨hTravT, hTravE⟩, hTravR⟩ := hTrav
      have hT := cCorr_block X _ (ihHt hpp hks hFreshT hTravT)
      have hE := cCorr_block X _ (ihHe hpp hks hFreshE hTravE)
      exact BlockCorr.cons (scorr_ite X _ _ hc hT hE)
        (ihRest hpp hks hFreshR hTravR)
  | @consTrav _ m _ _ K tb t hN0 hN hiC hhi inv _ _ _ _ x _ _ hK hb hr ihHb ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, Bool.and_eq_true] at hTrav
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
      {ip n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (hk : (kp, t) ∈ K.pp)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K (.var ip) i) (he : ExprCorr X K ce e)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeSlot kp ip n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.var kp) (.var ip) n ss off) τc ce) cr)
  | eConsStoreSlotNamed {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ}
      {t : D.Tab} {f : D.Feld t} {hgt : D.geist t = false}
      {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
      {tn ip n ss off : Nat} {τc : CTy} {ce : CX}
      {hw : V.schreibt t = true} {hL : darf D t Λ}
      {rest : Endblock D V l Γ Λ} {rs : List GRow} {cr : CS}
      (htn : tn = X.EL.tnr t)
      (hn : n = (X.EL.trec t).count) (hss : ss = (X.EL.trec t).ssize)
      (hoff : off = (X.EL.trec t).off (X.EL.fnr t f)) (hty : τc = X.EL.slotTy t f)
      (hi : ExprCorr X K (.var ip) i) (he : ExprCorr X K ce e)
      (hr : REnd X top m l K rest rs cr) :
      REnd X top m l K (.cons (Stmt.assignSlot (l := l) t f i e hw hL) rest)
        ((.storeNamed tn ip n ss off τc ce) :: rs)
        (.seq (.store (.slotA (.addr (.tab tn)) (.var ip) n ss off) τc ce) cr)
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
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact EndCorr.cons (scorr_assignVar X _ _ hK _ he hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpAdd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact EndCorr.cons (scorr_plusGleich X _ _ hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpSub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h1 h2 he hta htb htr hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact EndCorr.cons (scorr_minusGleich X _ _ hK _ _ h1 h2 he hta htb htr hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpAnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h0' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact EndCorr.cons (scorr_undGleich X _ _ hK _ _ h0' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @eConsSetOpOr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK h0' hw' he hta htb hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact EndCorr.cons (scorr_oderGleich X _ _ hK _ _ _ h0' hw' he hta htb hd)
        (ih hpp hks hFresh hTrav)
  | @eConsStoreSlotParam _ _ _ _ _ _ _ _ hgt _ _ _ _ _ _ _ _ hw hL _ _ _ hk hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      refine EndCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hn, hss, hoff, hty]
      exact scorr_assignSlotParam X _ _ hk _ hgt hw hL hi he
  | @eConsStoreSlotNamed _ _ _ _ _ _ _ hgt _ _ _ _ _ _ _ _ _ hw hL _ _ _ htn hn hss hoff hty hi he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      refine EndCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [htn, hn, hss, hoff, hty]
      exact scorr_assignSlotNamed X _ _ _ _ hgt hw hL hi he
  | @eConsStoreGlob _ _ _ _ _ _ hgg hat _ _ _ _ hw hL _ _ _ hgn hty he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      refine EndCorr.cons ?_ (ih hpp hks hFresh hTrav)
      rw [hgn, hty]
      exact scorr_assignGlob X _ _ _ hgg hat hw hL he
  | @eBindLet _ _ _ _ K τ _ _ x _ _ _ _ hK he hd _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk] at hTrav
      obtain ⟨hfresh, hFresh'⟩ := hFresh
      have hf := freshRaw_ok rfl hpp hks hfresh
      have hpp' : (K.push τ x).pp.map Prod.fst = pp := by simp [CEnvLay.push, hpp]
      have hks' : (K.push τ x).ks = ks := by simp [CEnvLay.push, hks]
      exact EndCorr.bind hK hf he hd (ih hpp' hks' hFresh' hTrav)
  | @ePreVoid _ _ _ _ _ _ _ _ _ _ _ he _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact EndCorr.pre he (ih hpp hks hFresh hTrav)
  | @eConsCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hA _ ih =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh] at hFresh
      simp only [rowsTravOk] at hTrav
      exact EndCorr.cons (scorr_call X _ _ _ _ _ _ hF hA)
        (ih hpp hks hFresh hTrav)
  | @eConsIte _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc ht he hr ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, Bool.and_eq_true] at hTrav
      obtain ⟨⟨hFreshT, hFreshE⟩, hFreshR⟩ := hFresh
      obtain ⟨⟨hTravT, hTravE⟩, hTravR⟩ := hTrav
      have hT := cCorr_block X _ (rblock_sound X hpp hks hFreshT hTravT ht)
      have hE := cCorr_block X _ (rblock_sound X hpp hks hFreshE hTravE he)
      exact EndCorr.cons (scorr_ite X _ _ hc hT hE)
        (ihRest hpp hks hFreshR hTravR)
  | @eConsTrav _ _ _ _ K tb t hN0 hN hiC hhi inv _ _ _ _ x _ _ hK hb hr ihRest =>
      intro hpp hks hFresh hTrav
      simp only [rowsFresh, Bool.and_eq_true] at hFresh
      simp only [rowsTravOk, Bool.and_eq_true] at hTrav
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

end Gabbro.Grammatik
