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
  | consStmt {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {K : CEnvLay D Γ}
      {s : Stmt D V l Γ Λ Λ'} {rest : Block D V l Γ Λ' Λ''}
      {r : GRow} {rs : List GRow} {cr : CS}
      (hs : StmtCorr X m K s (growRow r)) (hr : RBlock X m l K rest rs cr) :
      RBlock X m l K (.cons s rest) (r :: rs) (.seq (growRow r) cr)
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

end Gabbro.Grammatik
