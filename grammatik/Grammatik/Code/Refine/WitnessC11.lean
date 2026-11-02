module

public import Grammatik.Code.Refine.Witness
public import Grammatik.Code.Refine.Witnessa
public import Grammatik.Code.Refine.StmtOk.Teil7
public import Grammatik.Code.Refine.StmtOk.Teil8

@[expose] public section


/-
  File:      Grammatik/Code/Refine/WitnessC11.lean
  Subject:   TRACK L, PHASE L1 -- NON-DEGENERATE WITNESSES for the C11 lowering.

  One fixture per C11 form over the declaration `wD` of `Witness.lean`, each on a table with four
  slots (so every bound check below succeeds and every lowering takes its success leg):

  * `c11consume`: consuming traversal over `konto` with a live member/edge/invariant, bound `4`,
    the zero measure and a storing body (the placeholder runs the same fixed sweep as `traverse`);
  * `c11narrow`: required narrowing of `1` to `0 .. 3` with a fall-through rest (the in-range leg);
  * `c11ret`: scoped return of the empty value with empty scope evidence (exactly `ret`);
  * `c11retWhy`: scoped reason return `1` of two with empty scope evidence (exactly `retWhy`).

  For each, `_lower` says the lowering succeeds (closed evaluation) and `_ok` instantiates the
  generic correctness lemma on the fixture. Scope-crossing returns (non-empty `scopes`), the
  dynamic re-selection of consuming traversal and the capacity duty stay OPEN (see the design);
  admission still refuses all four forms.
-/

namespace Gabbro.Code.Lower.WitC11

open Gabbro.Grammatik

instance c11conf : Conf := ⟨64, false, Or.inr rfl⟩

/-- Consuming traversal over `konto`: live tests, bound `4`, zero measure, storing body. -/
def c11consumeBody : Gabbro.Grammatik.Block Wit.wD (vertragVon Wit.wD Wit.WFn.wipe) true [.index (Wit.wD.count ())] [] [] :=
  .cons (.assignSlot () () (.var .here)
    (.widen (lo := 0) (hi := 0) (by decide) (by decide) (.lit 0)) rfl (Wit.wDarf _)) .nil

def c11consume : Stmt Wit.wD (vertragVon Wit.wD Wit.WFn.wipe) true [] [] [] :=
  .consumeTraverse () .tru .tru .tru 4
    ((.widen (lo := 0) (hi := 0) (by decide) (by decide) (.lit 0)) : Expr Wit.wD [] [] (.int 0 4))
    c11consumeBody

/-- Required narrowing of `1` to `0 .. 3` with a fall-through rest. -/
def c11narrowRest : Gabbro.Grammatik.Block Wit.wD (vertragVon Wit.wD Wit.WFn.wipe) false [.int 0 3] [] [] :=
  .nil

def c11narrow : Gabbro.Grammatik.Block Wit.wD (vertragVon Wit.wD Wit.WFn.wipe) false [] [] [] :=
  .narrowRequired
    ((.widen (lo := 1) (hi := 1) (by decide) (by decide) (.lit 1)) : Expr Wit.wD [] [] (.int 1 1))
    0 3 c11narrowRest

/-- Scoped return of the empty value with empty scope evidence. -/
def c11retR : Gabbro.Grammatik.RueckRessourcen Wit.wD (vertragVon Wit.wD Wit.WFn.wipe) [] :=
  { scopes := [], genau := List.Perm.refl [] }

def c11ret : Stmt Wit.wD (vertragVon Wit.wD Wit.WFn.wipe) true [] [] [] :=
  .retScoped .empty c11retR

/-- Scoped reason return `1` of two with empty scope evidence. -/
def c11retWhy : Gabbro.Grammatik.Endblock Wit.wD (vertragVon Wit.wD Wit.WFn.fail) false [.int 0 3] [] :=
  .retWhyScoped ⟨1, by decide⟩ { scopes := [], genau := List.Perm.refl [] }

/-- The consuming traversal lowers (closed evaluation). -/
theorem zeuge_c11_consume_lower :
    ∃ blks st', lowerS Wit.wLay [] (0, 0) c11consume 7 8 ⟨10, 30⟩ = some (blks, st') :=
  ⟨_, _, rfl⟩

/-- The generic `traverse`-family correctness lemma instantiates on the fixture. -/
theorem zeuge_c11_consume_ok (M : Modl) (S : Sees) (fn : Nat) (blks : List Block) (st' : St)
    (h : lowerS Wit.wLay [] (0, 0) c11consume 7 8 ⟨10, 30⟩ = some (blks, st'))
    (hM : InM M fn blks) (hk : KOk M fn 8) (hlv : LvOk M fn (0, 0))
    (hFn : FnOk Wit.wLay M) (hCall : CallRef Wit.wLay M S (rufAt Wit.wP Wit.wO 0 1))
    (σ : World Wit.wD) (ρ : Env Wit.wD []) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep Wit.wLay σ m) (hE : EnvRep Wit.wLay rs m [] ρ) (hW : WfL Wit.wLay m)
    (hc : ∀ x ∈ ([] : List Reg), x < 10)
    (ih : ∀ (lay : Layout Wit.wD) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel Wit.wD) (passes : Nat) (R : (f : Wit.wD.Fn) → World Wit.wD → Env Wit.wD (Wit.wD.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv c11consumeBody lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World Wit.wD), ∀ (ρ : Env Wit.wD _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R c11consumeBody σ ρ)) :
    OutOk Wit.wLay [] (0, 0) M S fn 7 8 10 st'.r m rs ks dst
      (execStmt Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1) c11consume σ ρ) :=
  lowerS_ok_consumeTraverse Wit.wLay Wit.wLayOk [] (0, 0) Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1)
    () .tru .tru .tru 4
    ((.widen (lo := 0) (hi := 0) (by decide) (by decide) (.lit 0)) : Expr Wit.wD [] [] (.int 0 4))
    c11consumeBody 7 8 ⟨10, 30⟩ st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc ih

/-- The required narrowing lowers (closed evaluation). -/
theorem zeuge_c11_narrow_lower :
    ∃ blks st', lowerB Wit.wLay [] (0, 0) c11narrow 7 8 ⟨10, 30⟩ = some (blks, st') :=
  ⟨_, _, rfl⟩

/-- The generic required-narrowing correctness lemma instantiates on the fixture. -/
theorem zeuge_c11_narrow_ok (M : Modl) (S : Sees) (fn : Nat) (blks : List Block) (st' : St)
    (h : lowerB Wit.wLay [] (0, 0) c11narrow 7 8 ⟨10, 30⟩ = some (blks, st'))
    (hM : InM M fn blks) (hk : KOk M fn 8) (hlv : LvOk M fn (0, 0))
    (hFn : FnOk Wit.wLay M) (hCall : CallRef Wit.wLay M S (rufAt Wit.wP Wit.wO 0 1))
    (σ : World Wit.wD) (ρ : Env Wit.wD []) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep Wit.wLay σ m) (hE : EnvRep Wit.wLay rs m [] ρ) (hW : WfL Wit.wLay m)
    (hc : ∀ x ∈ ([] : List Reg), x < 10)
    (ih : ∀ (lay : Layout Wit.wD) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel Wit.wD) (passes : Nat) (R : (f : Wit.wD.Fn) → World Wit.wD → Env Wit.wD (Wit.wD.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv c11narrowRest lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World Wit.wD), ∀ (ρ : Env Wit.wD _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R c11narrowRest σ ρ)) :
    OutOk Wit.wLay [] (0, 0) M S fn 7 8 10 st'.r m rs ks dst
      (execBlock Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1) c11narrow σ ρ) :=
  lowerB_ok_narrowRequired Wit.wLay Wit.wLayOk [] (0, 0) Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1)
    1 1 ((.widen (lo := 1) (hi := 1) (by decide) (by decide) (.lit 1)) : Expr Wit.wD [] [] (.int 1 1))
    0 3 c11narrowRest 7 8 ⟨10, 30⟩ st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc ih

/-- The scoped return lowers (closed evaluation). -/
theorem zeuge_c11_ret_lower :
    ∃ blks st', lowerS Wit.wLay [] (0, 0) c11ret 7 8 ⟨10, 30⟩ = some (blks, st') :=
  ⟨_, _, rfl⟩

/-- The generic scoped-return correctness lemma instantiates on the fixture. -/
theorem zeuge_c11_ret_ok (M : Modl) (S : Sees) (fn : Nat) (blks : List Block) (st' : St)
    (h : lowerS Wit.wLay [] (0, 0) c11ret 7 8 ⟨10, 30⟩ = some (blks, st'))
    (hM : InM M fn blks) (hk : KOk M fn 8) (hlv : LvOk M fn (0, 0))
    (hFn : FnOk Wit.wLay M) (hCall : CallRef Wit.wLay M S (rufAt Wit.wP Wit.wO 0 1))
    (σ : World Wit.wD) (ρ : Env Wit.wD []) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep Wit.wLay σ m) (hE : EnvRep Wit.wLay rs m [] ρ) (hW : WfL Wit.wLay m)
    (hc : ∀ x ∈ ([] : List Reg), x < 10) :
    OutOk Wit.wLay [] (0, 0) M S fn 7 8 10 st'.r m rs ks dst
      (execStmt Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1) c11ret σ ρ) :=
  by
    unfold c11ret at h ⊢
    exact lowerS_ok_retScoped Wit.wLay Wit.wLayOk [] (0, 0) Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1)
      _ c11retR 7 8 ⟨10, 30⟩ st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc

/-- The scoped reason return lowers (closed evaluation). -/
theorem zeuge_c11_retWhy_lower :
    ∃ blks st', lowerEnd Wit.wLay [] (0, 0) c11retWhy 7 ⟨10, 30⟩ = some (blks, st') :=
  ⟨_, _, rfl⟩

/-- The generic scoped-reason-return correctness lemma instantiates on the fixture. -/
theorem zeuge_c11_retWhy_ok (M : Modl) (S : Sees) (fn : Nat) (blks : List Block) (st' : St)
    (h : lowerEnd Wit.wLay [] (0, 0) c11retWhy 7 ⟨10, 30⟩ = some (blks, st'))
    (hM : InM M fn blks) (hlv : LvOk M fn (0, 0))
    (hFn : FnOk Wit.wLay M) (hCall : CallRef Wit.wLay M S (rufAt Wit.wP Wit.wO 0 1))
    (σ : World Wit.wD) (ρ : Env Wit.wD [.int 0 3]) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep Wit.wLay σ m) (hE : EnvRep Wit.wLay rs m [] ρ) (hW : WfL Wit.wLay m)
    (hc : ∀ x ∈ ([] : List Reg), x < 10) :
    EndOk Wit.wLay [] (0, 0) M S fn 7 10 st'.r m rs ks dst
      (execEnd Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1) c11retWhy σ ρ) :=
  lowerEnd_ok_retWhyScoped Wit.wLay Wit.wLayOk [] (0, 0) Wit.wO 0 (rufAt Wit.wP Wit.wO 0 1)
    ⟨1, by decide⟩ { scopes := [], genau := List.Perm.refl [] } 7 ⟨10, 30⟩ st' blks h M S fn hM hlv hFn hCall σ ρ m rs ks dst hR hE hW hc

end Gabbro.Code.Lower.WitC11
