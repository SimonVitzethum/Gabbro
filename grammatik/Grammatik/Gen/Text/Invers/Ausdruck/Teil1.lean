module

public import Grammatik.Gen.Text.Invers.Namen
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

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

variable (z : Spez)

/-- The number of a table, a field, a static: the delaborator's names. -/
abbrev tN (t : z.deklaration.Tab) : Nat := (show Fin z.tabs.length from t).val
abbrev gN (g : z.deklaration.Glob) : Nat := (show Fin z.globs.length from g).val

/-- The kinds of a scope extended by a binder of kind `a` (depth 0). -/
def artAuf (a : UParamArt) (art : Nat → UParamArt) : Nat → UParamArt
  | 0 => a
  | d + 1 => art d

/-- The index the elaborator reads (`uIndex` at table number `num` of `c` slots). -/
def uOfIdx (art : Nat → UParamArt) (kopf : Option Nat) (num : Nat) (c : Int) {Γ : Ctx}
    {Λ : List (Res z.deklaration)} {τ : Ty} : Expr z.deklaration Γ Λ τ → Option UIdx
  | .lit n => if 0 ≤ n ∧ n < c then some (.lit n) else none
  | .widen _ _ e => uOfIdx art kopf num c e
  | .var x =>
    if kopf = some (Γ.length - 1 - tiefe x) then none else
    match art (tiefe x) with
    | .index m =>
      if m = num ∨ (List.finRange z.tabs.length).any (fun t' => t'.val == m && decide (z.deklaration.count t' = c))
      then some (.param (nVar (Γ.length - 1 - tiefe x))) else none
    | .int => some (.param (nVar (Γ.length - 1 - tiefe x)))
    | _ => none
  | _ => none

/-- An integer type. -/
def tyInt : Ty → Bool
  | .int _ _ => true
  | _ => false

/-- The side the elaborator reads (`uSeite`, `uWertBody`): a number. -/
def uOfS (art : Nat → UParamArt) (kopf : Option Nat) {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} :
    Expr z.deklaration Γ Λ τ → Option USide
  | .lit n => some (.lit n)
  | .var (τ := τ) x =>
    if kopf = some (Γ.length - 1 - tiefe x) then (if tyInt τ then some .erg else none) else
    match art (tiefe x) with
    | .ptr _ => none
    | .bool => none
    | .ref _ => none
    | _ => some (.param (nVar (Γ.length - 1 - tiefe x)))
  | .glob g _ => if z.deklaration.gtyp g = .bool then none else some (.glob (nGlob (gN z g)))
  | .slot t f i _ =>
    if z.deklaration.typ t f = .bool then none else
    (uOfIdx z art kopf (tN z t) (z.deklaration.count t) i).map fun ix =>
      .tab (nTab (tN z t)) (nFeld (show Fin _ from f).val) ix
  | .widen _ _ e => uOfS art kopf e
  | .add a b => do some (.add (← uOfS art kopf a) (← uOfS art kopf b))
  | .sub a b => do some (.sub (← uOfS art kopf a) (← uOfS art kopf b))
  | .mul a b => do some (.mul (← uOfS art kopf a) (← uOfS art kopf b))
  | .neg a => do some (.neg (← uOfS art kopf a))
  | _ => none

/-- The predicate the elaborator reads (`uSichert`, `uBool`): a truth value. -/
def uOfB (art : Nat → UParamArt) (kopf : Option Nat) {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} :
    Expr z.deklaration Γ Λ τ → Option UEns
  | .tru => some .tru
  | .fls => some .fls
  | .var (τ := τ) x =>
    if kopf = some (Γ.length - 1 - tiefe x) then (if τ = .bool then some .ergB else none) else
    match art (tiefe x) with
    | .bool => some (.var (nVar (Γ.length - 1 - tiefe x)))
    | _ => none
  | .glob g _ => if z.deklaration.gtyp g = .bool then some (.globB (nGlob (gN z g))) else none
  | .slot t f i _ =>
    if z.deklaration.typ t f = .bool then
      (uOfIdx z art kopf (tN z t) (z.deklaration.count t) i).map fun ix =>
        .tabB (nTab (tN z t)) (nFeld (show Fin _ from f).val) ix
    else none
  | .lt a b => do some (.cmp "<" (← uOfS z art kopf a) (← uOfS z art kopf b))
  | .le a b => do some (.cmp "<=" (← uOfS z art kopf a) (← uOfS z art kopf b))
  | .eq a b => do some (.cmp "==" (← uOfS z art kopf a) (← uOfS z art kopf b))
  | .and a b => do some (.and (← uOfB art kopf a) (← uOfB art kopf b))
  | .or a b => do some (.or (← uOfB art kopf a) (← uOfB art kopf b))
  | .not a => do some (.not (← uOfB art kopf a))
  | @Expr.forallSlots _ Γ _ t body _ => do
      some (.alle (nTab (tN z t)) (nVar Γ.length) (← uOfB (artAuf (.index (tN z t)) art) kopf body))
  | @Expr.existsSlots _ Γ _ t body _ => do
      some (.einige (nTab (tN z t)) (nVar Γ.length) (← uOfB (artAuf (.index (tN z t)) art) kopf body))
  | _ => none

/-- **The elaboration context of an expression**, against the accessors of the declaration. -/
structure EInvK (ctx : UCtx) (Γ : Ctx) (Λ : List (Res z.deklaration)) (art : Nat → UParamArt) (kopf : Option Nat) :
    Prop where
  var : ∀ d, d < Γ.length → kopf ≠ some (Γ.length - 1 - d) →
    ∃ j, uParamNr ctx (nVar (Γ.length - 1 - d)) = .ok j ∧ uArtBei ctx.kinds j = .ok (art d)
  namen : ∀ n ∈ ctx.names, RumpfName n
  lits : ctx.lits = []
  arrKonst : ctx.arrKonst = []
  wrapsLeer : ∀ tb ∈ ctx.tabs, tb.wraps = []
  glob : ∀ g : z.deklaration.Glob, ∃ gl, ctx.globs.find? (fun x => strEq x.name (nGlob (gN z g))) = some gl ∧
    (gl.ty = .bool ↔ z.deklaration.gtyp g = .bool)
  tab : ∀ t : z.deklaration.Tab, ∃ tb, ctx.tabs.find? (fun x => strEq x.name (nTab (tN z t))) = some tb ∧
    tb.name = nTab (tN z t) ∧ tb.arena = false ∧ tb.count = z.deklaration.count t ∧ tb.opts = [] ∧
    (∀ f : z.deklaration.Feld t, tb.cols.any (fun (g, _) => strEq g (nFeld (show Fin _ from f).val)) = true) ∧
    (∀ f : z.deklaration.Feld t,
      tb.bools.any (fun g => strEq g (nFeld (show Fin _ from f).val)) = decide (z.deklaration.typ t f = .bool))
  tabNr : ∀ t : z.deklaration.Tab, uTabNrAux ctx.tabs 0 (nTab (tN z t)) = .ok (tN z t, z.deklaration.count t)
  waechter : ∀ t : z.deklaration.Tab, darf z.deklaration t Λ → uHaeltWaechter ctx (nTab (tN z t)) = .ok ()

/-- The context of a body or `requires` expression: no result. -/
abbrev EInv (ctx : UCtx) (Γ : Ctx) (Λ : List (Res z.deklaration)) (art : Nat → UParamArt) : Prop :=
  EInvK z ctx Γ Λ art none

/-! ### Reading back -/

theorem tiefe_lt : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), tiefe x < Γ.length
  | _ :: _, _, .here => by simp only [tiefe, List.length_cons, Nat.zero_lt_succ]
  | _ :: _, _, .there v => by simp only [tiefe, List.length_cons, Nat.add_lt_add_iff_right]; exact tiefe_lt v

variable {z}

theorem tabNrAux_at : ∀ (tabs : List UTab) (k0 : Nat) (n : String) (j : Nat) (c : Int),
    uTabNrAux tabs k0 n = .ok (j, c) → k0 ≤ j ∧ ∃ tb, tabs[j - k0]? = some tb ∧ tb.count = c
  | [], _, _, _, _, h => by simp only [uTabNrAux, reduceCtorEq] at h
  | tb :: rest, k0, n, j, c, h => by
    simp only [uTabNrAux] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨le_refl _, tb, by simp only [Nat.sub_self, List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero], rfl⟩
    · obtain ⟨hk, tb', h1, h2⟩ := tabNrAux_at rest (k0 + 1) n j c h
      refine ⟨by omega, tb', ?_, h2⟩
      have hj : j - k0 = (j - (k0 + 1)) + 1 := by omega
      rw [hj]
      simpa using h1

theorem EInvK.tabFind {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) :
    uAnzahlTab ctx.tabs (nTab (tN z t)) = .ok (z.deklaration.count t) := by
  obtain ⟨tb, hf, _, _, hc, _⟩ := H.tab t
  simp only [uAnzahlTab, hf, hc]

/-- **The index**: `uIndex` reads the printed index back. -/
theorem idx_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) (n : Nat) :
    ∀ {τ : Ty} (i : Expr z.deklaration Γ Λ τ), sizeOf i < n → ∀ (s : SExpr) (ix : UIdx), delabE z kopf i = .ok s →
      uOfIdx z art kopf (tN z t) (z.deklaration.count t) i = some ix →
      uIndex ctx (nTab (tN z t)) (tN z t) s = .ok ix := by
  induction n with
  | zero => intro _ _ h; omega
  | succ n ih =>
  intro τ i hn s ix hd hu
  cases i with
  | lit n =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfIdx] at hu
    split at hu
    · rename_i h
      simp only [Option.some.injEq] at hu
      subst hu
      simp only [zahlE, h.1, ite_true, uIndex, H.tabFind t]
      have : (Int.ofNat n.toNat) = n := by simp only [Int.ofNat_eq_natCast, Int.ofNat_toNat, h.1, sup_of_le_left]
      rw [this]
      simp only [h.2, ↓reduceIte]
    · simp only [reduceCtorEq] at hu
  | widen h1 h2 e =>
    simp only [delabE] at hd
    simp only [uOfIdx] at hu
    exact ih e (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega) s ix hd hu
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfIdx] at hu
    split at hu
    · simp only [reduceCtorEq] at hu
    · rename_i hk
      simp only [hk, ite_false, uIndex]
      obtain ⟨j, hj, ha⟩ := H.var (tiefe x) (tiefe_lt x) hk
      rw [hj]
      simp only
      rw [ha]
      cases hart : art (tiefe x) with
      | index m =>
        rw [hart] at hu
        simp only at hu
        split at hu
        · rename_i hc
          simp only [Option.some.injEq] at hu; subst hu
          have hg : (m == tN z t || uGleicheAnzahl ctx.tabs m (tN z t)) = true := by
            rcases hc with rfl | hc
            · simp only [BEq.rfl, Bool.true_or]
            · obtain ⟨t', _, ht'⟩ := List.any_eq_true.1 hc
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht'
              obtain ⟨hm, hcnt⟩ := ht'
              subst hm
              obtain ⟨_, tb1, h1, c1⟩ := tabNrAux_at ctx.tabs 0 _ _ _ (H.tabNr t')
              obtain ⟨_, tb2, h2, c2⟩ := tabNrAux_at ctx.tabs 0 _ _ _ (H.tabNr t)
              simp only [Nat.sub_zero] at h1 h2
              have : uGleicheAnzahl ctx.tabs t'.val (tN z t) = true := by
                unfold uGleicheAnzahl
                show (match ctx.tabs[tN z t']?, ctx.tabs[tN z t]? with
                  | some a, some b => a.count == b.count | _, _ => false) = true
                rw [h1, h2]; simp only [c1, hcnt, c2, BEq.rfl]
              simp only [this, Bool.or_true]
          simp only [hg, ite_true]
        · simp only [reduceCtorEq] at hu
      | int =>
        rw [hart] at hu
        simp only [Option.some.injEq] at hu; subst hu
        rfl
      | _ => rw [hart] at hu; simp only [reduceCtorEq] at hu
  | _ => simp only [uOfIdx, reduceCtorEq] at hu

/-- The printed slot read `T.slots[i].f`. -/
def slotS (tn fn : String) (i : SExpr) : SExpr := .field (.index (.field (.variable tn) "slots") i) fn

theorem EInvK.param_fremd {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (x : String) (hx : ∀ n, RumpfName n → strEq n x = false) :
    ∃ e, uParamNr ctx x = .error e :=
  uParamNrAux_fremd ctx.names H.namen 0 x (fun n hm => hx n (H.namen n hm))

/-- The place of a slot read. -/
theorem zugriff_slot {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) (f : z.deklaration.Feld t) (i : SExpr) (ix : UIdx)
    (hi : uIndex ctx (nTab (tN z t)) (tN z t) i = .ok ix) (hL : darf z.deklaration t Λ) :
    uZugriff ctx (slotS (nTab (tN z t)) (nFeld (show Fin _ from f).val) i) =
      .ok (.tabelle (nTab (tN z t)), nTab (tN z t), nFeld (show Fin _ from f).val, ix) := by
  obtain ⟨tb, hf, hn, har, _, _, hcols, _⟩ := H.tab t
  obtain ⟨e, he⟩ := H.param_fremd (nTab (tN z t)) (fun n hn => strEq_rumpf_nTab hn _)
  have hs : strEq "slots" "slots" = true := by decide
  simp only [slotS, uZugriff, hs, Bool.not_true, Bool.false_eq_true, ite_false, he, hf, har, hcols f,
    hn, H.waechter t hL, H.tabNr t, hi]

theorem EInvK.boolFeld {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) (f : z.deklaration.Feld t) :
    uBoolFeld ctx (nTab (tN z t)) (nFeld (show Fin _ from f).val) = decide (z.deklaration.typ t f = .bool) := by
  obtain ⟨tb, hf, _, _, _, _, _, hb⟩ := H.tab t
  simp only [uBoolFeld, hf, hb f]

theorem EInvK.optFeld {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) (f : z.deklaration.Feld t) :
    uOptFeld ctx (nTab (tN z t)) (nFeld (show Fin _ from f).val) = none := by
  obtain ⟨tb, hf, _, _, _, ho, _⟩ := H.tab t
  simp only [uOptFeld, hf, ho, List.find?_nil, Option.map_none]

/-- What a leaf reader must answer on the printed leaves (both `uSeiteBlatt` and `uWertBlatt` do). -/
structure Blatt (ctx : UCtx) (Γ : Ctx) (Λ : List (Res z.deklaration)) (art : Nat → UParamArt) (kopf : Option Nat)
    (bl : SExpr → Except String USide) : Prop where
  lit : ∀ v : Nat, bl (.lit v) = .ok (.lit (Int.ofNat v))
  var : ∀ d, d < Γ.length → kopf ≠ some (Γ.length - 1 - d) → (∀ cap, art d ≠ .ptr cap) → art d ≠ .bool →
    (∀ n, art d ≠ .ref n) →
    bl (.variable (nVar (Γ.length - 1 - d))) = .ok (.param (nVar (Γ.length - 1 - d)))
  res : ∀ {τ : Ty} (x : Var Γ τ), tyInt τ = true → kopf = some (Γ.length - 1 - tiefe x) → bl .res = .ok .erg
  glob : ∀ g : z.deklaration.Glob, z.deklaration.gtyp g ≠ .bool →
    bl (.variable (nGlob (gN z g))) = .ok (.glob (nGlob (gN z g)))
  slot : ∀ (t : z.deklaration.Tab) (f : z.deklaration.Feld t) (i : SExpr) (ix : UIdx),
    uIndex ctx (nTab (tN z t)) (tN z t) i = .ok ix → darf z.deklaration t Λ → z.deklaration.typ t f ≠ .bool →
    bl (slotS (nTab (tN z t)) (nFeld (show Fin _ from f).val) i) = .ok (.tab (nTab (tN z t)) (nFeld (show Fin _ from f).val) ix)

theorem EInvK.globFind {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (g : z.deklaration.Glob) (hg : z.deklaration.gtyp g ≠ .bool) :
    uGlobLies ctx (nGlob (gN z g)) = .ok (.glob (nGlob (gN z g))) := by
  obtain ⟨gl, hf, hb⟩ := H.glob g
  simp only [uGlobLies, hf]
  cases h : gl.ty with
  | bool => exact absurd (hb.1 h) hg
  | int _ _ => rfl
  | wert _ => rfl

/-- The variable of depth `d` has the type `Γ[d]`, the one of number `n` the type `Γ.reverse[n]`. -/
theorem var_typ : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), Γ.reverse[Γ.length - 1 - tiefe x]? = some τ := by
  intro Γ τ x
  have h : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), Γ[tiefe x]? = some τ := by
    intro Γ τ x
    induction x with
    | here => simp only [tiefe, List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero]
    | there v ih => simp only [tiefe, List.getElem?_cons_succ, ih]
  have hl := tiefe_lt x
  rw [List.getElem?_reverse (by omega)]
  have : Γ.length - 1 - (Γ.length - 1 - tiefe x) = tiefe x := by omega
  rw [this, h x]

/-- The result of an `ensures` is read as `result` only when it is a number of a function with a result range. -/
def ErgOk (ctx : UCtx) (Γ : Ctx) (kopf : Option Nat) : Prop :=
  ∀ n, kopf = some n → n < Γ.length ∧ (∀ lo hi, Γ.reverse[n]? = some (.int lo hi) → ctx.res.isSome) ∧
    (Γ.reverse[n]? = some .bool → ctx.resBool = true)

theorem ergOk_none (ctx : UCtx) (Γ : Ctx) : ErgOk ctx Γ none := fun n h => by simp only [reduceCtorEq] at h

theorem ErgOk.auf {ctx ctx' : UCtx} {Γ : Ctx} {kopf : Option Nat} (h : ErgOk ctx Γ kopf) (hres : ctx'.res = ctx.res)
    (hb : ctx'.resBool = ctx.resBool) (τ : Ty) : ErgOk ctx' (τ :: Γ) kopf := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := h n hn
  refine ⟨by simp only [List.length_cons]; omega, fun lo hi hg => ?_, fun hg => ?_⟩
  · rw [hres]
    apply h2 lo hi
    rw [List.reverse_cons, List.getElem?_append_left (by simpa using h1)] at hg
    exact hg
  · rw [hb]
    apply h3
    rw [List.reverse_cons, List.getElem?_append_left (by simpa using h1)] at hg
    exact hg

theorem blatt_seite {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (hr : ErgOk ctx Γ kopf) :
    Blatt (z := z) ctx Γ Λ art kopf (uSeiteBlatt ctx) where
  lit v := by simp only [uSeiteBlatt, Int.ofNat_eq_natCast]
  var d hd hk hp hb _ := by
    obtain ⟨j, hj, ha⟩ := H.var d hd hk
    simp only [uSeiteBlatt, hj, ha]
  res {τ} x hτ hk := by
    have hx := var_typ x
    cases τ with
    | int lo hi =>
      have := (hr _ hk).2.1 lo hi hx
      simp only [uSeiteBlatt]
      cases h : ctx.res with
      | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at this
      | some _ => rfl
    | _ => simp only [tyInt, Bool.false_eq_true] at hτ
  glob g hg := by
    obtain ⟨e, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
    simp only [uSeiteBlatt, he, H.lits, H.arrKonst, List.find?_nil]
    exact H.globFind g hg
  slot t f i ix hi hL hb := by
    have hz := zugriff_slot H t f i ix hi hL
    simp only [slotS] at hz ⊢
    simp only [uSeiteBlatt, uGrenzwort, hz, H.boolFeld t f, H.optFeld t f, hb, decide_false,
      Bool.false_eq_true, ite_false, Option.isSome_none]

theorem blatt_wert {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) : Blatt (z := z) ctx Γ Λ art none (uWertBlatt ctx) where
  lit v := by simp only [uWertBlatt, Int.ofNat_eq_natCast]
  var d hd hk hp hb hr := by
    obtain ⟨j, hj, ha⟩ := H.var d hd hk
    simp only [uWertBlatt, hj, ha]
  res x _ hk := by simp only [reduceCtorEq] at hk
  glob g hg := by
    obtain ⟨e, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
    simp only [uWertBlatt, he, H.lits, H.arrKonst, List.find?_nil]
    exact H.globFind g hg
  slot t f i ix hi hL hb := by
    have hz := zugriff_slot H t f i ix hi hL
    simp only [slotS] at hz ⊢
    simp only [uWertBlatt, uGrenzwort, hz, H.boolFeld t f, H.optFeld t f, hb, decide_false,
      Bool.false_eq_true, ite_false, Option.isSome_none]

theorem rechne_bin (ctx : UCtx) (bl : SExpr → Except String USide) (op : String) (a b : SExpr) (x y : USide)
    (ha : uRechne ctx bl a = .ok x) (hb : uRechne ctx bl b = .ok y) :
    (op = "+" → uRechne ctx bl (.bin op a b) = .ok (.add x y)) ∧
    (op = "-" → uRechne ctx bl (.bin op a b) = .ok (.sub x y)) ∧
    (op = "*" → uRechne ctx bl (.bin op a b) = .ok (.mul x y)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp only [uRechne, strEq_eq, decide_true, String.reduceEq, decide_false, Bool.or_false, ↓reduceIte, ha, hb, Bool.or_true, Bool.false_eq_true, Bool.or_self]

end Gabbro.Grammatik.Gen.Text
