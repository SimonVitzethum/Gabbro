/-
  File:      Grammatik/Gen/Text/Invers/Ausdruck.lean
  Subject:   THE ELABORATOR INVERTS THE DELABORATOR ON EXPRESSIONS (Tier 2.1, step 1), generically: for every
             expression `e` of the generator's declaration that the delaborator prints as `s`, the elaborator's
             readers give back the plain data `uOfS`/`uOfB`/`uOfIdx` computes from `e` itself --
             `uSeite ctx s` and `uWertBody ctx s` the side `uOfS e` (a number), `uSichert ctx s` the predicate
             `uOfB e` (a truth value), `uIndex` the index `uOfIdx e`.

  The context `ctx` is described by `EInv` against the accessors of the declaration (`D.count`, `D.typ`,
  `D.gtyp`, `darf`), not against how the generator builds it: the variable printed for depth `d` is found at
  a position whose kind is `art d`, every body name is a `v{k}` or a `p{k}`, the tables and statics are found
  under their printed names with the declared counts and types, and every table the expression may read
  (`darf`) has its guards held.

  `uOfS`/`uOfB` are partial (`none`) exactly where the elaborator has no reading of the printed form: a literal
  index outside the table, an index variable of another table, a `bool` result inside an `ensures` (the
  elaborator reads `result` only as a number), and every form the delaborator does not print.
-/
import Grammatik.Gen.Text.Invers.Namen

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
    | .ptr _ _ => none
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
  var : ∀ d, d < Γ.length → kopf ≠ some (Γ.length - 1 - d) → (∀ n w, art d ≠ .ptr n w) → art d ≠ .bool →
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

/-- **The side**: the arithmetic layer over a leaf reader that answers the printed leaves reads every printed
    number back. -/
theorem rechne_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (bl : SExpr → Except String USide)
    (hB : Blatt (z := z) ctx Γ Λ art kopf bl) (n : Nat) :
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ (s : SExpr) (u : USide),
      delabE z kopf e = .ok s → uOfS z art kopf e = some u → uRechne ctx bl s = .ok u := by
  induction n with
  | zero => intro _ _ h; omega
  | succ n ih =>
  intro τ e hn s u hd hu
  cases e with
  | lit m =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS, Option.some.injEq] at hu
    subst hu
    by_cases h : 0 ≤ m
    · simp only [zahlE, h, ite_true]
      simp only [uRechne, hB.lit]
      simp only [Int.ofNat_eq_natCast, Int.toNat_of_nonneg h]
    · simp only [zahlE, h, ite_false]
      simp only [uRechne]
      simp only [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (show 0 ≤ -m by omega), neg_neg]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    split at hu
    · rename_i hk
      split at hu
      · rename_i hτ
        simp only [Option.some.injEq] at hu
        subst hu
        simp only [hk, ite_true, uRechne]
        exact hB.res x hτ hk
      · simp only [reduceCtorEq] at hu
    · rename_i hk
      simp only [hk, ite_false, uRechne]
      split at hu
      · simp only [reduceCtorEq] at hu
      · simp only [reduceCtorEq] at hu
      · simp only [reduceCtorEq] at hu
      · rename_i hp hb hr
        simp only [Option.some.injEq] at hu
        subst hu
        exact hB.var (tiefe x) (tiefe_lt x) hk (fun n w h => hp n w h) hb (fun n h => hr n h)
  | glob g hL =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    split at hu
    · simp only [reduceCtorEq] at hu
    · rename_i hg
      simp only [Option.some.injEq] at hu
      subst hu
      simp only [uRechne]
      exact hB.glob g hg
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp only [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfS] at hu
      split at hu
      · simp only [reduceCtorEq] at hu
      · rename_i hb
        cases hx : uOfIdx z art kopf (tN z t) (z.deklaration.count t) i with
        | none => simp only [hx, Option.map_none, reduceCtorEq] at hu
        | some ix =>
          simp only [hx, Option.map_some, Option.some.injEq] at hu
          subst hu
          have := hB.slot t f i' ix (idx_ok H t (sizeOf i + 1) i (by omega) i' ix hi hx) hL hb
          simp only [slotS] at this
          simp only [uRechne]
          exact this
  | widen h1 h2 e =>
    simp only [delabE] at hd
    simp only [uOfS] at hu
    exact ih e (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega) s u hd hu
  | add a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.add.sizeOf_spec] at hn
    exact (rechne_bin ctx bl "+" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).1 rfl
  | sub a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.sub.sizeOf_spec] at hn
    exact (rechne_bin ctx bl "-" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).2.1 rfl
  | mul a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.mul.sizeOf_spec] at hn
    exact (rechne_bin ctx bl "*" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).2.2 rfl
  | neg a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.neg.sizeOf_spec] at hn
    have hx := ih a (by omega) sa x ha xa
    cases sa with
    | lit m => simp only [uRechne] at hx ⊢; simp only [hx]
    | _ => simp only [uRechne] at hx ⊢ <;> simp only [hx]
  | _ => simp only [uOfS, reduceCtorEq] at hu

/-- **A number in an `ensures`/`requires`**. -/
theorem seite_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (hr : ErgOk ctx Γ kopf)
    {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : USide)
    (hd : delabE z kopf e = .ok s) (hu : uOfS z art kopf e = some u) : uSeite ctx s = .ok u :=
  rechne_ok H _ (blatt_seite H hr) (sizeOf e + 1) e (by omega) s u hd hu

/-- **A number in a body**. -/
theorem wert_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : USide)
    (hd : delabE z none e = .ok s) (hu : uOfS z art none e = some u) : uWertBody ctx s = .ok u :=
  rechne_ok H _ (blatt_wert H) (sizeOf e + 1) e (by omega) s u hd hu

theorem uParamNrAux_succ : ∀ (ns : List String) (k : Nat) (y : String) (j : Nat),
    uParamNrAux ns k y = .ok j → uParamNrAux ns (k + 1) y = .ok (j + 1)
  | [], _, _, _, h => by simp only [uParamNrAux, reduceCtorEq] at h
  | q :: rest, k, y, j, h => by
    simp only [uParamNrAux] at h ⊢
    split at h
    · simp only [Except.ok.injEq] at h; subst h; simp only [↓reduceIte, *]
    · simp only [*, Bool.false_eq_true, ite_false]
      exact uParamNrAux_succ rest (k + 1) y j h

/-- The scope under a quantifier binder `v{|Γ|}` over the table `t`. -/
def ctxAuf (ctx : UCtx) (x : String) (num : Nat) (c : Int) : UCtx :=
  { ctx with names := x :: ctx.names, kinds := .index num :: ctx.kinds, types := Ty.index c :: ctx.types,
             bits := 0 :: ctx.bits }

theorem EInvK.auf {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) :
    EInvK z (ctxAuf ctx (nVar Γ.length) (tN z t) (z.deklaration.count t)) (.index (z.deklaration.count t) :: Γ) Λ
      (artAuf (.index (tN z t)) art) kopf where
  var d hd hk := by
    cases d with
    | zero =>
      refine ⟨0, ?_, rfl⟩
      simp only [uParamNr, ctxAuf, List.length_cons, Nat.add_one_sub_one, Nat.sub_zero, uParamNrAux, strEq_nVar,
  BEq.rfl, ↓reduceIte]
    | succ d =>
      simp only [List.length_cons] at hd hk
      have hk' : kopf ≠ some (Γ.length - 1 - d) := by
        have : Γ.length + 1 - 1 - (d + 1) = Γ.length - 1 - d := by omega
        rw [this] at hk; exact hk
      obtain ⟨j, hj, ha⟩ := H.var d (by omega) hk'
      refine ⟨j + 1, ?_, ha⟩
      have hne : strEq (nVar Γ.length) (nVar (Γ.length + 1 - 1 - (d + 1))) = false := by
        simp only [strEq_nVar, beq_eq_false_iff_ne]; omega
      simp only [uParamNr, ctxAuf, List.length_cons, uParamNrAux, hne, Bool.false_eq_true, ite_false]
      have : Γ.length + 1 - 1 - (d + 1) = Γ.length - 1 - d := by omega
      rw [this]
      exact uParamNrAux_succ _ 0 _ j hj
  namen n hn := by
    simp only [ctxAuf, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact Or.inl ⟨_, rfl⟩
    · exact H.namen n hn
  lits := H.lits
  arrKonst := H.arrKonst
  glob := H.glob
  tab := H.tab
  wrapsLeer := H.wrapsLeer
  tabNr := H.tabNr
  waechter := H.waechter

theorem rechne_vgl (ctx : UCtx) (op : String) (a b : SExpr) (x y : USide)
    (ha : uSeite ctx a = .ok x) (hb : uSeite ctx b = .ok y) (hop : op = "<" ∨ op = "<=" ∨ op = "==") :
    uSichert ctx (.bin op a b) = .ok (.cmp op x y) := by
  rcases hop with rfl | rfl | rfl <;> simp only [uSichert, uIstVgl, ↓reduceIte, ha, hb]

/-- **A truth value in an `ensures`/`requires`**. -/
theorem sichert_ok (kopf : Option Nat) (n : Nat) :
    ∀ {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt},
    EInvK z ctx Γ Λ art kopf → ErgOk ctx Γ kopf →
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ (s : SExpr) (u : UEns),
      delabE z kopf e = .ok s → uOfB z art kopf e = some u → uSichert ctx s = .ok u := by
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; omega
  | succ n ih =>
  intro ctx Γ Λ art H hr τ e hn s u hd hu
  cases e with
  | tru =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB, Option.some.injEq] at hu; subst hu
    simp only [uSichert]
  | fls =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB, Option.some.injEq] at hu; subst hu
    simp only [uSichert]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i hk
      split at hu
      · rename_i hτ
        simp only [Option.some.injEq] at hu; subst hu
        subst hτ
        have hx := var_typ x
        have := (hr _ hk).2.2 hx
        simp only [hk, ↓reduceIte, uSichert, this]
      · simp only [reduceCtorEq] at hu
    · rename_i hk
      simp only [hk, ite_false]
      obtain ⟨j, hj, ha⟩ := H.var (tiefe x) (tiefe_lt x) hk
      split at hu
      · rename_i hb
        simp only [Option.some.injEq] at hu; subst hu
        simp only [uSichert, hj, ha, hb]
      · simp only [reduceCtorEq] at hu
  | glob g hL =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i hg
      simp only [Option.some.injEq] at hu; subst hu
      obtain ⟨e, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
      obtain ⟨gl, hf, hb⟩ := H.glob g
      have hgl : gl.ty = .bool := hb.2 hg
      simp only [uSichert, he, hf, hgl]
    · simp only [reduceCtorEq] at hu
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp only [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfB] at hu
      split at hu
      · rename_i hb
        cases hx : uOfIdx z art kopf (tN z t) (z.deklaration.count t) i with
        | none => simp only [hx, Option.map_none, reduceCtorEq] at hu
        | some ix =>
          simp only [hx, Option.map_some, Option.some.injEq] at hu
          subst hu
          have hz := zugriff_slot H t f i' ix (idx_ok H t (sizeOf i + 1) i (by omega) i' ix hi hx) hL
          simp only [slotS] at hz
          simp only [uSichert, hz, H.boolFeld t f, hb, decide_true, ite_true]
      · simp only [reduceCtorEq] at hu
  | lt a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    exact rechne_vgl ctx "<" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp only [String.reduceEq, or_self, or_false])
  | le a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    exact rechne_vgl ctx "<=" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp only [String.reduceEq, or_false, or_true])
  | eq a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    exact rechne_vgl ctx "==" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp only [String.reduceEq, or_true])
  | and a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfB z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.and.sizeOf_spec] at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    have h2 := ih H hr b (by omega) sb y hb xb
    simp only [uSichert, uIstVgl, String.reduceEq, imp_self, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_true, h1, h2]
  | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfB z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.or.sizeOf_spec] at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    have h2 := ih H hr b (by omega) sb y hb xb
    simp only [uSichert, uIstVgl, String.reduceEq, imp_self, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_false, decide_true, h1, h2]
  | not a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.not.sizeOf_spec] at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    simp only [uSichert, h1]
  | forallSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z kopf body with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z (artAuf (.index (tN z t)) art) kopf body with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.forallSlots.sizeOf_spec, sizeOf_default, add_zero] at hn
    have h1 := ih (H.auf t) (hr.auf rfl rfl _) body (by omega) sa x ha xa
    simp only [ctxAuf] at h1
    simp only [uSichert, BEq.rfl, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_true, uTabNr, H.tabNr t, h1]
  | existsSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z kopf body with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z (artAuf (.index (tN z t)) art) kopf body with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.existsSlots.sizeOf_spec, sizeOf_default, add_zero] at hn
    have h1 := ih (H.auf t) (hr.auf rfl rfl _) body (by omega) sa x ha xa
    simp only [ctxAuf] at h1
    simp only [uSichert, BEq.rfl, Bool.or_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_true, uTabNr, H.tabNr t, h1, beq_iff_eq, reduceCtorEq]
  | _ => simp only [uOfB, reduceCtorEq] at hu

/-- Without a result, a read-back side holds no `old` and no `result`. -/
theorem seite_ohne_erg (art : Nat → UParamArt) (n : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n →
      ∀ u, uOfS z art none e = some u → seiteAltErg u = false := by
  induction n with
  | zero => intro _ _ _ _ h; omega
  | succ n ih =>
  intro Γ Λ τ e hn u hu
  cases e with
  | lit m =>
    simp only [uOfS, Option.some.injEq] at hu; subst hu
    rfl
  | var x =>
    simp only [uOfS] at hu
    split at hu
    · rename_i h; simp only [reduceCtorEq] at h
    · split at hu <;> simp only [reduceCtorEq, Option.some.injEq] at hu; subst hu; rfl
  | glob g hL =>
    simp only [uOfS] at hu
    split at hu <;> simp only [reduceCtorEq, Option.some.injEq] at hu; subst hu; rfl
  | slot t f i hL =>
    simp only [uOfS] at hu
    split at hu
    · simp only [reduceCtorEq] at hu
    · cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i <;> simp only [hx, Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at hu; subst hu; rfl
  | widen h1 h2 e =>
    simp only [uOfS] at hu
    exact ih e (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega) u hu
  | add a b | sub a b | mul a b =>
    simp only [uOfS] at hu
    simp only [Expr.add.sizeOf_spec, Expr.sub.sizeOf_spec, Expr.mul.sizeOf_spec] at hn
    cases xa : uOfS z art none a <;> cases xb : uOfS z art none b <;> simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [seiteAltErg, ih a (by omega) _ xa, ih b (by omega) _ xb, Bool.or_self]
  | neg a =>
    simp only [uOfS] at hu
    simp only [Expr.neg.sizeOf_spec] at hn
    cases xa : uOfS z art none a <;> simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [seiteAltErg, ih a (by omega) _ xa]
  | _ => simp only [uOfS, reduceCtorEq] at hu

theorem ens_ohne_erg (n : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt} {τ : Ty} (e : Expr z.deklaration Γ Λ τ),
      sizeOf e < n → ∀ u, uOfB z art none e = some u → ensAltErg u = false := by
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ Λ art τ e hn u hu
  cases e with
  | tru | fls => simp only [uOfB, Option.some.injEq] at hu; subst hu; rfl
  | var x =>
    simp only [uOfB] at hu
    split at hu
    · rename_i h; simp only [reduceCtorEq] at h
    · split at hu <;> simp only [Option.some.injEq, reduceCtorEq] at hu; subst hu; rfl
  | glob g hL =>
    simp only [uOfB] at hu
    split at hu <;> simp only [Option.some.injEq, reduceCtorEq] at hu; subst hu; rfl
  | slot t f i hL =>
    simp only [uOfB] at hu
    split at hu
    · cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i <;> simp only [hx, Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at hu; subst hu; rfl
    · simp only [reduceCtorEq] at hu
  | lt a b | le a b | eq a b =>
    simp only [uOfB] at hu
    cases xa : uOfS z art none a <;> cases xb : uOfS z art none b <;> simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, seite_ohne_erg art (sizeOf a + 1) a (by omega) _ xa,
  seite_ohne_erg art (sizeOf b + 1) b (by omega) _ xb, Bool.or_self]
  | and a b | or a b =>
    simp only [uOfB] at hu
    simp only [Expr.and.sizeOf_spec, Expr.or.sizeOf_spec] at hn
    cases xa : uOfB z art none a <;> cases xb : uOfB z art none b <;> simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, ih a (by omega) _ xa, ih b (by omega) _ xb, Bool.or_self]
  | not a =>
    simp only [uOfB] at hu
    simp only [Expr.not.sizeOf_spec] at hn
    cases xa : uOfB z art none a <;> simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, ih a (by omega) _ xa]
  | forallSlots t body hL | existsSlots t body hL =>
    simp only [uOfB] at hu
    simp only [Expr.forallSlots.sizeOf_spec, sizeOf_default, add_zero, Expr.existsSlots.sizeOf_spec] at hn
    cases xa : uOfB z (artAuf (.index (tN z t)) art) none body <;> simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, ih body (by omega) _ xa]
  | _ => simp only [uOfB, reduceCtorEq] at hu

/-- **A truth value in a body** (`uBool`: the predicate reader without `old`/`result`). -/
theorem bool_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : UEns)
    (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) : uBool ctx s = .ok u := by
  have H' : EInv z { ctx with res := none, resBool := false } Γ Λ art :=
    { var := H.var, namen := H.namen, lits := H.lits, arrKonst := H.arrKonst, wrapsLeer := H.wrapsLeer, glob := H.glob, tab := H.tab, tabNr := H.tabNr,
      waechter := H.waechter }
  have h := sichert_ok none (sizeOf e + 1) H' (ergOk_none _ _) e (by omega) s u hd hu
  simp only [uBool, h, ens_ohne_erg (sizeOf e + 1) e (by omega) u hu, Bool.false_eq_true, ite_false]

end Gabbro.Grammatik.Gen.Text