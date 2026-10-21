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
    | .index m => if m = num then some (.param (nVar (Γ.length - 1 - tiefe x))) else none
    | .int => some (.param (nVar (Γ.length - 1 - tiefe x)))
    | _ => none
  | _ => none

/-- The side the elaborator reads (`uSeite`, `uWertBody`): a number. -/
def uOfS (art : Nat → UParamArt) (kopf : Option Nat) {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} :
    Expr z.deklaration Γ Λ τ → Option USide
  | .lit n => some (if 0 ≤ n then .lit n else .neg (.lit (-n)))
  | .var x =>
    if kopf = some (Γ.length - 1 - tiefe x) then some .erg else
    match art (tiefe x) with
    | .ptr _ _ => none
    | .bool => none
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
  | .var x =>
    if kopf = some (Γ.length - 1 - tiefe x) then none else
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
  | _ :: _, _, .here => by simp [tiefe]
  | _ :: _, _, .there v => by simp [tiefe]; exact tiefe_lt v

variable {z}

theorem EInvK.tabFind {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) :
    uAnzahlTab ctx.tabs (nTab (tN z t)) = .ok (z.deklaration.count t) := by
  obtain ⟨tb, hf, _, _, hc, _⟩ := H.tab t
  simp [uAnzahlTab, hf, hc]

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
      have : (Int.ofNat n.toNat) = n := by simp [h.1]
      rw [this]
      simp [h.2]
    · simp at hu
  | widen h1 h2 e =>
    simp only [delabE] at hd
    simp only [uOfIdx] at hu
    exact ih e (by simp at hn; omega) s ix hd hu
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfIdx] at hu
    split at hu
    · simp at hu
    · rename_i hk
      simp only [hk, ite_false, uIndex]
      obtain ⟨j, hj, ha⟩ := H.var (tiefe x) (tiefe_lt x) hk
      rw [hj]
      simp only
      rw [ha]
      revert hu
      cases art (tiefe x) <;> simp
      intro h1 h2; subst h1; subst h2; simp
  | _ => simp [uOfIdx] at hu

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
  simp [uOptFeld, hf, ho]

/-- What a leaf reader must answer on the printed leaves (both `uSeiteBlatt` and `uWertBlatt` do). -/
structure Blatt (ctx : UCtx) (Γ : Ctx) (Λ : List (Res z.deklaration)) (art : Nat → UParamArt) (kopf : Option Nat)
    (bl : SExpr → Except String USide) : Prop where
  lit : ∀ v : Nat, bl (.lit v) = .ok (.lit (Int.ofNat v))
  var : ∀ d, d < Γ.length → kopf ≠ some (Γ.length - 1 - d) → (∀ n w, art d ≠ .ptr n w) → art d ≠ .bool →
    bl (.variable (nVar (Γ.length - 1 - d))) = .ok (.param (nVar (Γ.length - 1 - d)))
  res : ∀ d, kopf = some d → bl .res = .ok .erg
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

theorem blatt_seite {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (hr : kopf.isSome → ctx.res.isSome) :
    Blatt (z := z) ctx Γ Λ art kopf (uSeiteBlatt ctx) where
  lit v := by simp [uSeiteBlatt]
  var d hd hk hp hb := by
    obtain ⟨j, hj, ha⟩ := H.var d hd hk
    simp only [uSeiteBlatt, hj, ha]
  res d hk := by
    have := hr (by simp [hk])
    simp only [uSeiteBlatt]
    cases h : ctx.res with
    | none => simp [h] at this
    | some _ => rfl
  glob g hg := by
    obtain ⟨e, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
    simp only [uSeiteBlatt, he, H.lits, List.find?_nil]
    exact H.globFind g hg
  slot t f i ix hi hL hb := by
    have hz := zugriff_slot H t f i ix hi hL
    simp only [slotS] at hz ⊢
    simp only [uSeiteBlatt, uGrenzwort, hz, H.boolFeld t f, H.optFeld t f, hb, decide_false,
      Bool.false_eq_true, ite_false, Option.isSome_none]

theorem blatt_wert {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) : Blatt (z := z) ctx Γ Λ art none (uWertBlatt ctx) where
  lit v := by simp [uWertBlatt]
  var d hd hk hp hb := by
    obtain ⟨j, hj, ha⟩ := H.var d hd hk
    simp only [uWertBlatt, hj, ha]
  res d hk := by simp at hk
  glob g hg := by
    obtain ⟨e, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
    simp only [uWertBlatt, he, H.lits, List.find?_nil]
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
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp [uRechne, ha, hb, strEq_eq]

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
      simp [Int.toNat_of_nonneg h]
    · simp only [zahlE, h, ite_false]
      simp only [uRechne, hB.lit]
      simp [Int.toNat_of_nonneg (show 0 ≤ -m by omega)]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    split at hu
    · rename_i hk
      simp only [Option.some.injEq] at hu
      subst hu
      simp only [hk, ite_true, uRechne]
      exact hB.res _ hk
    · rename_i hk
      simp only [hk, ite_false, uRechne]
      split at hu
      · simp at hu
      · simp at hu
      · rename_i hp hb
        simp only [Option.some.injEq] at hu
        subst hu
        exact hB.var (tiefe x) (tiefe_lt x) hk (fun n w h => hp n w h) hb
  | glob g hL =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    split at hu
    · simp at hu
    · rename_i hg
      simp only [Option.some.injEq] at hu
      subst hu
      simp only [uRechne]
      exact hB.glob g hg
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfS] at hu
      split at hu
      · simp at hu
      · rename_i hb
        cases hx : uOfIdx z art kopf (tN z t) (z.deklaration.count t) i with
        | none => simp [hx] at hu
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
    exact ih e (by simp at hn; omega) s u hd hu
  | add a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    simp at hn
    exact (rechne_bin ctx bl "+" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).1 rfl
  | sub a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    simp at hn
    exact (rechne_bin ctx bl "-" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).2.1 rfl
  | mul a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    simp at hn
    exact (rechne_bin ctx bl "*" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).2.2 rfl
  | neg a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    simp [xa] at hu
    subst hu
    simp at hn
    simp only [uRechne, ih a (by omega) sa x ha xa]
  | _ => simp [uOfS] at hu

/-- **A number in an `ensures`/`requires`**. -/
theorem seite_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (hr : kopf.isSome → ctx.res.isSome)
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
  | [], _, _, _, h => by simp [uParamNrAux] at h
  | q :: rest, k, y, j, h => by
    simp only [uParamNrAux] at h ⊢
    split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [*]
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
      simp [uParamNr, ctxAuf, uParamNrAux]
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
  glob := H.glob
  tab := H.tab
  tabNr := H.tabNr
  waechter := H.waechter

theorem rechne_vgl (ctx : UCtx) (op : String) (a b : SExpr) (x y : USide)
    (ha : uSeite ctx a = .ok x) (hb : uSeite ctx b = .ok y) (hop : op = "<" ∨ op = "<=" ∨ op = "==") :
    uSichert ctx (.bin op a b) = .ok (.cmp op x y) := by
  rcases hop with rfl | rfl | rfl <;> simp [uSichert, uIstVgl, ha, hb]

/-- **A truth value in an `ensures`/`requires`**. -/
theorem sichert_ok (kopf : Option Nat) (n : Nat) :
    ∀ {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt},
    EInvK z ctx Γ Λ art kopf → (kopf.isSome → ctx.res.isSome) →
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
    simp [uSichert]
  | fls =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB, Option.some.injEq] at hu; subst hu
    simp [uSichert]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · simp at hu
    · rename_i hk
      simp only [hk, ite_false]
      obtain ⟨j, hj, ha⟩ := H.var (tiefe x) (tiefe_lt x) hk
      split at hu
      · rename_i hb
        simp only [Option.some.injEq] at hu; subst hu
        simp [uSichert, hj, ha, hb]
      · simp at hu
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
    · simp at hu
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfB] at hu
      split at hu
      · rename_i hb
        cases hx : uOfIdx z art kopf (tN z t) (z.deklaration.count t) i with
        | none => simp [hx] at hu
        | some ix =>
          simp only [hx, Option.map_some, Option.some.injEq] at hu
          subst hu
          have hz := zugriff_slot H t f i' ix (idx_ok H t (sizeOf i + 1) i (by omega) i' ix hi hx) hL
          simp only [slotS] at hz
          simp only [uSichert, hz, H.boolFeld t f, hb, decide_true, ite_true]
      · simp at hu
  | lt a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    exact rechne_vgl ctx "<" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp)
  | le a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    exact rechne_vgl ctx "<=" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp)
  | eq a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    exact rechne_vgl ctx "==" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp)
  | and a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfB z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    simp at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    have h2 := ih H hr b (by omega) sb y hb xb
    simp [uSichert, uIstVgl, strEq_eq, h1, h2]
  | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp [ha, hb, bind, Except.bind] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    cases xb : uOfB z art kopf b with
    | none => simp [xa, xb] at hu
    | some y =>
    simp [xa, xb] at hu
    subst hu
    simp at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    have h2 := ih H hr b (by omega) sb y hb xb
    simp [uSichert, uIstVgl, strEq_eq, h1, h2]
  | not a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp [xa] at hu
    | some x =>
    simp [xa] at hu
    subst hu
    simp at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    simp [uSichert, h1]
  | forallSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z kopf body with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z (artAuf (.index (tN z t)) art) kopf body with
    | none => simp [xa] at hu
    | some x =>
    simp [xa] at hu
    subst hu
    simp at hn
    have h1 := ih (H.auf t) hr body (by omega) sa x ha xa
    simp only [ctxAuf] at h1
    simp [uSichert, uTabNr, H.tabNr t, h1, strEq_eq]
  | existsSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z kopf body with
    | error _ => simp [ha, bind, Except.bind] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z (artAuf (.index (tN z t)) art) kopf body with
    | none => simp [xa] at hu
    | some x =>
    simp [xa] at hu
    subst hu
    simp at hn
    have h1 := ih (H.auf t) hr body (by omega) sa x ha xa
    simp only [ctxAuf] at h1
    simp [uSichert, uTabNr, H.tabNr t, h1, strEq_eq]
  | _ => simp [uOfB] at hu

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
    split <;> rfl
  | var x =>
    simp only [uOfS] at hu
    split at hu
    · rename_i h; simp at h
    · split at hu <;> simp at hu; subst hu; rfl
  | glob g hL =>
    simp only [uOfS] at hu
    split at hu <;> simp at hu; subst hu; rfl
  | slot t f i hL =>
    simp only [uOfS] at hu
    split at hu
    · simp at hu
    · cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i <;> simp [hx] at hu; subst hu; rfl
  | widen h1 h2 e =>
    simp only [uOfS] at hu
    exact ih e (by simp at hn; omega) u hu
  | add a b | sub a b | mul a b =>
    simp only [uOfS] at hu
    simp at hn
    cases xa : uOfS z art none a <;> cases xb : uOfS z art none b <;> simp [xa, xb] at hu
    subst hu
    simp [seiteAltErg, ih a (by omega) _ xa, ih b (by omega) _ xb]
  | neg a =>
    simp only [uOfS] at hu
    simp at hn
    cases xa : uOfS z art none a <;> simp [xa] at hu
    subst hu
    simp [seiteAltErg, ih a (by omega) _ xa]
  | _ => simp [uOfS] at hu

theorem ens_ohne_erg (n : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt} {τ : Ty} (e : Expr z.deklaration Γ Λ τ),
      sizeOf e < n → ∀ u, uOfB z art none e = some u → ensAltErg u = false := by
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ Λ art τ e hn u hu
  cases e with
  | tru | fls => simp [uOfB] at hu; subst hu; rfl
  | var x =>
    simp only [uOfB] at hu
    split at hu
    · simp at hu
    · split at hu <;> simp at hu; subst hu; rfl
  | glob g hL =>
    simp only [uOfB] at hu
    split at hu <;> simp at hu; subst hu; rfl
  | slot t f i hL =>
    simp only [uOfB] at hu
    split at hu
    · cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i <;> simp [hx] at hu; subst hu; rfl
    · simp at hu
  | lt a b | le a b | eq a b =>
    simp only [uOfB] at hu
    cases xa : uOfS z art none a <;> cases xb : uOfS z art none b <;> simp [xa, xb] at hu
    subst hu
    simp [ensAltErg, seite_ohne_erg art (sizeOf a + 1) a (by omega) _ xa,
      seite_ohne_erg art (sizeOf b + 1) b (by omega) _ xb]
  | and a b | or a b =>
    simp only [uOfB] at hu
    simp at hn
    cases xa : uOfB z art none a <;> cases xb : uOfB z art none b <;> simp [xa, xb] at hu
    subst hu
    simp [ensAltErg, ih a (by omega) _ xa, ih b (by omega) _ xb]
  | not a =>
    simp only [uOfB] at hu
    simp at hn
    cases xa : uOfB z art none a <;> simp [xa] at hu
    subst hu
    simp [ensAltErg, ih a (by omega) _ xa]
  | forallSlots t body hL | existsSlots t body hL =>
    simp only [uOfB] at hu
    simp at hn
    cases xa : uOfB z (artAuf (.index (tN z t)) art) none body <;> simp [xa] at hu
    subst hu
    simp [ensAltErg, ih body (by omega) _ xa]
  | _ => simp [uOfB] at hu

/-- **A truth value in a body** (`uBool`: the predicate reader without `old`/`result`). -/
theorem bool_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : UEns)
    (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) : uBool ctx s = .ok u := by
  have H' : EInv z { ctx with res := none, resBool := false } Γ Λ art :=
    { var := H.var, namen := H.namen, lits := H.lits, glob := H.glob, tab := H.tab, tabNr := H.tabNr,
      waechter := H.waechter }
  have h := sichert_ok none (sizeOf e + 1) H' (by simp) e (by omega) s u hd hu
  simp only [uBool, h, ens_ohne_erg (sizeOf e + 1) e (by omega) u hu, Bool.false_eq_true, ite_false]

end Gabbro.Grammatik.Gen.Text