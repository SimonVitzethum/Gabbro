/-
  File:      Grammatik/Gen/Text/Invers/Ruf.lean
  Subject:   CALLS READ BACK (Tier 2.1, step 2b): the heads the elaborator reads (`koepfe`) are described by
             `KInv` against the accessors of the declaration (the name `fn{k}`, the parameter kinds, the
             required locks, the reason channel, the result); a printed call -- direct, through `let p = &f;`,
             bound by `let x = f(..)`, or with `else (e) { .. }` -- is read back to the plain data `uOf*` computes.
-/
import Grammatik.Gen.Text.Invers.Anweisung

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

variable {z : Spez} {V : Vertrag z.deklaration}

/-- The head the elaborator read for the function `f`. -/
structure KopfPasst (gNr : Nat → Nat) (f : z.deklaration.Fn) (k : UFnKopf) : Prop where
  name : k.name = nFn (fN z f)
  kinds : (z.deklaration.params f).mapM artErg = some k.kinds
  held : ∀ l ∈ k.held, ∃ L ∈ (z.deklaration.signatur f).haelt, l = nLock (lN z L)
  ext : k.ext = false
  griffe : ∀ g ∈ k.griffe, (z.deklaration.params f).length ≤ g.1
  kanal0 : z.deklaration.gruende f = 0 → k.kanal = none
  kanal : z.deklaration.gruende f ≠ 0 → k.kanal = some (gNr (z.deklaration.gruende f), z.deklaration.gruende f)
  ergBool : z.deklaration.erg f = some .bool → k.resBool = true
  ergInt : ∀ lo hi, z.deklaration.erg f = some (.int lo hi) → k.resBool = false ∧ k.res = some (lo, hi)

/-- **The heads**: every function is found under its printed name. -/
def KInv (gNr : Nat → Nat) (koepfe : List UFnKopf) : Prop :=
  ∀ f : z.deklaration.Fn, ∃ k, koepfe.find? (fun k => strEq k.name (nFn (fN z f))) = some k ∧ KopfPasst gNr f k

/-- **The head numbers**: every function's head stands at its own signature number (the elaborator
    numbers a pointer `&f` by the head index of `f`, the model by `sig f`). -/
def KIdx (koepfe : List UFnKopf) : Prop :=
  ∀ f : z.deklaration.Fn, koepfe.findIdx? (fun k => strEq k.name (nFn (fN z f))) = some (z.deklaration.sig f)

theorem kinv_idx {gNr : Nat → Nat} {koepfe : List UFnKopf} {f : z.deklaration.Fn} {k : UFnKopf}
    (h : koepfe.find? (fun k => strEq k.name (nFn (fN z f))) = some k) :
    ∃ i, koepfe.findIdx? (fun k => strEq k.name (nFn (fN z f))) = some i ∧ koepfe[i]? = some k := by
  rw [List.find?_eq_bind_findIdx?_getElem?] at h
  cases hi : koepfe.findIdx? (fun k => strEq k.name (nFn (fN z f))) with
  | none => simp [hi] at h
  | some i => simp only [hi, Option.bind_some] at h; exact ⟨i, rfl, h⟩

/-- The arguments. -/
theorem args_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) (tabs : List UTab) :
    ∀ {τs : List Ty} (args : Args z.deklaration Γ Λ τs) (as : List SExpr) (xs : List UArg) (ks : List UParamArt),
      delabA z args = .ok as → uOfArgs z art args = some xs → τs.mapM artErg = some ks →
      uArgs ctx tabs ks as = .ok xs := by
  intro τs args
  induction args with
  | nil =>
    intro as xs ks hd hu hk
    simp only [delabA, Except.ok.injEq] at hd; subst hd
    simp only [uOfArgs, Option.some.injEq] at hu; subst hu
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hk; subst hk
    rfl
  | @cons τ τs e rest ih =>
    intro as xs ks hd hu hk
    simp only [delabA] at hd
    cases he : delabE z none e with
    | error _ => simp [he, bind, Except.bind] at hd
    | ok se =>
    cases hr : delabA z rest with
    | error _ => simp [he, hr, bind, Except.bind] at hd
    | ok sr =>
    simp only [he, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    cases τ with
    | bool =>
      simp only [uOfArgs] at hu
      cases hb : uOfB z art none e with
      | none => simp [hb] at hu
      | some b =>
      cases hx : uOfArgs z art rest with
      | none => simp [hb, hx] at hu
      | some xr =>
      simp only [hb, hx, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      simp only [List.mapM_cons, artErg, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hk
      cases hks : τs.mapM artErg with
      | none => simp [hks] at hk
      | some kr =>
      simp only [hks, Option.bind_some, Option.some.injEq] at hk
      subst hk
      simp [uArgs, uArg, bool_ok H e se b he hb, ih sr xr kr hr hx hks]
    | int lo hi =>
      simp only [uOfArgs] at hu
      cases hb : uOfS z art none e with
      | none => simp [hb] at hu
      | some b =>
      cases hx : uOfArgs z art rest with
      | none => simp [hb, hx] at hu
      | some xr =>
      simp only [hb, hx, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      simp only [List.mapM_cons, artErg, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hk
      cases hks : τs.mapM artErg with
      | none => simp [hks] at hk
      | some kr =>
      simp only [hks, Option.bind_some, Option.some.injEq] at hk
      subst hk
      simp [uArgs, uArg, wert_ok H e se b he hb, ih sr xr kr hr hx hks]
    | _ => simp [uOfArgs] at hu

theorem delabA_length {Γ : Ctx} {Λ : List (Res z.deklaration)} :
    ∀ {τs : List Ty} (args : Args z.deklaration Γ Λ τs) (as : List SExpr), delabA z args = .ok as →
      as.length = τs.length := by
  intro τs args
  induction args with
  | nil => intro as hd; simp only [delabA, Except.ok.injEq] at hd; subst hd; rfl
  | cons e rest ih =>
    intro as hd
    simp only [delabA] at hd
    cases he : delabE z none e <;> cases hr : delabA z rest <;>
      simp only [he, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    simp [ih _ hr]

/-- Device handles stand behind every printed argument: the arguments pass unchanged. -/
theorem ohneGriffArgs_ok (ctx : UCtx) (gs : List (Nat × String × String)) :
    ∀ (as : List SExpr) (k : Nat), (∀ g ∈ gs, k + as.length ≤ g.1) → uOhneGriffArgs ctx gs k as = .ok as := by
  intro as
  induction as with
  | nil => intro k _; rfl
  | cons a rest ih =>
    intro k hg
    have hf : gs.find? (fun g => g.1 == k) = none := by
      rw [List.find?_eq_none]
      intro g hm
      have := hg g hm
      simp only [List.length_cons] at this
      simp only [beq_iff_eq]; omega
    simp only [uOhneGriffArgs, hf]
    rw [ih (k + 1) (fun g hm => by have := hg g hm; simp only [List.length_cons] at this; omega)]

/-- **A call**: the callee is found, its locks are held, the arguments read back. -/
theorem ruf_ok {gNr : Nat → Nat} {koepfe : List UFnKopf} {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)}
    {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (f : z.deklaration.Fn) (k : UFnKopf)
    (hf : koepfe.find? (fun k => strEq k.name (nFn (fN z f))) = some k) (hK : KopfPasst gNr f k)
    (hh : ∀ L, L ∈ (z.deklaration.signatur f).haelt → Res.held L ∈ Λ)
    (args : Args z.deklaration Γ Λ (z.deklaration.params f)) (as : List SExpr) (xs : List UArg)
    (hd : delabA z args = .ok as) (hu : uOfArgs z art args = some xs) :
    uRuf ctx tabs koepfe (nFn (fN z f)) as = .ok (k, xs) := by
  have hheld : (k.held.all fun l => ctx.held.any (strEq · l)) = true := by
    rw [List.all_eq_true]
    intro l hl
    obtain ⟨L, hL, rfl⟩ := hK.held l hl
    exact H.held L (hh L hL)
  have hg := ohneGriffArgs_ok ctx k.griffe as 0 (fun g hm => by
    have := hK.griffe g hm; rw [delabA_length args as hd]; omega)
  simp only [uRuf, hf, hheld, Bool.not_true, Bool.false_eq_true, ite_false, hg,
    args_ok H.einv tabs args as xs k.kinds hd hu hK.kinds]

theorem SInv.pushZ {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (k : Nat) (a : UParamArt) (ty : Ty) (b : Nat) (ls : List String) :
    SInv z V (ctxMit ctx (nZeiger k) a ty b [] ls) Γ Λ art where
  var d hd := by
    obtain ⟨j, hj, ha⟩ := H.var d hd
    refine ⟨j + 1, ?_, ha⟩
    simp only [uParamNr, ctxMit, uParamNrAux, strEq_nZeiger_nVar, Bool.false_eq_true, ite_false]
    exact uParamNrAux_succ _ 0 _ j hj
  namen n hn := by
    simp only [ctxMit, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact Or.inr ⟨_, rfl⟩
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
  muts := rfl
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

theorem SInv.fnFremd {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (i : Nat) : ∃ e, uParamNr ctx (nFn i) = .error e :=
  uParamNrAux_fremd ctx.names H.namen 0 _ (fun n hm => strEq_rumpf_nFn (H.namen n hm) i)

/-- `f(..);` -/
theorem anw1_call {gNr : Nat → Nat} {koepfe : List UFnKopf} {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)}
    {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (f : z.deklaration.Fn) (k : UFnKopf)
    (hf : koepfe.find? (fun k => strEq k.name (nFn (fN z f))) = some k) (hK : KopfPasst gNr f k)
    (hh : ∀ L, L ∈ (z.deklaration.signatur f).haelt → Res.held L ∈ Λ) (hr : z.deklaration.gruende f = 0)
    (args : Args z.deklaration Γ Λ (z.deklaration.params f)) (as : List SExpr) (xs : List UArg)
    (hd : delabA z args = .ok as) (hu : uOfArgs z art args = some xs) :
    uAnw1 ctx tabs koepfe (.call (nFn (fN z f)) as) = .ok (.call (nFn (fN z f)) xs) := by
  obtain ⟨e, he⟩ := H.fnFremd (fN z f)
  simp only [uAnw1, uFnZeiger, he, ruf_ok H tabs f k hf hK hh args as xs hd hu, hK.kanal0 hr, Option.isSome_none,
    Bool.false_eq_true, ite_false, hK.ext]

/-- `let p = &f;` -/
theorem bindWert_fnref {gNr : Nat → Nat} {koepfe : List UFnKopf} {ctx : UCtx} {Γ : Ctx}
    {Λ : List (Res z.deklaration)} {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (tabs : List UTab)
    (f : z.deklaration.Fn) (k : UFnKopf) (i : Nat) (hi : koepfe.findIdx? (fun k => strEq k.name (nFn (fN z f))) = some i)
    (hk : koepfe[i]? = some k) (hK : KopfPasst gNr f k) (x : String) :
    uBindWert ctx tabs koepfe false x none (.fnref (nFn (fN z f))) =
      .ok (.bindFnref x (nFn (fN z f)) i, ctxMit ctx x (.fnptr i) (.fnptr i) 0 [] ctx.loops) := by
  obtain ⟨e, he⟩ := H.fnFremd (fN z f)
  have ht : (ctx.tabs.any fun tb => strEq tb.name (nFn (fN z f))) = false := by
    rw [List.any_eq_false]
    intro tb hm
    obtain ⟨j, hj⟩ := H.tabNamen tb hm
    rw [hj, strEq_nTab_nFn]; simp
  simp only [uBindWert, uRegOrt, he, Except.toOption, Option.isSome_none, ht, Bool.or_false, Bool.false_eq_true,
    ite_false, hi, hk, hK.ext, Bool.false_or, H.muts, List.filter_nil, Option.isSome_none]
  rfl

/-- `p(..);` through the pointer `p` just bound to `f`. -/
theorem anw1_callInd {gNr : Nat → Nat} {koepfe : List UFnKopf} {ctx : UCtx} {Γ : Ctx}
    {Λ : List (Res z.deklaration)} {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (tabs : List UTab)
    (f : z.deklaration.Fn) (k : UFnKopf) (i : Nat)
    (hf : koepfe.find? (fun k => strEq k.name (nFn (fN z f))) = some k) (hk : koepfe[i]? = some k)
    (hK : KopfPasst gNr f k) (hh : ∀ L, L ∈ (z.deklaration.signatur f).haelt → Res.held L ∈ Λ)
    (hr : z.deklaration.gruende f = 0)
    (args : Args z.deklaration Γ Λ (z.deklaration.params f)) (as : List SExpr) (xs : List UArg)
    (hd : delabA z args = .ok as) (hu : uOfArgs z art args = some xs) (hb : i < ctx.zeigerBasis) (p : Nat)
    (ls : List String) :
    uAnw1 (ctxMit ctx (nZeiger p) (.fnptr i) (.fnptr i) 0 [] ls) tabs koepfe (.call (nZeiger p) as) =
      .ok (.callInd (nZeiger p) (nFn (fN z f)) xs) := by
  have H' := H.pushZ p (.fnptr i) (.fnptr i) 0 ls
  have hp : uParamNr (ctxMit ctx (nZeiger p) (.fnptr i) (.fnptr i) 0 [] ls) (nZeiger p) = .ok 0 := by
    simp [uParamNr, ctxMit, uParamNrAux]
  have hz : uFnZeiger (ctxMit ctx (nZeiger p) (.fnptr i) (.fnptr i) 0 [] ls) koepfe (nZeiger p) = some (.ok k) := by
    unfold uFnZeiger; rw [hp]; simp [ctxMit, uArtBei, hk, hb]
  have hR := ruf_ok H' tabs f k hf hK hh args as xs hd hu
  simp only [uAnw1, hz, hR, hK.kanal0 hr, Option.isSome_none, Bool.false_eq_true, ite_false, hK.name]

/-- `let x = f(..);` -/
theorem bindWert_call {gNr : Nat → Nat} {koepfe : List UFnKopf} {ctx : UCtx} {Γ : Ctx}
    {Λ : List (Res z.deklaration)} {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (tabs : List UTab)
    (f : z.deklaration.Fn) (k : UFnKopf) (hf : koepfe.find? (fun k => strEq k.name (nFn (fN z f))) = some k)
    (hK : KopfPasst gNr f k) (hh : ∀ L, L ∈ (z.deklaration.signatur f).haelt → Res.held L ∈ Λ)
    (hr : z.deklaration.gruende f = 0) (τ : Ty) (he : z.deklaration.erg f = some τ) (a : UParamArt)
    (ha : artErg τ = some a)
    (args : Args z.deklaration Γ Λ (z.deklaration.params f)) (as : List SExpr) (xs : List UArg)
    (hd : delabA z args = .ok as) (hu : uOfArgs z art args = some xs) (x : String) :
    ∃ ty, uBindWert ctx tabs koepfe false x none (.call (nFn (fN z f)) as) =
      .ok (.bindCall x (nFn (fN z f)) xs, ctxMit ctx x a ty 0 [] ctx.loops) := by
  obtain ⟨e, he'⟩ := H.fnFremd (fN z f)
  have hR := ruf_ok H tabs f k hf hK hh args as xs hd hu
  cases τ with
  | bool =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    refine ⟨.bool, ?_⟩
    simp only [uBindWert, uRegOrt, uFnZeiger, he', hf, hR, hK.kanal0 hr, Option.isSome_none, Bool.false_eq_true,
      ite_false, hK.ext, hK.ergBool he, H.muts, List.filter_nil]
    rfl
  | int lo hi =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    obtain ⟨h1, h2⟩ := hK.ergInt lo hi he
    refine ⟨.int lo hi, ?_⟩
    simp only [uBindWert, uRegOrt, uFnZeiger, he', hf, hR, hK.kanal0 hr, Option.isSome_none, Bool.false_eq_true,
      ite_false, hK.ext, h1, h2, H.muts, List.filter_nil]
    rfl
  | _ => simp [artErg] at ha

/-- `let x = p(..);` through the pointer `p` just bound to `f`. -/
theorem bindWert_callInd {gNr : Nat → Nat} {koepfe : List UFnKopf} {ctx : UCtx} {Γ : Ctx}
    {Λ : List (Res z.deklaration)} {art : Nat → UParamArt} (H : SInv z V ctx Γ Λ art) (tabs : List UTab)
    (f : z.deklaration.Fn) (k : UFnKopf) (i : Nat)
    (hf : koepfe.find? (fun k => strEq k.name (nFn (fN z f))) = some k) (hk : koepfe[i]? = some k)
    (hK : KopfPasst gNr f k) (hh : ∀ L, L ∈ (z.deklaration.signatur f).haelt → Res.held L ∈ Λ)
    (hr : z.deklaration.gruende f = 0) (τ : Ty) (he : z.deklaration.erg f = some τ) (a : UParamArt)
    (ha : artErg τ = some a)
    (args : Args z.deklaration Γ Λ (z.deklaration.params f)) (as : List SExpr) (xs : List UArg)
    (hd : delabA z args = .ok as) (hu : uOfArgs z art args = some xs) (hb : i < ctx.zeigerBasis) (p : Nat)
    (ls : List String) (x : String) :
    ∃ ty, uBindWert (ctxMit ctx (nZeiger p) (.fnptr i) (.fnptr i) 0 [] ls) tabs koepfe false x none
        (.call (nZeiger p) as) =
      .ok (.bindCallInd x (nZeiger p) (nFn (fN z f)) xs,
        ctxMit (ctxMit ctx (nZeiger p) (.fnptr i) (.fnptr i) 0 [] ls) x a ty 0 [] ls) := by
  have H' := H.pushZ p (.fnptr i) (.fnptr i) 0 ls
  have hp : uParamNr (ctxMit ctx (nZeiger p) (.fnptr i) (.fnptr i) 0 [] ls) (nZeiger p) = .ok 0 := by
    simp [uParamNr, ctxMit, uParamNrAux]
  have hz : uFnZeiger (ctxMit ctx (nZeiger p) (.fnptr i) (.fnptr i) 0 [] ls) koepfe (nZeiger p) = some (.ok k) := by
    unfold uFnZeiger; rw [hp]; simp [ctxMit, uArtBei, hk, hb]
  have hR := ruf_ok H' tabs f k hf hK hh args as xs hd hu
  cases τ with
  | bool =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    refine ⟨.bool, ?_⟩
    simp only [uBindWert, uRegOrt, hz, hR, hK.kanal0 hr, Option.isSome_none, Bool.false_eq_true, ite_false,
      hK.ergBool he, hK.name, Bool.or_self]
    rfl
  | int lo hi =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    obtain ⟨h1, h2⟩ := hK.ergInt lo hi he
    refine ⟨.int lo hi, ?_⟩
    simp only [uBindWert, uRegOrt, hz, hR, hK.kanal0 hr, Option.isSome_none, Bool.false_eq_true, ite_false, h1, h2,
      hK.name, Bool.or_self]
    rfl
  | _ => simp [artErg] at ha

/-- `let y = f(..) else (e) { .. }` at the head of a run. -/
theorem reihe_bindElse (tabs : List UTab) (koepfe : List UFnKopf) (f : Nat) (ctx : UCtx) (y c e : String)
    (as : List SExpr) (ss : List SAnw) (en : Option SEnde) (rest : List SAnw) (callee : UFnKopf) (xs : List UArg)
    (num cnt : Nat) (a : UParamArt) (ty : Ty) (ebody : List UStmt) (ctxEB : UCtx) (endS ys : List UStmt) (cE : UCtx)
    (hR : uRuf ctx tabs koepfe c as = .ok (callee, xs)) (hk : callee.kanal = some (num, cnt))
    (hx : callee.ext = false)
    (hv : uWertArt callee = some (a, ty))
    (h1 : uAnwReihe tabs koepfe f (uMitLokal ctx e (.why num) (Ty.why cnt) (ctx.muts.filter (fun m => !strEq m e))) ss =
      .ok (ebody, ctxEB))
    (h2 : uEndeStmt ctxEB en = .ok endS)
    (h3 : uAnwReihe tabs koepfe f (uMitLokal ctx y a ty (ctx.muts.filter (fun m => !strEq m y))) rest = .ok (ys, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.bindElse y none (.call c as) e (.block ss en) :: rest) =
      .ok ([.bindElse y c xs e] ++ ebody ++ endS ++ [.blkEnd] ++ ys, cE) := by
  rw [uAnwReihe] <;> first | (simp only [Option.isSome_none, Bool.false_eq_true, ite_false, hR, hk, hx, hv, h1, h2, h3]) | (intros; simp_all)

/-- Without marks, a call keeps the held resources. -/
theorem nach_ohne_marken (hM : ∀ m : z.deklaration.Marke, False) (S : Signatur z.deklaration.Tab z.deklaration.Glob
    z.deklaration.Lock z.deklaration.Marke) (Λ : List (Res z.deklaration)) : nachSig z.deklaration S Λ = Λ := by
  have h1 : S.konsumiert = [] := by
    cases h : S.konsumiert with
    | nil => rfl
    | cons x _ => exact (hM x.1).elim
  have h2 : S.produziert = [] := by
    cases h : S.produziert with
    | nil => rfl
    | cons x _ => exact (hM x.1).elim
  simp [nachSig, h1, h2]

/-- A call statement at the head of a run. -/
theorem reihe_call (tabs : List UTab) (koepfe : List UFnKopf) (f : Nat) (ctx : UCtx) (c : String) (as : List SExpr)
    (rest : List SAnw) (st : UStmt) (xs : List UStmt) (cE : UCtx) (h1 : uAnw1 ctx tabs koepfe (.call c as) = .ok st)
    (h2 : uAnwReihe tabs koepfe f ctx rest = .ok (xs, cE)) :
    uAnwReihe tabs koepfe (f + 1) ctx (.call c as :: rest) = .ok (st :: xs, cE) := by
  rw [uAnwReihe] <;> first | (simp only [h1, h2]) | (intros; simp_all)

theorem mitLokal_eq (ctx : UCtx) (h : ctx.muts = []) (x : String) (a : UParamArt) (ty : Ty) :
    uMitLokal ctx x a ty (ctx.muts.filter (fun m => !strEq m x)) = ctxMit ctx x a ty 0 [] ctx.loops := by
  simp only [uMitLokal, ctxMit, h, List.filter_nil]

end Gabbro.Grammatik.Gen.Text