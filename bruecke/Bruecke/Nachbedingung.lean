import Bruecke.Anweisung
import Bruecke.Start

/-!
# S3, part 4: what the lowering says about the program, and a function's promise

`Gesenkt u P` collects what `lowerAllg u = .ok (P, fs)` says about `P`: no `requires`, and every
`ensures` and every body is the lowering's (up to the type transports of `lowerFnAt`).
`post_iff` is the promise of one function: the duty file's `postU` over related Body states is
the goal theorem's `EnsAmRueck` over the G states, both ways.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- What the lowering says about the program. -/
structure Gesenkt (u : UProg) (P : Programm (declOf u)) : Prop where
  req : ∀ f, P.requires f = .wahr
  ens : ∀ f, ∃ e0, lowEnsList u (ErgCtx (ctxOf u f) (verOf u f).erg) (resOf u f) (fnAt u f)
      (fnAt u f).ergebnis (fnAt u f).sichert = .ok e0 ∧ HEq (P.ensures f) e0
  rumpf : ∀ f, ∃ b0, lowBody u f (fnAt u f).saetze (fnAt u f).rueck = .ok b0 ∧ HEq (P.rumpf f) b0

theorem lowerFnAt_ok (c : Fin u.fns.length) {v : EnsTy u c × RumpTy u c}
    (h : lowerFnAt u c = .ok v) :
    ∃ e0 b0, lowEnsList u (ErgCtx (ctxOf u c) (verOf u c).erg) (resOf u c) (fnAt u c)
      (fnAt u c).ergebnis (fnAt u c).sichert = .ok e0 ∧
      lowBody u c (fnAt u c).saetze (fnAt u c).rueck = .ok b0 ∧ HEq v.1 e0 ∧ HEq v.2 b0 := by
  unfold lowerFnAt at h
  split at h
  · cases h
  · rename_i e0 he0
    split at h
    · cases h
    · rename_i b0 hb0
      cases h
      refine ⟨e0, b0, he0, hb0, ?_, ?_⟩
      · dsimp only; exact mpr2_heq _ _ _
      · dsimp only; exact mpr2_heq _ _ _

theorem lowerAtPair_eq (f : Fin u.fns.length) (h : ∃ v, lowerFnAt u f = .ok v)
    {v : EnsTy u f × RumpTy u f} (hv : lowerFnAt u f = .ok v) : lowerAtPair u f h = v := by
  unfold lowerAtPair
  split
  · rename_i v' hv'
    rw [hv] at hv'
    cases hv'
    rfl
  · rename_i e he
    rw [hv] at he
    cases he

/-- **What `lowerAllg` says about the program it answers.** -/
theorem gesenkt_of {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : lowerAllg u = .ok (P, fs)) : Gesenkt u P := by
  have hreq := lowerAllg_requires u P fs h
  unfold lowerAllg at h
  split at h
  · cases h
  · rename_i hall
    injection h with h1
    injection h1 with h2 h3
    subst h2
    refine ⟨hreq, fun f => ?_, fun f => ?_⟩
    · have w := lowerEach_all_ok u (List.finRange u.fns.length) f (List.mem_finRange f) hall
      obtain ⟨v, hv⟩ := w
      obtain ⟨e0, b0, he, hb, he', _⟩ := lowerFnAt_ok f hv
      refine ⟨e0, he, ?_⟩
      show HEq (lowerAtPair u f _).1 e0
      rw [lowerAtPair_eq f _ hv]
      exact he'
    · have w := lowerEach_all_ok u (List.finRange u.fns.length) f (List.mem_finRange f) hall
      obtain ⟨v, hv⟩ := w
      obtain ⟨e0, b0, he, hb, _, hb'⟩ := lowerFnAt_ok f hv
      refine ⟨b0, hb, ?_⟩
      show HEq (lowerAtPair u f _).2 b0
      rw [lowerAtPair_eq f _ hv]
      exact hb'

/-! ## The answer and the `ensures` environment -/

/-- A G answer as the Body result: none, or the value. -/
def ergValOf {D : Deklaration} : (e : Option Ty) → ErgVal D e → Option Gabbro.Body.Value
  | none, _ => none
  | some τ, v => some (valOf τ v)

theorem ergValOf_nth {D : Deklaration} {Γ : Ctx} : ∀ (e : Option Ty) (v : ErgVal D e) (ρ : Env D Γ),
    e.isSome = true → ergValOf e v = some (nthVal (ergEnv e v ρ) 0)
  | none, _, _, h => by cases h
  | some _, _, _, _ => rfl

theorem nthVal_ergEnv {D : Deklaration} {Γ : Ctx} : ∀ (e : Option Ty) (v : ErgVal D e) (ρ : Env D Γ)
    (j : Nat), nthVal (ergEnv e v ρ) ((if e.isSome then 1 else 0) + j) = nthVal ρ j
  | none, _, _, j => by simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]; rfl
  | some _, _, _, j => by
      simp only [Option.isSome_some, ↓reduceIte]
      rw [Nat.add_comm]; rfl

theorem nthVal_heq {D : Deklaration} {Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (ρ₁ : Env D Γ₁) (ρ₂ : Env D Γ₂)
    (hρ : HEq ρ₁ ρ₂) (j : Nat) : nthVal ρ₁ j = nthVal ρ₂ j := by
  subst h; cases hρ; rfl

theorem eval_heq2 {D : Deklaration} {Γ₁ Γ₂ : Ctx} {Λ₁ Λ₂ : List (Res D)} (hΓ : Γ₁ = Γ₂)
    (hΛ : Λ₁ = Λ₂) (e₁ : Expr D Γ₁ Λ₁ .bool) (e₂ : Expr D Γ₂ Λ₂ .bool) (he : HEq e₁ e₂)
    (ρ₁ : Env D Γ₁) (ρ₂ : Env D Γ₂) (hρ : HEq ρ₁ ρ₂) (σ₀ σ : World D) :
    eval σ₀ e₁ σ ρ₁ = eval σ₀ e₂ σ ρ₂ := by
  subst hΓ; subst hΛ; cases he; cases hρ; rfl

/-- Without a `bool` result the result type is the recorded range. -/
theorem ergTy_of {f : UFn} (h : f.ergBool = false) :
    f.ergTy = f.ergebnis.map fun r => Ty.int r.1 r.2 := by
  unfold UFn.ergTy; rw [h]; rfl

theorem isSome_erg (f : Fin u.fns.length) (hb : (fnAt u f).ergBool = false) :
    ((declOf u).erg f).isSome = (fnAt u f).ergebnis.isSome := by
  rw [erg_eq, ergTy_of hb]; simp

/-- The answer clause of the promise holds for every typed answer. -/
theorem resultClause_wahr (f : Fin u.fns.length) (hb : (fnAt u f).ergBool = false) :
    ∀ v : ErgVal (declOf u) ((declOf u).erg f),
      ∀ q ∈ (resultClause (fnAt u f) (ergValOf ((declOf u).erg f) v)).toList, q := by
  have he := (erg_eq u f).trans (ergTy_of hb)
  revert he
  generalize (declOf u).erg f = e
  intro he v q hq
  subst he
  cases hr : (fnAt u f).ergebnis with
  | none => simp [resultClause, hr] at hq
  | some lr =>
    simp only [resultClause, hr, Option.map_some, Option.toList_some, List.mem_singleton] at hq
    subst hq
    obtain ⟨lo, hi⟩ := lr
    revert v
    rw [hr]
    intro v
    exact ⟨(v : Zahl lo hi).n, rfl, v.lo_le, v.le_hi⟩

/-- Every clause of the promise is in the fragment. Checked per unit. -/
def PostDef (u : UProg) (fn : UFn) : Prop := ∀ e ∈ fn.sichert, (ensExpr u fn {} e).isSome = true

theorem ensList_some (fn : UFn) (s s' : Gabbro.Body.State) (r : Option Gabbro.Body.Value) :
    ∀ es : List UEns, (∀ e ∈ es, (ensExpr u fn {} e).isSome = true) →
      ∃ cs, ensList u fn s s' r es = some cs
  | [], _ => ⟨[], rfl⟩
  | e :: es, h => by
      obtain ⟨cs, hcs⟩ := ensList_some fn s s' r es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
      have he := h e (List.mem_cons_self ..)
      cases hx : ensExpr u fn {} e with
      | none => rw [hx] at he; cases he
      | some xa =>
        exact ⟨_, by simp only [ensList, ensClause, hx, hcs, Option.map_some]; rfl⟩

/-- The unit's well-typed world, as the bridge states it (the duty files' `wellFormed`,
    `Instanz*.wf_eq`). -/
def wfU (u : UProg) (s : Gabbro.Body.State) : Prop := Gabbro.Body.WF (shapeOfU u) s.world

/-- **The promise of one function**: over Body states related to the G entry and exit, the
    duty file's promise is exactly the goal theorem's return check. -/
theorem post_iff {P : Programm (declOf u)} (G : Gesenkt u P) (f : Fin u.fns.length)
    (hA : ArtStimmt (fnAt u f)) (hT : TabEindeutig u) (hN : NamenFrei (fnAt u f))
    (hO : OldsKurz u (fnAt u f)) (hD : PostDef u (fnAt u f))
    (hBE : (fnAt u f).ergBool = false) (hBT : ∀ t : Fin u.tabellen.length, (tabAt u t).bools = [])
    (σ₀ σ' : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params f))
    (v : ErgVal (declOf u) ((declOf u).erg f)) (s s' : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s.world) (hL₀ : LRel (fnAt u f) 0 ρ s.local') (hW : WRel u σ' s'.world) :
    (postU u (wfU u) (fnAt u f) s s' (ergValOf ((declOf u).erg f) v)).getD False ↔
      EnsAmRueck P f σ₀ σ' ρ v := by
  obtain ⟨cs, hcs⟩ := ensList_some (fnAt u f) s s' (ergValOf ((declOf u).erg f) v) _ hD
  obtain ⟨e0, he0, hPe⟩ := G.ens f
  let E := ergEnv ((declOf u).erg f) v ρ
  let E₀ : Env (declOf u) (ErgCtx (ctxOf u f) (verOf u f).erg) :=
    cast (congrArg (Env (declOf u)) (ensCtx_eq u f).symm) E
  have hE : HEq E₀ E := cast_heq _ _
  have hL : LRel (fnAt u f) (if (fnAt u f).ergebnis.isSome then 1 else 0) E₀ s.local' := by
    intro p j hj
    rw [nthVal_heq (ensCtx_eq u f) E₀ E hE, ← isSome_erg f hBE, nthVal_ergEnv]
    exact (hL₀ p j hj).trans (by rw [Nat.zero_add])
  have her : (fnAt u f).ergebnis.isSome = true →
      ergValOf ((declOf u).erg f) v = some (nthVal E₀ 0) := by
    intro h
    rw [nthVal_heq (ensCtx_eq u f) E₀ E hE]
    exact ergValOf_nth _ v ρ (by rw [isSome_erg f hBE]; exact h)
  have hcl := ensList_iff hA hT hN σ₀ σ' E₀ s s' hW₀ hL hW _ her (fnAt u f).sichert cs e0
    hO hcs he0
  have hev : eval σ₀ (P.ensures f) σ' E = eval σ₀ e0 σ' E₀ :=
    eval_heq2 (ensCtx_eq u f).symm (endeRes_eq u f).symm _ _ hPe E E₀ hE.symm σ₀ σ'
  unfold EnsAmRueck
  rw [show ergEnv ((declOf u).erg f) v ρ = E from rfl, hev, ← hcl]
  simp only [postU, hcs, Option.getD_some]
  rw [chain_iff]
  have hrc := resultClause_wahr f hBE v
  constructor
  · intro ⟨_, hall⟩ q hq
    exact hall q (List.mem_append_right _ hq)
  · intro hall
    refine ⟨wf_of_wrel u hBT hW, fun q hq => ?_⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact hrc q hq
    · exact hall q hq

/-! ## The trailing return -/

/-- The Body tail `zuBody` appends for the trailing return. -/
def endBody (u : UProg) (fn : UFn) : URet → Option (List Gabbro.Body.Stmt)
  | .keine => some []
  | .wert v => (sideExpr u fn v).map (fun e => [.ret (some e)])
  | .bool _ => none

theorem zuBody_eq (fn : UFn) : zuBody u fn =
    match stmtsBody u fn fn.saetze with
    | none => none
    | some ss => (endBody u fn fn.rueck).map (ss ++ ·) := by
  unfold zuBody
  cases stmtsBody u fn fn.saetze with
  | none => rfl
  | some ss =>
    cases fn.rueck with
    | keine => simp [endBody]
    | wert v => simp only [endBody, Option.map_map]; rfl
    | bool _ => simp [endBody]

theorem ergValOf_heq {D : Deklaration} {e₁ e₂ : Option Ty} (h : e₁ = e₂) (x₁ : ErgVal D e₁)
    (x₂ : ErgVal D e₂) (hx : HEq x₁ x₂) : ergValOf e₁ x₁ = ergValOf e₂ x₂ := by
  subst h; cases hx; rfl

theorem evalErg_heq {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {e₁ e₂ : Option Ty} (h : e₁ = e₂)
    (E₁ : ErgExpr D Γ Λ e₁) (E₂ : ErgExpr D Γ Λ e₂) (hE : HEq E₁ E₂) (σ₀ σ : World D) (ρ : Env D Γ) :
    HEq (evalErg σ₀ E₁ σ ρ) (evalErg σ₀ E₂ σ ρ) := by
  subst h; cases hE; rfl

theorem ergOrte_heq {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {e₁ e₂ : Option Ty} (h : e₁ = e₂)
    (E₁ : ErgExpr D Γ Λ e₁) (E₂ : ErgExpr D Γ Λ e₂) (hE : HEq E₁ E₂) : E₁.orte = E₂.orte := by
  subst h; cases hE; rfl

theorem ergValOf_none {D : Deklaration} {e : Option Ty} (x : ErgVal D e) (h : e = none) :
    ergValOf e x = none := by
  subst h; rfl

/-- **The trailing return**: G returns (the read world, the answer); the Body tail ends in the
    same state with the same answer. -/
theorem lowEnd_sim (c : Fin u.fns.length) {r : URet}
    {eb : Endblock (declOf u) (verOf u c) false (ctxOf u c) (resOf u c)} {eB : List Gabbro.Body.Stmt}
    (h : lowEnd u c r = .ok eb) (hb : endBody u (fnAt u c) r = some eB)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∃ σ' v, execEnd O passes R eb σ ρ = .zurueck σ' v ∧ σ'.slots = σ.slots ∧
      ∀ ρB : Gabbro.Body.Env, Gabbro.Body.finalState (Gabbro.Body.exec ρB eB s) = some s ∧
        Gabbro.Body.finalValue (Gabbro.Body.exec ρB eB s) = ergValOf (verOf u c).erg v := by
  cases r with
  | bool _ => simp [endBody] at hb
  | keine =>
    simp only [endBody, Option.some.injEq] at hb
    subst hb
    revert h
    simp only [lowEnd]
    split
    · rename_i hE
      intro h
      cases h
      refine ⟨_, _, rfl, rfl, fun ρB => ⟨rfl, ?_⟩⟩
      have he : (verOf u c).erg = none := by
        show (vertragVon (declOf u) c).erg = none
        rw [vErg_eq u c, hE]
      rw [ergValOf_none _ he]
      rfl
    · intro h; cases h
  | wert sd =>
    simp only [endBody] at hb
    cases hs : sideExpr u (fnAt u c) sd with
    | none => rw [hs] at hb; cases hb
    | some e =>
      rw [hs] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      revert h
      simp only [lowEnd]
      split
      · rename_i lo hi hE
        split
        · intro h; cases h
        · rename_i ve hve
          intro h
          cases h
          refine ⟨_, _, rfl, rfl, fun ρB => ?_⟩
          obtain ⟨sw, sl⟩ := s
          have herg : (verOf u c).erg = some (.int lo hi) := by
            show (vertragVon (declOf u) c).erg = _
            rw [vErg_eq u c, hE]
          generalize hσl : σ.lese _ _ = σl
          have hWl : WRel u σl sw := by rw [← hσl]; exact wrel_slots u rfl hW
          have hv := lowWertAt_sim hve hs hA hT σl σl ρ sw sl hWl hL
          rw [ergValOf_heq herg _ (evalErg σl (ErgExpr.wert (D := declOf u) ve) σl ρ)
            (evalErg_heq herg _ _ (mpr3_heq _ _ _ _) _ _ _)]
          simp only [Gabbro.Body.exec, Gabbro.Body.step, hv, Gabbro.Body.finalState,
            Gabbro.Body.finalValue]
          trivial
      · intro h; cases h
      · intro h; cases h

end Gabbro.Bruecke
