import Bruecke.Ausdruck

/-!
# S3, part 3: the statements -- a lowered G statement and its Body statement take related
# states to related states

A slot write through a pointer or at a table (`lowAssignDurch`, `lowAssignTab` against
`stmtBody`'s `.assign`), and the facts the call and the trailing return need.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The writes: the lowering's casts are the constructors -/

theorem assignDurchStmt_eq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabellen.length)
    (fh : FieldHit u t) (p : Expr (declOf u) Γ Λ (.ptr t.val true))
    (ht : (declOf u).tabNr t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.weit.1 fh.weit.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    ∃ e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx), HEq e2 e ∧
      assignDurchStmt u Γ Λ V t fh p ht i e hw hL =
        Stmt.assignDurch (D := declOf u) p t ht fh.idx i e2 hw hL :=
  ⟨_, mpr_heq _ _, rfl⟩

theorem assignSlotStmt_eq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabellen.length)
    (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.weit.1 fh.weit.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    ∃ e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx), HEq e2 e ∧
      assignSlotStmt u Γ Λ V t fh i e hw hL =
        Stmt.assignSlot (D := declOf u) t fh.idx i e2 hw hL :=
  ⟨_, mpr_heq _ _, rfl⟩

/-- **A slot write through a pointer parameter**: the G write and the Body write take related
    states to related states, and the place's carrier is a table the function writes. -/
theorem lowAssignDurch_sim (c : Fin u.fns.length) {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) (resOf u c) (resOf u c)}
    {bst : Gabbro.Body.Stmt}
    (h : lowAssignDurch u c b fname ix v = .ok g)
    (hb : stmtBody u (fnAt u c) (.assign b fname ix v) = some bst)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).schreibt.any (· == cn) = true := by
  unfold lowAssignDurch at h
  split at h
  · cases h
  · rename_i j hj
    split at h
    · rename_i num hp
      split at h
      · rename_i hlt
        split at h
        · cases h
        · rename_i fh hfh
          split at h
          · cases h
          · rename_i pv hpv
            split at h
            · cases h
            · rename_i i hi
              split at h
              · cases h
              · rename_i e he
                split at h
                · rename_i hG
                  split at h
                  · rename_i hw
                    cases h
                    obtain ⟨e2, he2, heq⟩ := assignDurchStmt_eq (ctxOf u c) (resOf u c) (verOf u c)
                      ⟨num, hlt⟩ fh (Expr.var pv) (tabNr_some u num hlt) i e _ hG
                    rw [heq]
                    have hpt := ptrTab_of (fnAt u c) hA b j num true hj hp hlt
                    simp only [stmtBody, hpt] at hb
                    cases hsv : sideExpr u (fnAt u c) v with
                    | none => rw [hsv] at hb; cases hb
                    | some ve =>
                      rw [hsv] at hb
                      cases hb
                      let σl := σ.lese (resOf u c) ((Expr.var (D := declOf u) (Λ := resOf u c) pv).orte ++ i.orte ++ e2.orte)
                      have hWl : WRel u σl s.world := wrel_slots u rfl hW
                      have hv := lowWertAt_sim he hsv hA hT σl σl ρ s.world s.local' hWl hL
                      have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                      have hx : valOf ((declOf u).typ ⟨num, hlt⟩ fh.idx) (eval σl e2 σl ρ) =
                          valOf (.int fh.weit.1 fh.weit.2) (eval σl e σl ρ) :=
                        valOf_eval_heq (typAt_of u ⟨num, hlt⟩ fh.idx fh.weit fh.hit) e2 e he2 σl σl ρ
                      refine ⟨_, (tabAt u ⟨num, hlt⟩).name, (eval σl i σl ρ).n, fname,
                        valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                      · intro ρB
                        simp only [Gabbro.Body.step]
                        rw [hk, hv, ← hx]
                      · exact wrel_slots u rfl (wrel_store u hWl _ ⟨num, hlt⟩ (hT _) fname fh hfh _ _)
                      · exact hw
                  · cases h
                · cases h
      · cases h
    · cases h

/-- **A slot write at a table.** -/
theorem lowAssignTab_sim (c : Fin u.fns.length) {b fname : String} {ix : UIdx} {v : USide}
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) (resOf u c) (resOf u c)}
    {bst : Gabbro.Body.Stmt}
    (h : lowAssignTab u c b fname ix v = .ok g)
    (hb : stmtBody u (fnAt u c) (.assignTab b fname ix v) = some bst)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∃ σ₁ cn k fld val, execStmt O passes R g σ ρ = .ok σ₁ ρ ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.slot cn k fld) val, s.local'⟩) ∧
      WRel u σ₁ (Gabbro.Body.store s.world (.slot cn k fld) val) ∧
      (fnAt u c).schreibt.any (· == cn) = true := by
  unfold lowAssignTab at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h
    · rename_i fh hfh
      split at h
      · cases h
      · rename_i i hi
        split at h
        · cases h
        · rename_i e he
          split at h
          · rename_i hG
            split at h
            · rename_i hw
              cases h
              obtain ⟨e2, he2, heq⟩ := assignSlotStmt_eq (ctxOf u c) (resOf u c) (verOf u c)
                t fh i e _ hG
              rw [heq]
              simp only [stmtBody] at hb
              cases hsv : sideExpr u (fnAt u c) v with
              | none => rw [hsv] at hb; cases hb
              | some ve =>
                rw [hsv] at hb
                cases hb
                let σl := σ.lese (resOf u c) (i.orte ++ e2.orte)
                have hWl : WRel u σl s.world := wrel_slots u rfl hW
                have hv := lowWertAt_sim he hsv hA hT σl σl ρ s.world s.local' hWl hL
                have hk := lowIdx_sim hi σl σl ρ s.world s.local' hL
                have hx : valOf ((declOf u).typ t fh.idx) (eval σl e2 σl ρ) =
                    valOf (.int fh.weit.1 fh.weit.2) (eval σl e σl ρ) :=
                  valOf_eval_heq (typAt_of u t fh.idx fh.weit fh.hit) e2 e he2 σl σl ρ
                refine ⟨_, b, (eval σl i σl ρ).n, fname, valOf _ (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                · intro ρB
                  simp only [Gabbro.Body.step]
                  rw [hk, hv, ← hx]
                · exact wrel_slots u rfl (wrel_store u hWl b t ht fname fh hfh _ _)
                · have hn := tabIdx_name _ _ _ ht
                  have : writesAt u (fnAt u c) t = true := hw
                  unfold writesAt at this
                  rw [show (tabAt u t).name = b from hn] at this
                  exact this
            · cases h
          · cases h

/-! ## 2. The call: arguments, the callee's entry state, its precondition -/

theorem execStmt_heq {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hΛ : Λ₁ = Λ₂) (s₁ : Stmt D V l Γ Λ Λ₁) (s₂ : Stmt D V l Γ Λ Λ₂) (hs : HEq s₁ s₂)
    (σ : World D) (ρ : Env D Γ) : execStmt O passes R s₁ σ ρ = execStmt O passes R s₂ σ ρ := by
  subst hΛ; cases hs; rfl

theorem castNachStmt_heq (caller callee : Fin u.fns.length)
    (s : Stmt (declOf u) (verOf u caller) false (ctxOf u caller)
      (resOf u caller) (nach (declOf u) callee (resOf u caller))) :
    HEq (castNachStmt u caller callee s) s := by
  unfold castNachStmt; exact mp_heq _ _

/-- The Body values of a G environment, in order. -/
def envVals {D : Deklaration} : {Γ : Ctx} → Env D Γ → List Gabbro.Body.Value
  | _, .nil => []
  | τ :: _, .cons v ρ => valOf τ v :: envVals ρ

theorem nthVal_envVals {D : Deklaration} : ∀ {Γ : Ctx} (ρ : Env D Γ) (j : Nat),
    nthVal ρ j = ((envVals ρ)[j]?).getD .absent
  | _, .nil, _ => rfl
  | _ :: _, .cons _ _, 0 => rfl
  | _ :: _, .cons _ ρ, j + 1 => nthVal_envVals ρ j

theorem envVals_length {D : Deklaration} : ∀ {Γ : Ctx} (ρ : Env D Γ), (envVals ρ).length = Γ.length
  | _, .nil => rfl
  | _ :: _, .cons v ρ => by simp [envVals, envVals_length ρ]

/-- A pointer entry reads as `.absent`. -/
theorem nthVal_ptr {D : Deklaration} : ∀ {Γ : Ctx} (ρ : Env D Γ) (j n : Nat) (w : Bool),
    Γ[j]? = some (.ptr n w) → nthVal ρ j = .absent
  | _, .nil, _, _, _, h => rfl
  | _ :: _, .cons v ρ, 0, n, w, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
  | _ :: _, .cons v ρ, j + 1, n, w, h => nthVal_ptr ρ j n w (by simpa using h)

theorem ctxOf_get (c : Fin u.fns.length) (j : Nat) :
    (ctxOf u c)[j]? = ((fnAt u c).params[j]?).map (·.2) := by
  simp [ctxOf]

/-- The names of every function's parameters are distinct. Checked per unit. -/
def NamenEindeutig (fn : UFn) : Prop := (fn.params.map (·.1)).Nodup

/-- A pointer parameter reads as `.absent` in a related binding. -/
theorem lrel_ptr (c : Fin u.fns.length) {ρ : Env (declOf u) (ctxOf u c)} {β : Gabbro.Body.Binding}
    (hL : LRel (fnAt u c) 0 ρ β) (p : String) (j : Nat) (hj : paramPos (fnAt u c).params p = .ok j)
    (n : Nat) (w : Bool) (hτ : ((fnAt u c).params[j]?).map (·.2) = some (.ptr n w)) :
    β p = .absent := by
  rw [hL p j hj, Nat.zero_add]
  exact nthVal_ptr ρ j n w (by rw [ctxOf_get]; exact hτ)

theorem uIdxOfSide_expr {sd : USide} {ix : UIdx} (h : uIdxOfSide sd = .ok ix) :
    sideExpr u fn sd = some (idxExpr ix) := by
  cases sd <;> simp [uIdxOfSide] at h <;> subst h <;> rfl

/-- **One call argument**: the Body argument term evaluates to the G argument value. -/
theorem lowCallArgOne_sim (c : Fin u.fns.length) {k : UParamArt} {τ : Ty} {a : UArg}
    {e : Expr (declOf u) (ctxOf u c) (resOf u c) τ} {eB : Gabbro.Body.Expr}
    (h : lowCallArgOne u c k τ a = .ok e) (hb : argExpr u (fnAt u c) a = some eB)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u) (hN : NamenEindeutig (fnAt u c))
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    Gabbro.Body.eval s eB = some (valOf τ (eval σ₀ e σ ρ)) := by
  cases a with
  | var p =>
    simp only [argExpr, Option.some.injEq] at hb
    subst hb
    simp only [lowCallArgOne] at h
    split at h
    · split at h
      · split at h
        · split at h
          · cases h
          · rename_i j hj
            split at h
            · rename_i num2 w2 hp
              obtain ⟨w3, hw3⟩ := hA j num2 w2 hp
              have hab := lrel_ptr c hL p j hj num2 w3 hw3
              have goal : Gabbro.Body.eval s (.name p) = some .absent := by
                simp only [Gabbro.Body.eval, hab]
              repeat' split at h
              all_goals first | (cases h; exact goal) | cases h
            · cases h
        · cases h
      · cases h
    · split at h <;> cases h
    · cases h
    · cases h
  | freshPtr tname w2 =>
    simp only [argExpr] at hb
    cases hq : ptrParam u (fnAt u c) tname with
    | none => rw [hq] at hb; cases hb
    | some p' =>
      rw [hq] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      subst hb
      have goal : Gabbro.Body.eval s (.name p') = some .absent := by
        unfold ptrParam at hq
        split at hq
        · rename_i q hfil
          simp only [Option.some.injEq] at hq
          subst hq
          have hmem := hfil ▸ List.mem_singleton_self q
          rw [List.mem_filter] at hmem
          obtain ⟨hqm, hqp⟩ := hmem
          obtain ⟨jq, hjq⟩ := List.mem_iff_getElem?.mp hqm
          have hpos := paramPos_of_nodup _ jq q.1 q.2 hN (by rw [hjq])
          have hty : ∃ tn tw, q.2 = .ptr tn tw := by
            revert hqp
            cases q.2 <;> simp
          obtain ⟨tn, tw, htq⟩ := hty
          have hab := lrel_ptr c hL q.1 jq hpos tn tw (by rw [hjq]; simp [htq])
          simp only [Gabbro.Body.eval, hab]
        · cases hq
      simp only [lowCallArgOne] at h
      split at h
      · repeat' split at h
        all_goals first | (cases h; exact goal) | cases h
      · split at h <;> cases h
      · cases h
      · cases h
  | wert sd =>
    simp only [argExpr] at hb
    simp only [lowCallArgOne] at h
    split at h
    · cases h
    · split at h
      · rename_i num _ lo hi
        split at h
        · rename_i hlt
          split at h
          · rename_i hLo
            split at h
            · rename_i hHi
              split at h
              · cases h
              · rename_i ix hix
                split at h
                · cases h
                · rename_i ei hei
                  cases h
                  rw [uIdxOfSide_expr hix] at hb
                  cases hb
                  rw [lowIdx_sim hei σ₀ σ ρ s.world s.local' hL]
                  have hτ : Ty.int lo hi = Ty.index ((declOf u).count ⟨num, hlt⟩) := by rw [hLo, hHi]
                  rw [valOf_eval_heq hτ _ ei ((mpr_heq _ _).trans (mpr_heq _ _)) σ₀ σ ρ]
                  rfl
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · cases h
      · rename_i e' he'
        cases h
        cases s
        exact lowWertAt_sim he' hb hA hT σ₀ σ ρ _ _ hW hL
    · cases h

/-- **The argument list.** -/
theorem lowCallArgsAux_sim (c : Fin u.fns.length)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u) (hN : NamenEindeutig (fnAt u c))
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∀ (ks : List UParamArt) (ts : List Ty) (as : List UArg)
      (a : Args (declOf u) (ctxOf u c) (resOf u c) ts) (es : List Gabbro.Body.Expr),
      lowCallArgsAux u c ks ts as = .ok a → argsExpr u (fnAt u c) as = some es →
      Gabbro.Body.evalAll s es = some (envVals (evalArgs σ₀ a σ ρ))
  | [], ts, as, a, es, h, hb => by
      simp only [lowCallArgsAux] at h
      split at h
      · cases h
        simp only [argsExpr, Option.some.injEq] at hb
        subst hb
        rfl
      · cases h
  | k :: ks, ts, as, a, es, h, hb => by
      simp only [lowCallArgsAux] at h
      split at h
      · rename_i t ts' x as'
        split at h
        · cases h
        · rename_i e he
          split at h
          · cases h
          · rename_i rest hrest
            cases h
            simp only [argsExpr] at hb
            split at hb
            · rename_i eB esB hx hxs
              simp only [Option.some.injEq] at hb
              subst hb
              have h1 := lowCallArgOne_sim c he hx hA hT hN σ₀ σ ρ s hW hL
              have h2 := lowCallArgsAux_sim c hA hT hN σ₀ σ ρ s hW hL ks ts' as' rest esB hrest hxs
              simp only [Gabbro.Body.evalAll, h1, h2]
              rfl
            · cases hb
      · cases h

theorem bindAll_fremd : ∀ (ns : List String) (vs : List Gabbro.Body.Value) (β : Gabbro.Body.Binding)
    (p : String), p ∉ ns → Gabbro.Body.bindAll ns vs β p = β p
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | n :: ns, v :: vs, β, p, h => by
      simp only [Gabbro.Body.bindAll]
      rw [bindAll_fremd ns vs _ p (fun hm => h (List.mem_cons_of_mem _ hm))]
      exact Gabbro.Body.bindLocal_elsewhere _ _ _ _ (fun e => h (e ▸ List.mem_cons_self ..))

/-- **The callee's entry binding** (`bindAll` in `Body.step`) holds, at every parameter name, the
    argument at that name's position -- the names being distinct. -/
theorem bindAll_at : ∀ (P : List (String × Ty)) (vs : List Gabbro.Body.Value)
    (β : Gabbro.Body.Binding) (p : String) (j : Nat),
    (P.map (·.1)).Nodup → P.length = vs.length → paramPos P p = .ok j →
    Gabbro.Body.bindAll (P.map (·.1)) vs β p = (vs[j]?).getD .absent
  | [], _, _, _, _, _, _, h => by simp [paramPos] at h
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl
  | (q, τ) :: P, v :: vs, β, p, j, hn, hl, h => by
      simp only [List.map_cons, List.nodup_cons] at hn
      simp only [List.map_cons, Gabbro.Body.bindAll]
      unfold paramPos at h
      split at h
      · rename_i hq
        cases h
        have : q = p := by simpa using hq
        subst this
        rw [bindAll_fremd _ _ _ _ hn.1]
        simp
      · rename_i hq
        split at h
        · cases h
        · rename_i k hk
          cases h
          have hqp : p ≠ q := fun e => hq (by simp [e])
          rw [bindAll_at P vs _ p k hn.2 (by simpa using hl) hk]
          simp

/-- The callee's LRel in its Body entry state. -/
theorem lrel_bindAll {D : Deklaration} {Γ : Ctx} (fn : UFn) (ρ : Env D Γ)
    (hN : NamenEindeutig fn) (hl : fn.params.length = Γ.length) :
    LRel fn 0 ρ (Gabbro.Body.bindAll (fn.params.map (·.1)) (envVals ρ) (fun _ => .absent)) := by
  intro p j hj
  rw [bindAll_at fn.params (envVals ρ) _ p j hN (by rw [envVals_length, hl]) hj, Nat.zero_add,
    nthVal_envVals]

theorem nthVal_int {D : Deklaration} : ∀ {Γ : Ctx} (ρ : Env D Γ) (j : Nat) (lo hi : Int),
    Γ[j]? = some (.int lo hi) → ∃ n, nthVal ρ j = .int n ∧ lo ≤ n ∧ n ≤ hi
  | _, .nil, _, _, _, h => by simp at h
  | _ :: _, .cons v ρ, 0, lo, hi, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨(v : Zahl lo hi).n, rfl, v.lo_le, v.le_hi⟩
  | _ :: _, .cons v ρ, j + 1, lo, hi, h => nthVal_int ρ j lo hi (by simpa using h)

theorem eval_conjE (t : Gabbro.Body.State) : ∀ (es : List Gabbro.Body.Expr),
    (∀ e ∈ es, Gabbro.Body.eval t e = some (.bool true)) →
    Gabbro.Body.eval t (conjE es) = some (.bool true)
  | [], _ => rfl
  | [e], h => h e (List.mem_singleton_self _)
  | e :: e' :: es, h => by
      simp only [conjE, Gabbro.Body.eval]
      rw [h e (List.mem_cons_self ..),
        eval_conjE t (e' :: es) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      rfl

/-- **The callee's precondition holds at its Body entry state**: every declared shape is the
    shape of a typed G value, and a `Held` clause reads `true`. -/
theorem preExpr_wahr {D : Deklaration} {Γ : Ctx} (fn : UFn) (ρ : Env D Γ) (β : Gabbro.Body.Binding)
    (w : Gabbro.Body.World) (hN : NamenEindeutig fn) (hΓ : Γ = fn.params.map (·.2))
    (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ (preExpr fn) = some (.bool true) := by
  apply eval_conjE
  intro e he
  rw [List.mem_append] at he
  rcases he with he | he
  · unfold shapeConjuncts at he
    rw [List.mem_filterMap] at he
    obtain ⟨q, hq, hqe⟩ := he
    cases hsh : shapeOfTy q.2 with
    | none => rw [hsh] at hqe; cases hqe
    | some sh =>
      rw [hsh] at hqe
      simp only [Option.map_some, Option.some.injEq] at hqe
      subst hqe
      obtain ⟨jq, hjq⟩ := List.mem_iff_getElem?.mp hq
      obtain ⟨qn, qτ⟩ := q
      have hpos := paramPos_of_nodup _ jq qn qτ hN (by rw [hjq])
      cases qτ with
      | int lo hi =>
        simp only [shapeOfTy, Option.some.injEq] at hsh
        subst hsh
        obtain ⟨n, hn, hlo, hhi⟩ := nthVal_int ρ jq lo hi (by rw [hΓ]; simp [hjq])
        simp only [Gabbro.Body.eval]
        rw [hL qn jq hpos, Nat.zero_add, hn]
        simp [hlo, hhi]
      | _ => simp [shapeOfTy] at hsh
  · rw [List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    rfl

/-- **A direct call.** On the G side the call asks the handler `R` for the callee at the read
    world `σr` with the evaluated arguments `envA`, and takes its answer; on the Body side the step
    asks the environment for the callee at the entry state `⟨s.world, bindAll … (envVals envA) …⟩`
    (the callee's precondition holds there) and takes its world. -/
theorem lowCall_sim (c : Fin u.fns.length) {cname : String} {args : List UArg}
    {g : Stmt (declOf u) (verOf u c) false (ctxOf u c) (resOf u c) (resOf u c)}
    {bst : Gabbro.Body.Stmt}
    (h : lowCall u c cname args = .ok g)
    (hb : stmtBody u (fnAt u c) (.call cname args) = some bst)
    (hA : ArtStimmt (fnAt u c)) (hT : TabEindeutig u) (hN : ∀ c', NamenEindeutig (fnAt u c'))
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) (ctxOf u c)) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel (fnAt u c) 0 ρ s.local') :
    ∃ (callee : Fin u.fns.length) (σr : World (declOf u))
      (envA : Env (declOf u) ((declOf u).params callee)),
      cname = (fnAt u callee).name ∧ fnSuch u cname = some (fnAt u callee) ∧ σr.slots = σ.slots ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB bst s = .running ⟨(ρB cname
          ⟨s.world, Gabbro.Body.bindAll ((fnAt u callee).params.map (·.1)) (envVals envA)
            (fun _ => .absent)⟩).1.world, s.local'⟩) ∧
      LRel (fnAt u callee) 0 envA
        (Gabbro.Body.bindAll ((fnAt u callee).params.map (·.1)) (envVals envA) (fun _ => .absent)) ∧
      Gabbro.Body.eval ⟨s.world, Gabbro.Body.bindAll ((fnAt u callee).params.map (·.1))
        (envVals envA) (fun _ => .absent)⟩ (preExpr (fnAt u callee)) = some (.bool true) ∧
      ((∃ σ' v, R callee σr envA = .ok σ' v ∧ execStmt O passes R g σ ρ = .ok σ' ρ) ∨
        (∃ e, R callee σr envA = .logik e ∧ execStmt O passes R g σ ρ = .logik e) ∨
        (∃ e, R callee σr envA = .hardware e ∧ execStmt O passes R g σ ρ = .hardware e)) ∧
      (∀ t, writesAt u (fnAt u callee) t = true → writesAt u (fnAt u c) t = true) := by
  unfold lowCall at h
  split at h
  · cases h
  · rename_i callee hcallee
    split at h
    · cases h
    · rename_i a ha
      split at h
      · rename_i hWr
        split at h
        · rename_i hH
          split at h
          · rename_i hX
            cases h
            -- the Body side
            have hfs : fnSuch u cname = some (fnAt u callee) := fnIdx_find _ _ _ hcallee
            simp only [stmtBody, hfs] at hb
            cases hes : argsExpr u (fnAt u c) args with
            | none => rw [hes] at hb; cases hb
            | some es =>
              rw [hes] at hb
              simp only [Option.some.injEq] at hb
              subst hb
              let σr := σ.lese (resOf u c) a.orte
              have hWr' : WRel u σr s.world := wrel_slots u rfl hW
              have hev := lowCallArgsAux_sim c hA hT (hN c) σr σr ρ s hWr' hL _ _ _ a es ha hes
              have hlen : (fnAt u callee).params.length = ((declOf u).params callee).length := by
                rw [params_eq]; simp
              have hLc := lrel_bindAll (fnAt u callee) (evalArgs σr a σr ρ) (hN callee) hlen
              have hpre := preExpr_wahr (fnAt u callee) (evalArgs σr a σr ρ) _ s.world (hN callee)
                (params_eq u callee) hLc
              refine ⟨callee, σr, evalArgs σr a σr ρ, (fnIdx_name _ _ _ hcallee).symm, hfs, rfl,
                fun ρB => ?_, hLc, hpre, ?_, hWr⟩
              · simp only [Gabbro.Body.step, hev, hpre]
              · rw [execStmt_heq O passes R (nach_eq u callee (resOf u c)).symm _ _
                  (castNachStmt_heq c callee _) σ ρ]
                simp only [execStmt]
                cases hR : R callee σr (evalArgs σr a σr ρ) with
                | ok σ' v => exact .inl ⟨σ', v, rfl, rfl⟩
                | grund σ' r => exact absurd r.isLt (by have := sigGruende_zero u callee; omega)
                | logik e => exact .inr (.inl ⟨e, rfl, rfl⟩)
                | hardware e => exact .inr (.inr ⟨e, rfl, rfl⟩)
          · cases h
        · cases h
      · cases h

end Gabbro.Bruecke
