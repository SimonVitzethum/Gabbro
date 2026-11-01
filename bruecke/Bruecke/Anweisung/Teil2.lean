module

public import Bruecke.Ausdruck
public import Bruecke.Anweisung.Teil1

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

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
  unfold lowCall lowCallL at h
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
                | why σ' r => exact absurd r.isLt (by have := sigGruende_zero u callee; omega)
                | logik e => exact .inr (.inl ⟨e, rfl, rfl⟩)
                | hardware e => exact .inr (.inr ⟨e, rfl, rfl⟩)
          · cases h
        · cases h
      · cases h

/-- A statement the bridge accepts is not a `locks` marker (the bridge refuses them by name). -/
theorem stmtBody_nomark (f : UFn) (st : UStmt) (h : (stmtBody u f st).isSome = true) :
    ∀ g, st ≠ UStmt.sperrtAuf g := by
  intro g e
  subst e
  simp [stmtBody] at h

/-- The cons step of the body reader for a statement that opens no `locks` block. -/
theorem lowBody_cons (c : Fin u.fns.length) (r : URet) (s : UStmt) (ss : List UStmt)
    (h : ∀ g, s ≠ UStmt.sperrtAuf g) :
    lowBody u c (s :: ss) r =
      (match lowStmt u c s with
       | .error e => .error e
       | .ok st =>
         match lowBody u c ss r with
         | .error e => .error e
         | .ok e => .ok (Endblock.cons st e)) := by
  cases s with
  | sperrtAuf g => exact absurd rfl (h g)
  | _ => rfl

theorem stmtsBody_isSome {f : UFn} {ss : List UStmt} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBody u f ss = some bs) : ∀ st ∈ ss, (stmtBody u f st).isSome = true := by
  induction ss generalizing bs with
  | nil => intro st hm; exact absurd hm List.not_mem_nil
  | cons s ss ih =>
    intro st hm
    simp only [stmtsBody] at h
    split at h
    · rename_i x xs hx hxs
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [hx]; rfl
      · exact ih hxs st hm
    · cases h

end Gabbro.Bruecke
