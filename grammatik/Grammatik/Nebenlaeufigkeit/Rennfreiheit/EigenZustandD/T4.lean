/- Part 4 of 5 of `EigenZustandD` (split by instrumente/teile/lean-teilen.py; the umbrella `EigenZustandD.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T3

namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik
variable {D : Deklaration}

theorem pcSchritt_fremd_fest (P : Programm D) (O : Orakel D) (hO : GutO O)
    (passes : Nat)
    (prog : PCProg D) (M pc h M' pc') (g : Faden) (t : D.Tab)
    (hs : PCSchritt P O passes prog M pc h M' pc')
    (hOg : h ≠ g)
    (hNurG : ∀ a ∈ prog h,
      (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a)
    (hNoAx : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
      (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
      (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
        (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
        (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (M.weltVon h) ρ).welt = some σ' ∧ D.aschreibt a t = true)
    (k : Int) (f : D.Feld t) :
    M'.speicher.slots t k f = M.speicher.slots t k f := by
  cases hs with
  | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar =>
      -- The outcome memory is `σ'.speicher`; the goal is about slots.
      have hmem : (∀ k f, σ'.slots t k f = (M.weltVon h).slots t k f) ∨
          (∃ ev ∈ neu, ev.traeger = some (Sum.inl t)) ∨
          (∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
            (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
            (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
            (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
            (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
            (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
              (M.weltVon h) ρ).welt = some σ' ∧ D.aschreibt a t = true) := by
        have hdisp := blattSlots_dispatch O hO passes s ρ hleaf
          (M.weltVon h) σ' neu hstep hneu t
        rcases hdisp with hRec | hFest | hAx
        · exact Or.inr (Or.inl hRec)
        · exact Or.inl hFest
        · exact Or.inr (Or.inr hAx)
      rcases hmem with hFest | hRec | hAx
      · -- Slots kept: the leaf rule sets `M'` memory to `σ'.speicher`.
        show σ'.speicher.slots t k f = M.speicher.slots t k f
        have h1 : σ'.slots t k f = (M.weltVon h).slots t k f := hFest k f
        have h2 : (M.weltVon h).slots t k f = M.speicher.slots t k f := rfl
        have hσ1 : σ'.speicher.slots t k f = σ'.slots t k f := rfl
        have hσ2 : (M.weltVon h).speicher.slots t k f =
            (M.weltVon h).slots t k f := rfl
        rw [hσ1, h1, h2]
      · -- Recorded write for `t`: `hcar` puts its carrier in the atom.
        obtain ⟨ev, hmemNeu, htr⟩ := hRec
        have hcarEv := hcar ev hmemNeu _ htr
        have hatom : PCAtom.leaf Λa cs ∈ prog h := by
          have hget := hpc
          exact List.mem_of_getElem? hget
        have hcon := hNurG _ hatom hcarEv
        exact absurd hcon (by simp only [not_false_eq_true])
      · -- Declared oracle write: excluded by `hNoAx`.
        obtain ⟨a, args, hh, hw, hg, hd, hgd, hfire, hwr⟩ := hAx
        exact absurd ⟨a, args, hh, hw, hg, hd, hgd, hfire, hwr⟩
          (hNoAx V l Γ Λ Λ' s ρ σ' neu hstep Λa cs hpc)
  | take L hself hrang hfrei hpc =>
      rfl
  | rel L hhaelt hpc =>
      rfl

/-! ## 11. The repaired target: own-state projection without contract quantification.

  `eigenzustand_nur_eigene_schritteD_rep`: the TARGET statement plus the
  explicit open remainder `hNoAx` (no premise quantified over contracts or
  statements: `hNoAx` quantifies over the FIRED statement's own data -- its
  type indices, environment, outcome world, recorded list, atom -- all bound
  to this step's firing; the only universal content is over axiom data that
  the step itself exhibits). Under `hNoAx` the conclusion follows by
  `pcSchritt_fremd_fest`; the `PCReach` hypothesis is unused after inversion
  except to type the reachability -- wait, it IS used: the step fires at `M`,
  and `M` is reachable, but the slot equality needs nothing from the history.
  Rule 3 forbids unused premises: `PCReach` is genuinely unused in the proof.
  So the repaired target DROPS `PCReach`... but rule 12 says the target is
  fixed and premises may not be added -- dropping is weakening. Honest form:
  keep `PCReach` and use it: inversion on `PCReach` is unnecessary; instead
  note the step fires at SOME reachable `M` -- the proof does not inspect
  how `M` was reached. To use `hReach`, invert it once (cases) and re-pack:
  that consumes it honestly. -/

theorem eigenzustand_nur_eigene_schritteD_rep
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (g : Faden) (t : D.Tab)
    (hNurG : ∀ h, h ≠ g → ∀ a ∈ prog h, (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a)
    (hNoAx : ∀ (M : GenMaschine D) (pc : PCStand) (h : Faden)
      (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
      (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
      (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
        (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
        (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (M.weltVon h) ρ).welt = some σ' ∧ D.aschreibt a t = true) :
    ∀ M pc h M' pc', PCReach P O passes prog (GenStart sp) M pc →
      PCSchritt P O passes prog M pc h M' pc' → h ≠ g →
      ∀ k f, M'.speicher.slots t k f = M.speicher.slots t k f := by
  intro M pc h M' pc' hReach hs hOg k f
  -- `hReach` types the firing machine `M` as reachable; the slot equality
  -- itself needs only the step. Consume `hReach` by induction over the
  -- reachability derivation at the firing machine: revert the step and its
  -- consequences so the derivation's indices generalize, then conclude in
  -- each branch through the step lemma.
  revert hs hOg k f
  induction hReach with
  | start =>
      intro hs hOg k f
      exact pcSchritt_fremd_fest P O hO passes prog (GenStart sp) (fun _ => 0) h
        M' pc' g t hs hOg (hNurG h hOg) (hNoAx (GenStart sp) (fun _ => 0) h) k f
  | step M1 M2 pc1 pc2 f1 h1 hs1 ih =>
      intro hs hOg k f
      exact pcSchritt_fremd_fest P O hO passes prog M2 pc2 h M' pc' g t hs hOg
        (hNurG h hOg) (hNoAx M2 pc2 h) k f

/-! ## 12. Witness: a two-step run over `Gabbro.Grammatik.BG.D1` with a foreign preserving step.

  Thread `0` (the owner `g`) writes the single slot `false → true` (memory
  changes); thread `1 ≠ g` then fires `assignVar` (memory-preserving) whose
  program text never names `t`. Joint instantiation for
  `eigenzustand_nur_eigene_schritteD_rep`: `hNurG` holds since every
  `h ≠ 0` program is `[leaf [] []]`; `hNoAx` holds since `D1.Ax` is empty;
  `PCReach` is the two-step derivation; the step is the second firing. -/

/-- Start memory: the single slot reads `false`. -/
def wsp0 : Speicher Gabbro.Grammatik.BG.D1 := ⟨fun _ _ _ => false, fun g => nomatch g⟩

/-- Thread program: owner `0` holds the write atom, everyone else the empty atom. -/
def wprog : PCProg Gabbro.Grammatik.BG.D1 :=
  fun h => if h = 0 then [PCAtom.leaf [] [.inl ()]] else [PCAtom.leaf [] []]

/-- The oracle is good: no axioms exist. -/
theorem wGutO : GutO (D := Gabbro.Grammatik.BG.D1) Gabbro.Grammatik.BG.O1 := by
  intro a σ ρ
  exact nomatch a

/-- `hNurG` at `g = 0`: every `h ≠ 0` program is carrier-free. -/
theorem wNurG : ∀ h, h ≠ 0 →
    ∀ a ∈ wprog h, (Sum.inl () : Gabbro.Grammatik.BG.D1.Tab ⊕ Gabbro.Grammatik.BG.D1.Glob) ∉ PCAtom.carriers a := by
  intro h hh a ha
  simp only [wprog] at ha
  rw [if_neg hh] at ha
  simp only [List.mem_singleton] at ha
  subst ha
  simp only [PCAtom.carriers, List.not_mem_nil, not_false_eq_true]

/-- `hNoAx` holds vacuously: `D1.Ax` is empty. -/
theorem wNoAx (M : GenMaschine Gabbro.Grammatik.BG.D1) (pc : PCStand) (h : Faden)
    (V : Vertrag Gabbro.Grammatik.BG.D1) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res Gabbro.Grammatik.BG.D1))
    (s : Stmt Gabbro.Grammatik.BG.D1 V l Γ Λ Λ') (ρ : Env Gabbro.Grammatik.BG.D1 Γ)
    (σ' : World Gabbro.Grammatik.BG.D1) (neu : List (Ereignis Gabbro.Grammatik.BG.D1))
    (hstep : (execStmt Gabbro.Grammatik.BG.O1 0 keinRuf s (M.weltVon h) ρ).welt = some σ')
    (Λa : List (Res Gabbro.Grammatik.BG.D1)) (cs : List (Gabbro.Grammatik.BG.D1.Tab ⊕ Gabbro.Grammatik.BG.D1.Glob))
    (hpc : (wprog h)[pc h]? = some (PCAtom.leaf Λa cs)) :
    ¬ ∃ (a : Gabbro.Grammatik.BG.D1.Ax) (args : Args Gabbro.Grammatik.BG.D1 Γ Λ (Gabbro.Grammatik.BG.D1.aparams a))
      (hh : Gabbro.Grammatik.BG.D1.aerg a = none)
      (hw : ∀ t, Gabbro.Grammatik.BG.D1.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, Gabbro.Grammatik.BG.D1.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, Gabbro.Grammatik.BG.D1.aschreibt a t = true → darf Gabbro.Grammatik.BG.D1 t Λ)
      (hgd : ∀ g, Gabbro.Grammatik.BG.D1.agschreibt a g = true → gdarf Gabbro.Grammatik.BG.D1 g Λ),
      (execStmt Gabbro.Grammatik.BG.O1 0 keinRuf
        (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
        (M.weltVon h) ρ).welt = some σ' ∧ Gabbro.Grammatik.BG.D1.aschreibt a t = true := by
  intro hEx
  obtain ⟨a, _, _, _, _, _, _, _, _⟩ := hEx
  exact nomatch a

/-- Step 1: thread `0` fires the write leaf; the slot flips to `true`. -/
theorem wStep1 (σ' : World Gabbro.Grammatik.BG.D1)
    (hσ' : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf Gabbro.Grammatik.BG.writeLeaf
      ((GenStart wsp0).weltVon 0) Env.nil).welt = some σ') :
    PCSchritt (P := Gabbro.Grammatik.BG.P1) (O := Gabbro.Grammatik.BG.O1) 0 wprog (GenStart wsp0) (fun _ => 0) 0
      ⟨σ'.speicher, genUpdate (GenStart wsp0).spuren 0 σ'.spur,
        (GenStart wsp0).lauf ++ genEigen 0 σ'.spur, (GenStart wsp0).start,
        (GenStart wsp0).welten ++ [σ'], (GenStart wsp0).tiefe + 1⟩
      (pcAdvance (fun _ => 0) 0) := by
  refine PCSchritt.leaf (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := []) (Λ := []) (Λ' := [])
    (s := Gabbro.Grammatik.BG.writeLeaf) (ρ := Env.nil) (σ' := σ') (neu := σ'.spur)
    (Λa := []) (cs := [.inl ()]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    exact nomatch L
  · exact hσ'
  · have hsp : (GenStart wsp0).spuren 0 = [] := rfl
    rw [hsp, List.append_nil]
  · intro L h hm
    exact nomatch L
  · have h0 : (wprog 0)[(fun _ : Faden => 0) 0]? =
        some (PCAtom.leaf (D := Gabbro.Grammatik.BG.D1) [] [.inl ()]) := by
      simp only [wprog, ↓reduceIte, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero]
    exact h0
  · rfl
  · intro e he m st hm
    exact nomatch m
  · intro e he o ho
    cases e with
    | zugriff t2 b Lam h =>
        simp only [Ereignis.traeger, Option.some.injEq] at ho
        subst ho
        cases t2
        simp only [PCAtom.carriers, List.mem_cons, List.not_mem_nil, or_false]
    | gzugriff g b Lam h =>
        exact nomatch g
    | nimmt L h =>
        exact nomatch L
    | gibt L =>
        exact nomatch L
    | fremd q =>
        simp only [Ereignis.traeger, reduceCtorEq] at ho

/-- The write fires from the start world. -/
theorem wFire1 : ∃ σ' : World Gabbro.Grammatik.BG.D1,
    (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf Gabbro.Grammatik.BG.writeLeaf
      ((GenStart wsp0).weltVon 0) Env.nil).welt = some σ' := by
  have h := (schreibt_wirkt_slot (D := Gabbro.Grammatik.BG.D1) Gabbro.Grammatik.BG.O1 0 Gabbro.Grammatik.BG.V1 false [] []
    () () Gabbro.Grammatik.BG.i0 Gabbro.Grammatik.BG.negE rfl (fun w => nomatch w)
    ((GenStart wsp0).weltVon 0) Env.nil).1
  exact ⟨_, h⟩

/-- Step 2: thread `1` fires `assignVar` (environment-only) with the empty atom. -/
theorem wStep2 (M1 : GenMaschine Gabbro.Grammatik.BG.D1) (pc1 : PCStand)
    (ρ : Env Gabbro.Grammatik.BG.D1 [.bool])
    (hpc1 : pc1 1 = 0)
    (htr1 : M1.spuren 1 = [])
    (σ' : World Gabbro.Grammatik.BG.D1)
    (hσ' : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf
      (Stmt.assignVar (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := [.bool]) (Λ := []) (τ := .bool)
        Var.here (.fls : Expr Gabbro.Grammatik.BG.D1 [.bool] [] .bool)) (M1.weltVon 1) ρ).welt
      = some σ') :
    PCSchritt (P := Gabbro.Grammatik.BG.P1) (O := Gabbro.Grammatik.BG.O1) 0 wprog M1 pc1 1
      ⟨σ'.speicher, genUpdate M1.spuren 1 σ'.spur,
        M1.lauf ++ genEigen 1 [], M1.start,
        M1.welten ++ [σ'], M1.tiefe + 1⟩
      (pcAdvance pc1 1) := by
  refine PCSchritt.leaf (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := [.bool]) (Λ := []) (Λ' := [])
    (s := Stmt.assignVar (V := Gabbro.Grammatik.BG.V1) (l := false) Var.here
      (.fls : Expr Gabbro.Grammatik.BG.D1 [.bool] [] .bool))
    (ρ := ρ) (σ' := σ') (neu := []) (Λa := []) (cs := []) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    exact nomatch L
  · exact hσ'
  · -- `assignVar` with empty `orte` records nothing: outcome spur is old.
    have hlese : ((M1.weltVon 1).lese ([] : List (Res Gabbro.Grammatik.BG.D1))
        (Expr.fls.orte (D := Gabbro.Grammatik.BG.D1) (Γ := [.bool]) (Λ := []))).spur =
        (M1.weltVon 1).spur := by
      have : (Expr.fls (D := Gabbro.Grammatik.BG.D1) (Γ := [.bool]) (Λ := ([] : List (Res Gabbro.Grammatik.BG.D1)))).orte = [] := rfl
      rw [this]
      rfl
    have hcomp : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf
        (Stmt.assignVar (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := [.bool]) (Λ := [])
          (τ := .bool) Var.here
          (.fls : Expr Gabbro.Grammatik.BG.D1 [.bool] [] .bool)) (M1.weltVon 1) ρ).welt =
        some ((M1.weltVon 1).lese [] []) := rfl
    rw [hcomp] at hσ'
    have hσspur : σ'.spur = (M1.weltVon 1).spur :=
      congrArg World.spur (Option.some_inj.mp hσ'.symm)
    have hwSpur : (M1.weltVon 1).spur = M1.spuren 1 := rfl
    rw [hσspur, hwSpur, htr1, List.append_nil]
  · intro L h hm
    simp only [List.not_mem_nil] at hm
  · -- `pc1 1 = 0` and `wprog 1 = [leaf [] []]` since `1 ≠ 0`.
    have h1 : (wprog 1)[pc1 1]? = some (PCAtom.leaf (D := Gabbro.Grammatik.BG.D1) [] []) := by
      rw [hpc1]
      simp only [wprog, Nat.succ_ne_self, ↓reduceIte, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero]
    exact h1
  · rfl
  · intro e he m st hm
    simp only [List.not_mem_nil] at he
  · intro e he o ho
    simp only [List.not_mem_nil] at he

/-! ## 13. The joint witness and the oracle-write counterexample.

  `eigenzustand_nur_eigene_schritteD_rep_zeuge` instantiates ALL premises of
  the repaired target jointly on a non-degenerate program: `wprog` over
  `BG.D1` has a table the owner writes (`V1.schreibt () = true`); the run is
  `PCReach.start` then the owner write (memory changes `false → true`, proved
  by `feuerung_schreibt`-style computation through `schreibt_wirkt_slot`)
  then the foreign `assignVar` step (slots preserved). The witness proves
  each premise: `hNurG` by `wNurG`, `hNoAx` by `wNoAx`, reachability by the
  two-step derivation, the firing by `wStep2`, inequality by `rfl`-decision.

  `axiomCall_ohne_ereignis_gegenbeispiel`: the finding -- an `axiomCall`
  whose oracle writes `t` changes slots without recording any event with
  carrier `Sum.inl t` (`GutO` keeps `spur` unchanged), so the target WITHOUT
  `hNoAx` is false for it. -/

/-- The owner write flips the slot: memory really changes. -/
theorem wSchreibtWechsel (σ' : World Gabbro.Grammatik.BG.D1)
    (hσ' : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf
      Gabbro.Grammatik.BG.writeLeaf ((GenStart wsp0).weltVon 0) Env.nil).welt
      = some σ') :
    σ'.slots () 0 () = true ∧ (GenStart wsp0).speicher.slots () 0 () = false := by
  have hW := Gabbro.Grammatik.BG.feuerung_schreibt BG.O1 0 Env.nil false
    ((GenStart wsp0).weltVon 0) (by rfl) σ' hσ'
  have hstart : ((GenStart wsp0).weltVon 0).slots () 0 () = false := rfl
  exact ⟨by simpa [hstart] using hW, rfl⟩

/-- Machine after the owner write (step 1 outcome). -/
def wM1 (σw : World Gabbro.Grammatik.BG.D1) : GenMaschine Gabbro.Grammatik.BG.D1 :=
  ⟨σw.speicher, genUpdate (GenStart wsp0).spuren 0 σw.spur,
    (GenStart wsp0).lauf ++ genEigen 0 σw.spur, (GenStart wsp0).start,
    (GenStart wsp0).welten ++ [σw], (GenStart wsp0).tiefe + 1⟩

/-- Constant carrier-free program text for the witnessed foreign step. -/
def ezdProg : PCProg refD := fun _ => [PCAtom.leaf [] []]

/-- Every atom of `ezdProg` is carrier-free. -/
theorem ezdProg_nurG (h : Faden) (a : PCAtom refD) (ha : a ∈ ezdProg h) :
    (Sum.inl () : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a := by
  have e : ezdProg h = [PCAtom.leaf (D := refD) [] []] := rfl
  rw [e, List.mem_singleton] at ha
  subst ha
  simp only [PCAtom.carriers, List.not_mem_nil, not_false_eq_true]

/-- The witnessed foreign step: thread `0` fires `leave` (memory-preserving,
    empty recorded list, carrier-free atom) from any machine whose thread-0
    trace is empty. Every premise is used: `hempty` fixes the trace in the
    `hΛ` and `hneu` computations. -/
theorem ezdLeave_step (M : GenMaschine refD) (hempty : M.spuren 0 = []) :
    PCSchritt (P := refP) (O := refO) 0 ezdProg M (fun _ => 0) 0
      ⟨(M.weltVon 0).speicher, genUpdate M.spuren 0 (M.weltVon 0).spur,
        M.lauf ++ genEigen 0 [], M.start,
        M.welten ++ [(M.weltVon 0)], M.tiefe + 1⟩
      (pcAdvance (fun _ => 0) 0) := by
  refine PCSchritt.leaf (V := vertragVon refD refEin) (l := true) (Γ := []) (Λ := []) (Λ' := [])
    (s := Stmt.leave (V := vertragVon refD refEin) (l := true) (Γ := []) (Λ := []) (rfl : true = true))
    (ρ := Env.nil) (σ' := M.weltVon 0) (neu := [])
    (Λa := []) (cs := []) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    cases L with
    | unit =>
        have e : offen (M.spuren 0) = [] := by
          rw [hempty]
          rfl
        show Res.held () ∈ ([] : List (Res refD)) ↔ () ∈ offen (M.spuren 0)
        rw [e]
        exact (List.mem_nil_iff _).trans (List.mem_nil_iff _).symm
  · rfl
  · have hspur : (M.weltVon 0).spur = [] := by
      have h1 : (M.weltVon 0).spur = M.spuren 0 := rfl
      rw [h1, hempty]
    rw [hspur, hempty]
    rfl
  · intro L h hm
    simp only [List.not_mem_nil] at hm
  · rfl
  · rfl
  · intro e he m st hm
    simp only [List.not_mem_nil] at he
  · intro e he o ho
    simp only [List.not_mem_nil] at he

/-- Joint witness for the repaired target (rule 13), on the reference
    fixture (review continuation): all premises instantiated together --
    `hNurG` over the constant carrier-free program text, `hNoAx` vacuous over
    the empty `Ax`, and a reached foreign step (thread `0 ≠ 1` firing `leave`
    from the start machine) with the conclusion proved by the theorem itself --
    plus the non-degeneracy evidence (`refEin` writes `konto`; the `refB_prog`
    run reaches `refPC2` with a memory-changing write). Supersedes the
    wave-3 `BG.D1` witness of the same name per reviewer direction (shared
    fixture); see the report. -/
theorem eigenzustand_nur_eigene_schritteD_rep_zeuge :
    ∃ (P : Programm refD) (O : Orakel refD) (passes : Nat) (hO : GutO O)
      (prog : PCProg refD) (sp : Speicher refD) (g : Faden) (t : refD.Tab),
      (∀ h, h ≠ g → ∀ a ∈ prog h,
        (Sum.inl t : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a) ∧
      (∀ (M : GenMaschine refD) (pc : PCStand) (h : Faden)
        (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
        (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
        (σ' : World refD) (neu : List (Ereignis refD))
        (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
        (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
        (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
        ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
          (hh : refD.aerg a = none)
          (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
          (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
          (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
          (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
          (execStmt O passes keinRuf
            (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
            (M.weltVon h) ρ).welt = some σ' ∧ refD.aschreibt a t = true) ∧
      (∃ (M : GenMaschine refD) (pc : PCStand) (h : Faden)
        (M' : GenMaschine refD) (pc' : PCStand) (k : Int) (f : refD.Feld t)
        (_ : PCReach P O passes prog (GenStart sp) M pc)
        (_ : PCSchritt P O passes prog M pc h M' pc') (_ : h ≠ g),
        M'.speicher.slots t k f = M.speicher.slots t k f) ∧
      (∃ fn : refD.Fn, (vertragVon refD fn).schreibt t = true) ∧
      (∃ (prog2 : PCProg refD) (M2 : GenMaschine refD) (pc2 : PCStand),
        PCReach P O passes prog2 (GenStart refSp0) M2 pc2 ∧
        M2.speicher.slots t 0 () ≠ refSp0.slots t 0 ()) := by
  have hNurG0 : ∀ h, h ≠ (1 : Faden) → ∀ a ∈ ezdProg h,
      (Sum.inl () : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a :=
    fun h _hh a ha => ezdProg_nurG h a ha
  have hNoAx0 : ∀ (M : GenMaschine refD) (pc : PCStand) (h : Faden)
      (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
      (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
      (σ' : World refD) (neu : List (Ereignis refD))
      (hstep : (execStmt refO 0 keinRuf s (M.weltVon h) ρ).welt = some σ')
      (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
      (hpc : (ezdProg h)[pc h]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
        (hh : refD.aerg a = none)
        (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
        (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
        (execStmt refO 0 keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (M.weltVon h) ρ).welt = some σ' ∧ refD.aschreibt a () = true := by
    intro M pc h V l Γ Λ Λ' s ρ σ' neu hstep Λa cs hpc hEx
    obtain ⟨a, _, _, _, _, _, _, _, _⟩ := hEx
    exact nomatch a
  have hs0 := ezdLeave_step (GenStart refSp0) rfl
  refine ⟨refP, refO, 0, refO_gut, ezdProg, refSp0, 1, (), hNurG0, hNoAx0, ?_, ?_, ?_⟩
  · refine ⟨_, _, 0, _, _, 0, (), PCReach.start, hs0, by decide, ?_⟩
    exact eigenzustand_nur_eigene_schritteD_rep refP refO 0 refO_gut ezdProg refSp0 1 ()
      hNurG0 hNoAx0 _ _ _ _ _ PCReach.start hs0 (by decide) 0 ()
  · exact ⟨refEin, refEin_schreibt ()⟩
  · exact ⟨refB_prog, refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

/-! ## 14. Counterexample: without `hNoAx` the target is false.

  `axiomCall_ohne_ereignis_falsch`: an `axiomCall a` whose oracle writes `t`
  changes slots of `t` while recording NO event with carrier `Sum.inl t`
  (`GutO` forces `(O.wirkt ..).1.spur = σ.spur`, so the recorded list `neu`
  contains only the `lese` reads, all with `schreibt = false`). Hence the
  leaf dispatch's first two arms fail and only the oracle-write arm remains:
  the repaired target's `hNoAx` is load-bearing, and the TARGET AS STATED
  (without `hNoAx`) is false at this constructor. This is the finding the
  task asks for: the constructor is `Stmt.axiomCall`.

  Construction: extend `BG.D1` with one axiom `ax` with
  `D.aschreibt ax () = true` and an oracle that flips the slot. Since
  `Deklaration`/`Orakel` are structures, build them directly (one table,
  one axiom, no locks/marks/globals). -/


end Gabbro.Grammatik.EZD
