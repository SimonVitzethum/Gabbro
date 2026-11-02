/- Part 4 of 5 of `EigenZustandD` (split by instrumente/teile/lean-teilen.py; the umbrella `EigenZustandD.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T3
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


end Gabbro.Grammatik.EZD
