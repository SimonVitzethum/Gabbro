module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T4a
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
