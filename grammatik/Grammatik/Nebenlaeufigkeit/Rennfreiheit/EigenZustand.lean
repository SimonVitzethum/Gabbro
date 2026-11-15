/-
  File:      Grammatik/EigenZustand.lean
  Subject:   OWN-STATE PROJECTION WITHOUT REMAINDER (lane 80).

  Under the recording oracle bound (`GutO`, `Satz.lean`), an `axiomCall`
  whose axiom declares a write to `t` records a write event with carrier
  `Sum.inl t` (`axiomCallRecordsWrite`). The lane-56 leaf dispatch
  (`EZD.blattSlots_dispatch`, reused) then leaves no remainder: a recorded
  write contradicts `hNurG` via `hcar`, and the oracle-write arm does so
  through the recorded event. The target `eigenzustand_nur_eigene_schritte`
  is the original statement, with witnesses on the reference fixture
  (`refD`, no axioms) and on the one-axiom unguarded declaration (`AxGegen`).
-/
module
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD
public import Grammatik.Korpus.Referenz.ReferenzB
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


namespace Gabbro.Grammatik

open Gabbro.Grammatik.EZD

variable {D : Deklaration}

/-- An oracle write to `t` is recorded: a fired `axiomCall` whose axiom
    declares the write leaves a write event with carrier `Sum.inl t` in the
    recorded list. The `GutO` trace clause is conditional on the guards being
    held; the fired statement discharges it from its guard premises `hd`/`hgd`
    plus `HeldGenau` at the entry world (reads preserve `haelt`). From the
    `GutO` witness domains (complete over the
    declared writes) the event is the `axiomSpur` table write; the `lese`
    reads sit underneath. A failed `einpassen` yields no world. -/
theorem axiomCallRecordsWrite (O : Orakel D) (hO : GutO O) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {h : D.aerg a = none}
    {hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ}
    {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    {σ : World D} {ρ : Env D Γ} {σ' : World D} {neu : List (Ereignis D)}
    (hh : HeldGenau Λ σ.haelt)
    (hstep : (execStmt O passes keinRuf
      (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur)
    {t : D.Tab} (hwr : D.aschreibt a t = true) :
    ∃ ev ∈ neu, ev.traeger = some (Sum.inl t) := by
  have hhaelt : (σ.lese Λ args.orte).haelt = σ.haelt := lese_haelt _ _ _
  have hhL : HeldGenau Λ (σ.lese Λ args.orte).haelt := by
    rw [hhaelt]
    exact hh
  have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t →
      L ∈ (σ.lese Λ args.orte).haelt :=
    fun t hwr L hL => (hhL L).mp (hd t hwr _ hL)
  have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
      L ∈ (σ.lese Λ args.orte).haelt :=
    fun g hwr L hL => (hhL L).mp (hgd g hwr _ hL)
  obtain ⟨_, _, hcond⟩ := hO a ((σ.lese Λ args.orte).fragt (.inl a))
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
  obtain ⟨tabs₀, globs₀, Λe, hct₀, _, _, _, _, _, hspurO⟩ := hcond hgt hgg
  have hlese : (σ.lese Λ args.orte).spur =
      (args.orte.map fun o => match o with
        | .inl t => Ereignis.zugriff t false Λ σ.haelt
        | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur := rfl
  have hfire : (execStmt O passes keinRuf
      (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
      (match axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | (sg₂, Option.some _) => (Ausgang.ok sg₂ ρ : Ausgang V l Γ)
      | (_, Option.none) =>
        (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ)).welt := rfl
  cases hAns : axiomAntwort O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk fst snd =>
      cases snd with
      | some v =>
          have hcomp : (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
              some fst := by
            rw [hfire, hAns, Ausgang.welt]
          rw [hcomp] at hstep
          have hsg' : σ' = fst := Option.some_inj.mp hstep.symm
          have hfst : fst = (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
              (evalArgs (σ.lese Λ args.orte) args
                (σ.lese Λ args.orte) ρ)).1 := by
            have hA := hAns
            simp only [axiomAntwort] at hA
            have hF := congrArg Prod.fst hA
            simp only at hF
            exact hF.symm
          have hsp : σ'.spur =
              axiomSpur tabs₀ globs₀ a Λe (σ.lese Λ args.orte).haelt ++
              (Ereignis.fremd (.inl a) :: (σ.lese Λ args.orte).spur) := by
            rw [hsg', hfst]
            exact hspurO
          rw [hsp, hlese, ← List.cons_append, ← List.append_assoc] at hneu
          have hneueq : axiomSpur tabs₀ globs₀ a Λe (σ.lese Λ args.orte).haelt ++
              (Ereignis.fremd (.inl a) :: args.orte.map fun o => match o with
                | .inl t => Ereignis.zugriff t false Λ σ.haelt
                | .inr g => Ereignis.gzugriff g false Λ σ.haelt) = neu :=
            List.append_cancel_right hneu
          have hmem := axiomSpur_write_tab tabs₀ globs₀ a Λe
            (σ.lese Λ args.orte).haelt t (hct₀ t hwr) hwr
          have hmem2 : Ereignis.zugriff t true Λe (σ.lese Λ args.orte).haelt ∈
              axiomSpur tabs₀ globs₀ a Λe (σ.lese Λ args.orte).haelt ++
              (Ereignis.fremd (.inl a) :: args.orte.map fun o => match o with
                | .inl t => Ereignis.zugriff t false Λ σ.haelt
                | .inr g => Ereignis.gzugriff g false Λ σ.haelt) :=
            List.mem_append.mpr (Or.inl hmem)
          rw [hneueq] at hmem2
          exact ⟨_, hmem2, rfl⟩
      | none =>
          rw [hfire, hAns, Ausgang.welt] at hstep
          simp only [reduceCtorEq] at hstep

/-- A foreign step keeps the slots of `t`: invert the `PCSchritt`.
    Take/release keep `M.speicher` by construction. For a leaf, run the
    lane-56 dispatch (reused): a recorded write for `t` contradicts `hNurG`
    via `hcar`; slots kept is the goal; a declared oracle write to `t` is
    recorded (`axiomCallRecordsWrite`) and contradicts `hNurG` the same way.
    No remainder premise: the oracle arm is discharged by the recording
    `GutO`. -/
theorem foreignStepKeepsSlots (P : Programm D) (O : Orakel D) (hO : GutO O)
    (passes : Nat)
    (prog : PCProg D) (M pc h M' pc') (t : D.Tab)
    (hs : PCSchritt P O passes prog M pc h M' pc')
    (hNurG : ∀ a ∈ prog h,
      (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a)
    (k : Int) (f : D.Feld t) :
    M'.speicher.slots t k f = M.speicher.slots t k f := by
  cases hs with
  | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar =>
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
        have hdisp := EZD.blattSlots_dispatch O hO passes s ρ hleaf
          (M.weltVon h) σ' neu hstep hneu t
        rcases hdisp with hRec | hFest | hAx
        · exact Or.inr (Or.inl hRec)
        · exact Or.inl hFest
        · exact Or.inr (Or.inr hAx)
      rcases hmem with hFest | hRec | hAx
      · show σ'.speicher.slots t k f = M.speicher.slots t k f
        have h1 : σ'.slots t k f = (M.weltVon h).slots t k f := hFest k f
        have h2 : (M.weltVon h).slots t k f = M.speicher.slots t k f := rfl
        have hσ1 : σ'.speicher.slots t k f = σ'.slots t k f := rfl
        rw [hσ1, h1, h2]
      · obtain ⟨ev, hmemNeu, htr⟩ := hRec
        have hcarEv := hcar ev hmemNeu _ htr
        have hatom : PCAtom.leaf Λa cs ∈ prog h :=
          List.mem_of_getElem? hpc
        exact absurd hcarEv (hNurG _ hatom)
      · obtain ⟨a, args, hh, hw, hg, hd, hgd, hfire, hwr⟩ := hAx
        obtain ⟨ev, hmemNeu, htr⟩ :=
          axiomCallRecordsWrite O hO passes hΛ hfire hneu hwr
        have hcarEv := hcar ev hmemNeu _ htr
        have hatom : PCAtom.leaf Λa cs ∈ prog h :=
          List.mem_of_getElem? hpc
        exact absurd hcarEv (hNurG _ hatom)
  | take L hself hrang hfrei hpc =>
      rfl
  | rel L hhaelt hpc =>
      rfl

/-- Own-state projection, no remainder: a step fired by a thread `h`
    whose program text never names table `t` leaves every slot of `t`
    unchanged. The reachability derivation is consumed by induction (each
    branch concludes through the step lemma); the oracle arm is discharged
    by the recording `GutO`. -/
theorem eigenzustand_nur_eigene_schritte
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (g : Faden) (t : D.Tab)
    (hNurG : ∀ h, h ≠ g → ∀ a ∈ prog h, (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a) :
    ∀ M pc h M' pc', PCReach P O passes prog (GenStart sp) M pc →
      PCSchritt P O passes prog M pc h M' pc' → h ≠ g →
      ∀ k f, M'.speicher.slots t k f = M.speicher.slots t k f := by
  intro M pc h M' pc' hReach hs hOg k f
  revert hs hOg k f
  induction hReach with
  | start =>
      intro hs hOg k f
      exact foreignStepKeepsSlots P O hO passes prog (GenStart sp) (fun _ => 0) h
        M' pc' t hs (hNurG h hOg) k f
  | step M1 M2 pc1 pc2 f1 h1 hs1 ih =>
      intro hs hOg k f
      exact foreignStepKeepsSlots P O hO passes prog M2 pc2 h M' pc' t hs
        (hNurG h hOg) k f

/- REMOVED (reviewer revision): `oracleWriteHoldsGuard` (an oracle write
    holds the guard from the bound alone) is unprovable under the
    CONDITIONAL `GutO` -- its only link to the goal needs the full
    guard-held antecedent, and with guard premises added it would be
    trivial without `GutO`. Guarded-table writers exist (`FremdSperre.hOF`):
    the guard flows from the constructor's `hd`/`hgd` plus `HeldGenau`,
    which is exactly how `axiomAntwort_gut`, `axiomCallRecordsWrite`, and
    the `Extraktion` characterization discharge the antecedent. -/

/-- Joint witness for the target (rule 13) on the reference fixture: all
    premises instantiated together -- `hNurG` over the constant carrier-free
    program text, a reached foreign step (thread `0 ≠ 1` firing `leave` from
    the start machine) with the conclusion proved by the theorem itself --
    plus the non-degeneracy evidence (`refEin` writes `konto`; the
    `refB_prog` run reaches `refPC2` with a memory-changing write).
    `refD` declares no axiom, so no oracle step can occur. -/
theorem eigenzustand_nur_eigene_schritte_zeuge :
    ∃ (P : Programm refD) (O : Orakel refD) (passes : Nat) (hO : GutO O)
      (prog : PCProg refD) (sp : Speicher refD) (g : Faden) (t : refD.Tab),
      (∀ h, h ≠ g → ∀ a ∈ prog h,
        (Sum.inl t : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a) ∧
      (∃ (M : GenMaschine refD) (pc : PCStand) (h : Faden)
        (M' : GenMaschine refD) (pc' : PCStand) (k : Int) (f : refD.Feld t),
        PCReach P O passes prog (GenStart sp) M pc ∧
        PCSchritt P O passes prog M pc h M' pc' ∧ h ≠ g ∧
        M'.speicher.slots t k f = M.speicher.slots t k f) ∧
      (∃ fn : refD.Fn, (vertragVon refD fn).schreibt t = true) ∧
      (∃ (prog2 : PCProg refD) (M2 : GenMaschine refD) (pc2 : PCStand),
        PCReach P O passes prog2 (GenStart refSp0) M2 pc2 ∧
        M2.speicher.slots t 0 () ≠ refSp0.slots t 0 ()) := by
  have hNurG0 : ∀ h, h ≠ (1 : Faden) → ∀ a ∈ EZD.ezdProg h,
      (Sum.inl () : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a :=
    fun h _ a ha => EZD.ezdProg_nurG h a ha
  have hs0 := EZD.ezdLeave_step (GenStart refSp0) rfl
  refine ⟨refP, refO, 0, refO_gut, EZD.ezdProg, refSp0, 1, (), hNurG0, ?_, ?_, ?_⟩
  · refine ⟨_, _, 0, _, _, 0, (), PCReach.start, hs0, by decide, ?_⟩
    exact eigenzustand_nur_eigene_schritte refP refO 0 refO_gut EZD.ezdProg refSp0 1 ()
      hNurG0 _ _ _ _ _ PCReach.start hs0 (by decide) 0 ()
  · exact ⟨refEin, refEin_schreibt ()⟩
  · exact ⟨refB_prog, refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

end Gabbro.Grammatik
