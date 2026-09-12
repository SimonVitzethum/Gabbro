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
import Grammatik.Maschine
import Grammatik.Satz
import Grammatik.EigenZustandD
import Grammatik.ReferenzB

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
  obtain ⟨_, _, hcond⟩ := hO a (σ.lese Λ args.orte)
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
          have hfst : fst = (O.wirkt a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args
                (σ.lese Λ args.orte) ρ)).1 := by
            have hA := hAns
            simp only [axiomAntwort] at hA
            have hF := congrArg Prod.fst hA
            simp only at hF
            exact hF.symm
          have hsp : σ'.spur =
              axiomSpur tabs₀ globs₀ a Λe (σ.lese Λ args.orte).haelt ++
              (σ.lese Λ args.orte).spur := by
            rw [hsg', hfst]
            exact hspurO
          rw [hsp, hlese, ← List.append_assoc] at hneu
          have hneueq : axiomSpur tabs₀ globs₀ a Λe (σ.lese Λ args.orte).haelt ++
              (args.orte.map fun o => match o with
                | .inl t => Ereignis.zugriff t false Λ σ.haelt
                | .inr g => Ereignis.gzugriff g false Λ σ.haelt) = neu :=
            List.append_cancel_right hneu
          have hmem := axiomSpur_write_tab tabs₀ globs₀ a Λe
            (σ.lese Λ args.orte).haelt t (hct₀ t hwr) hwr
          have hmem2 : Ereignis.zugriff t true Λe (σ.lese Λ args.orte).haelt ∈
              axiomSpur tabs₀ globs₀ a Λe (σ.lese Λ args.orte).haelt ++
              (args.orte.map fun o => match o with
                | .inl t => Ereignis.zugriff t false Λ σ.haelt
                | .inr g => Ereignis.gzugriff g false Λ σ.haelt) :=
            List.mem_append.mpr (Or.inl hmem)
          rw [hneueq] at hmem2
          exact ⟨_, hmem2, rfl⟩
      | none =>
          rw [hfire, hAns, Ausgang.welt] at hstep
          simp at hstep

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

/-- Thread program for the one-axiom memory run: every thread holds the
    atom carrying the axiom's written table. -/
def axiomProg : PCProg EZD.AxGegen.D2 :=
  fun _ => [PCAtom.leaf [] [Sum.inl ()]]

/-- The axiom call fires from the start world (the oracle answers `some`). -/
theorem axFireExists : ∃ σ' : World EZD.AxGegen.D2,
    (execStmt (O := EZD.AxGegen.O2) 0 keinRuf EZD.AxGegen.axCall
      ((GenStart EZD.AxGegen.wspF).weltVon 1) Env.nil).welt = some σ' := by
  have hAns : axiomAntwort (O := EZD.AxGegen.O2) ()
      (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
      (evalArgs (Γ := []) (Λ := []) (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
        (Args.nil (D := EZD.AxGegen.D2) (Γ := []) (Λ := []))
        (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []) Env.nil) =
      (EZD.AxGegen.Wflip2 (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []),
        Option.some ()) := by
    rfl
  have hcomp : (execStmt (O := EZD.AxGegen.O2) 0 keinRuf EZD.AxGegen.axCall
      ((GenStart EZD.AxGegen.wspF).weltVon 1) Env.nil).welt =
      (match axiomAntwort (O := EZD.AxGegen.O2) ()
        (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
        (evalArgs (Γ := []) (Λ := []) (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
          (Args.nil (D := EZD.AxGegen.D2) (Γ := []) (Λ := []))
          (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []) Env.nil) with
      | (σ₂, Option.some _) => (Ausgang.ok σ₂ Env.nil : Ausgang EZD.AxGegen.V2 false []).welt
      | (_, Option.none) =>
        (Ausgang.hardware (D := EZD.AxGegen.D2) (.annahme ()) :
          Ausgang EZD.AxGegen.V2 false []).welt) := rfl
  rw [hcomp, hAns, Ausgang.welt]
  exact ⟨_, rfl⟩

/-- The memory-changing step on the one-axiom declaration: thread `1`
    fires `axCall` from the start world; the recorded list holds exactly
    the oracle's write event, covered by the carrying atom. -/
theorem axiomMemStep (σ' : World EZD.AxGegen.D2)
    (hfire' : (execStmt (O := EZD.AxGegen.O2) 0 keinRuf EZD.AxGegen.axCall
      ((GenStart EZD.AxGegen.wspF).weltVon 1) Env.nil).welt = some σ')
    (hneu' : σ'.spur =
      [Ereignis.zugriff () true []
        ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt] ++
        (GenStart EZD.AxGegen.wspF).spuren 1) :
    PCSchritt (P := EZD.AxGegen.P2w) (O := EZD.AxGegen.O2) 0 axiomProg
      (GenStart EZD.AxGegen.wspF) (fun _ => 0) 1
      ⟨σ'.speicher, genUpdate (GenStart EZD.AxGegen.wspF).spuren 1 σ'.spur,
        (GenStart EZD.AxGegen.wspF).lauf ++ genEigen 1
          [Ereignis.zugriff () true []
            ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt],
        (GenStart EZD.AxGegen.wspF).start,
        (GenStart EZD.AxGegen.wspF).welten ++ [σ'],
        (GenStart EZD.AxGegen.wspF).tiefe + 1⟩
      (pcAdvance (fun _ => 0) 1) := by
  refine PCSchritt.leaf (GenStart EZD.AxGegen.wspF) (fun _ => 0) 1
    (V := EZD.AxGegen.V2) (l := false) (Γ := []) (Λ := []) (Λ' := [])
    (s := EZD.AxGegen.axCall) (ρ := Env.nil) (σ' := σ')
    (neu := [Ereignis.zugriff () true []
      ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt])
    (Λa := []) (cs := [Sum.inl ()]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    exact nomatch L
  · exact hfire'
  · exact hneu'
  · intro L h hm
    simp at hm
  · rfl
  · rfl
  · intro e he m st hm
    simp only [List.mem_singleton] at he
    subst he
    simp [Ereignis.lambda] at hm
  · intro e he o ho
    simp only [List.mem_singleton] at he
    subst he
    have h2 : (Ereignis.zugriff () true []
        ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt).traeger =
        some (Sum.inl ()) := rfl
    rw [h2] at ho
    have ho' : o = Sum.inl () := (Option.some_inj.mp ho).symm
    rw [ho']
    simp only [PCAtom.carriers]
    exact List.mem_singleton.mpr rfl

/-- The witnessed foreign step on the one-axiom declaration: thread `1`
    fires `leave` (memory-preserving, empty recorded list, carrier-free
    atom) from any machine whose thread-1 trace is empty. The axiom's own
    step is excluded by `hNurG`: its recorded write would need a carrying
    atom. -/
theorem axiomLeaveStep (M : GenMaschine EZD.AxGegen.D2)
    (hempty : M.spuren 1 = []) :
    PCSchritt (P := EZD.AxGegen.P2w) (O := EZD.AxGegen.O2) 0 EZD.AxGegen.progF
      M (fun _ => 0) 1
      ⟨(M.weltVon 1).speicher, genUpdate M.spuren 1 (M.weltVon 1).spur,
        M.lauf ++ genEigen 1 [], M.start,
        M.welten ++ [(M.weltVon 1)], M.tiefe + 1⟩
      (pcAdvance (fun _ => 0) 1) := by
  refine PCSchritt.leaf M (fun _ => 0) 1
    (V := EZD.AxGegen.V2) (l := true) (Γ := []) (Λ := []) (Λ' := [])
    (s := Stmt.leave (V := EZD.AxGegen.V2) (l := true) (Γ := []) (Λ := [])
      (rfl : true = true))
    (ρ := Env.nil) (σ' := M.weltVon 1) (neu := [])
    (Λa := []) (cs := []) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    exact nomatch L
  · rfl
  · have hspur : (M.weltVon 1).spur = [] := by
      have h1 : (M.weltVon 1).spur = M.spuren 1 := rfl
      rw [h1, hempty]
    rw [hspur, hempty]
    rfl
  · intro L h hm
    simp at hm
  · rfl
  · rfl
  · intro e he m st hm
    simp at he
  · intro e he o ho
    simp at he

/-- Second witness (rule 13) on the one-axiom unguarded declaration
    (`AxGegen`): the target's premises hold here too -- `hNurG` over the
    constant carrier-free program text (the foreign thread's axiom step is
    excluded by it: firing `axCall` would record the write event, and `hcar`
    would demand its carrier in the atom), the reached foreign step is
    thread `1 ≠ 0` firing `leave` -- and the declaration is non-degenerate:
    the axiom's function writes the table and the axiom step itself, fired
    under a carrying atom, reaches a memory-changing run. -/
theorem eigenzustand_axiom_zeuge :
    ∃ (P : Programm EZD.AxGegen.D2) (O : Orakel EZD.AxGegen.D2) (passes : Nat)
      (hO : GutO O)
      (prog : PCProg EZD.AxGegen.D2) (sp : Speicher EZD.AxGegen.D2) (g : Faden)
      (t : EZD.AxGegen.D2.Tab),
      (∀ h, h ≠ g → ∀ a ∈ prog h,
        (Sum.inl t : EZD.AxGegen.D2.Tab ⊕ EZD.AxGegen.D2.Glob) ∉ PCAtom.carriers a) ∧
      (∃ (M : GenMaschine EZD.AxGegen.D2) (pc : PCStand) (h : Faden)
        (M' : GenMaschine EZD.AxGegen.D2) (pc' : PCStand) (k : Int)
        (f : EZD.AxGegen.D2.Feld t),
        PCReach P O passes prog (GenStart sp) M pc ∧
        PCSchritt P O passes prog M pc h M' pc' ∧ h ≠ g ∧
        M'.speicher.slots t k f = M.speicher.slots t k f) ∧
      (∃ fn : EZD.AxGegen.D2.Fn, (vertragVon EZD.AxGegen.D2 fn).schreibt t = true) ∧
      (∃ (M2 : GenMaschine EZD.AxGegen.D2) (pc2 : PCStand),
        PCReach P O passes axiomProg (GenStart EZD.AxGegen.wspF) M2 pc2 ∧
        M2.speicher.slots t 0 () ≠ EZD.AxGegen.wspF.slots t 0 ()) := by
  obtain ⟨σ', hfire'⟩ := axFireExists
  have hs0 := axiomLeaveStep (GenStart EZD.AxGegen.wspF) rfl
  have hσ' : σ' = EZD.AxGegen.Wflip2
      (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []) := by
    have hAns2 : axiomAntwort (O := EZD.AxGegen.O2) ()
        (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
        (evalArgs (Γ := []) (Λ := []) (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
          (Args.nil (D := EZD.AxGegen.D2) (Γ := []) (Λ := []))
          (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []) Env.nil) =
        (EZD.AxGegen.Wflip2 (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []),
          Option.some ()) := rfl
    have hrfl2 : (execStmt (O := EZD.AxGegen.O2) 0 keinRuf EZD.AxGegen.axCall
        ((GenStart EZD.AxGegen.wspF).weltVon 1) Env.nil).welt =
        (match axiomAntwort (O := EZD.AxGegen.O2) ()
          (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
          (evalArgs (Γ := []) (Λ := []) (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
            (Args.nil (D := EZD.AxGegen.D2) (Γ := []) (Λ := []))
            (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []) Env.nil) with
        | (σ₂, Option.some _) =>
          (Ausgang.ok σ₂ Env.nil : Ausgang EZD.AxGegen.V2 false []).welt
        | (_, Option.none) =>
          (Ausgang.hardware (D := EZD.AxGegen.D2) (.annahme ()) :
            Ausgang EZD.AxGegen.V2 false []).welt) := rfl
    rw [hrfl2, hAns2, Ausgang.welt] at hfire'
    exact Option.some_inj.mp hfire'.symm
  have hneu' : σ'.spur =
      [Ereignis.zugriff () true []
        ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt] ++
        (GenStart EZD.AxGegen.wspF).spuren 1 := by
    rw [hσ']
    rfl
  have hstep2 := axiomMemStep σ' hfire' hneu'
  have hreach2 : PCReach EZD.AxGegen.P2w EZD.AxGegen.O2 0 axiomProg
      (GenStart EZD.AxGegen.wspF) _ _ :=
    PCReach.step _ _ _ _ 1 PCReach.start hstep2
  have hne : σ'.speicher.slots () 0 () ≠ EZD.AxGegen.wspF.slots () 0 () := by
    have hflip := EZD.AxGegen.axFeuert ((GenStart EZD.AxGegen.wspF).weltVon 1)
      Env.nil σ' hfire'
    have h0 : (((GenStart EZD.AxGegen.wspF).weltVon 1).slots () 0 ()) = false := rfl
    have hM0 : (EZD.AxGegen.wspF.slots () 0 ()) = false := rfl
    show σ'.slots () 0 () ≠ EZD.AxGegen.wspF.slots () 0 ()
    rw [hflip, h0, hM0]
    intro h
    cases h
  refine ⟨EZD.AxGegen.P2w, EZD.AxGegen.O2, 0, EZD.AxGegen.O2gut,
    EZD.AxGegen.progF, EZD.AxGegen.wspF, 0, (), EZD.AxGegen.hNurF, ?_, ?_, ?_⟩
  · refine ⟨_, _, 1, _, _, 0, (), PCReach.start, hs0, by decide, ?_⟩
    exact eigenzustand_nur_eigene_schritte EZD.AxGegen.P2w EZD.AxGegen.O2 0
      EZD.AxGegen.O2gut EZD.AxGegen.progF EZD.AxGegen.wspF 0 ()
      EZD.AxGegen.hNurF _ _ _ _ _ PCReach.start hs0 (by decide) 0 ()
  · exact ⟨(), rfl⟩
  · exact ⟨_, _, hreach2, hne⟩

/-! ## CUTS: what is not proved.

  * The carrier domains of an oracle answer (`tabs₀`/`globs₀` in `GutO`)
    are existentially quantified per call: a `GutO` proof chooses them.
    The caller's extracted atom covers the declared writes only over
    caller-side domains that are complete (`hct`/`hcg`, carried explicitly
    through `Extraktion.execEreignis_aus_axiomCall` and the `Ziel` lifters).
  * `Block.bindAxiom` now carries the guard premises `hd`/`hgd` like
    `Stmt.axiomCall` (reviewer revision, `Syntax.lean`); its `Gut` strength
    flows from the same rewritten `axiomAntwort_gut` through `block_gut`.
  * The per-world guard theorem is gone (reviewer revision): under the
    conditional `GutO` it is unprovable as stated and trivial with guard
    premises. Guarded-table writers exist (`FremdSperre.hOF`,
    `gutO_bewacht_zeuge`); the guard flows from the constructor's `hd`/`hgd`
    plus `HeldGenau` at each discharge site.
  * `stmtTraeger`/`stmtAtome` (`Extraktion.lean`) already list the axiom's
    declared written carriers for `axiomCall`; no change was needed there.
-/

#print axioms Gabbro.Grammatik.axiomCallRecordsWrite
#print axioms Gabbro.Grammatik.foreignStepKeepsSlots
#print axioms Gabbro.Grammatik.eigenzustand_nur_eigene_schritte
#print axioms Gabbro.Grammatik.eigenzustand_nur_eigene_schritte_zeuge
#print axioms Gabbro.Grammatik.eigenzustand_axiom_zeuge

end Gabbro.Grammatik
