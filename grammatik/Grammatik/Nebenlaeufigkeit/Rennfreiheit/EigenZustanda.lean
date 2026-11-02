module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustand
@[expose] public section


namespace Gabbro.Grammatik

open Gabbro.Grammatik.EZD

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
      (EZD.AxGegen.Wflip2 ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []).fragt (.inl ())),
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
        ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt, Ereignis.fremd (.inl ())] ++
        (GenStart EZD.AxGegen.wspF).spuren 1) :
    PCSchritt (P := EZD.AxGegen.P2w) (O := EZD.AxGegen.O2) 0 axiomProg
      (GenStart EZD.AxGegen.wspF) (fun _ => 0) 1
      ⟨σ'.speicher, genUpdate (GenStart EZD.AxGegen.wspF).spuren 1 σ'.spur,
        (GenStart EZD.AxGegen.wspF).lauf ++ genEigen 1
          [Ereignis.zugriff () true []
            ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt, Ereignis.fremd (.inl ())],
        (GenStart EZD.AxGegen.wspF).start,
        (GenStart EZD.AxGegen.wspF).welten ++ [σ'],
        (GenStart EZD.AxGegen.wspF).tiefe + 1⟩
      (pcAdvance (fun _ => 0) 1) := by
  refine PCSchritt.leaf (GenStart EZD.AxGegen.wspF) (fun _ => 0) 1
    (V := EZD.AxGegen.V2) (l := false) (Γ := []) (Λ := []) (Λ' := [])
    (s := EZD.AxGegen.axCall) (ρ := Env.nil) (σ' := σ')
    (neu := [Ereignis.zugriff () true []
      ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt, Ereignis.fremd (.inl ())])
    (Λa := []) (cs := [Sum.inl ()]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    exact nomatch L
  · exact hfire'
  · exact hneu'
  · intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  · rfl
  · rfl
  · intro e he m st hm
    rcases List.mem_cons.mp he with rfl | he
    · simp only [Ereignis.lambda, List.not_mem_nil] at hm
    · simp only [List.mem_singleton] at he
      subst he
      simp only [Ereignis.lambda, List.not_mem_nil] at hm
  · intro e he o ho
    rcases List.mem_cons.mp he with rfl | he
    · have h2 : (Ereignis.zugriff () true []
          ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt).traeger =
          some (Sum.inl ()) := rfl
      rw [h2] at ho
      have ho' : o = Sum.inl () := (Option.some_inj.mp ho).symm
      rw [ho']
      simp only [PCAtom.carriers]
      exact List.mem_singleton.mpr rfl
    · simp only [List.mem_singleton] at he
      subst he
      simp only [Ereignis.traeger, reduceCtorEq] at ho

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
    simp only [List.not_mem_nil] at hm
  · rfl
  · rfl
  · intro e he m st hm
    simp only [List.not_mem_nil] at he
  · intro e he o ho
    simp only [List.not_mem_nil] at he

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
      ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []).fragt (.inl ())) := by
    have hAns2 : axiomAntwort (O := EZD.AxGegen.O2) ()
        (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
        (evalArgs (Γ := []) (Λ := []) (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])
          (Args.nil (D := EZD.AxGegen.D2) (Γ := []) (Λ := []))
          (((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []) Env.nil) =
        (EZD.AxGegen.Wflip2 ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] []).fragt (.inl ())),
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
        ((((GenStart EZD.AxGegen.wspF).weltVon 1).lese [] [])).haelt, Ereignis.fremd (.inl ())] ++
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
