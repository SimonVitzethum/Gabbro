/-
  File:      Grammatik/Referenz104Rahmen.lean
  Subject:   `beispiele/104-referenz.gab` CERTIFIED by the goal theorem over
             declared frames (`ziel_ort_rahmen`): every premise holds
             jointly on the hand translation `r4P` of `Referenz104.lean`,
             and the conclusion holds on its reached run.

  The finding of `Referenz104.lean` was `r4_einzahlen_nicht_V`: `einzahlen`
  (`k.slots[i].stand = 100; lies(k, i);` with `ensures old(stand) <=
  stand`) does not meet `KoerperGutV`, because a contract-respecting
  handler may answer `lies` with the slot reset. Against frame-respecting
  handlers (`KoerperGutR`) it does: `lies` declares no write, so the handler's
  answer keeps every slot, the slot is still `100` after the call, and
  `old(stand) <= 100` holds because `stand : 0 .. 100` (`r4_einzahlen_R`).
  So `KoerperGutR` is STRICTLY weaker than `KoerperGutV` on this program
  (`r4_rahmen_echt_schwaecher`).
-/
import Grammatik.Referenz104
import Grammatik.ZielOrtRahmen

namespace Gabbro.Grammatik

/-! ## 1. `einzahlen` meets the obligation against declared frames -/

/-- **`einzahlen` of `104-referenz.gab` meets `KoerperGutR`.** The body
    writes `100` into the slot, calls `lies` (whose signature writes
    nothing: every frame-respecting answer keeps the slots), and returns;
    `old(stand) <= stand` is `old(stand) <= 100`, true by the slot's range.
    The caller duty holds: `lies` requires `true`, the gate lets it through,
    and the handler blames nobody. -/
theorem r4_einzahlen_R : KoerperGutR r4P 0 r4Ein := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : r4P.rumpf r4Ein = r4RumpfEin := rfl
    rw [hr] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [r4Schreib, execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [r4RufLies, execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [r4RetEin, execEnd] at hrun2
    simp only [r4RufLies, execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      -- the frame of `lies` (no declared write) keeps the slot table
      have hfr := (hR.2 r4Lies _ _ σ2 w hRv).1.1 () rfl
      simp only [r4Schreib, execStmt] at h1
      cases h1
      show decide ((σ.slots () (ρ.get (.dort .hier)).n ()).n ≤
        (σ2.slots () (ρ.get (.dort .hier)).n ()).n) = true
      have e3 := (hfr (ρ.get (.dort .hier)).n ()).trans (storeSlot_hit (D := r4D) _ () _ () _)
      have h100 : (σ2.slots () (ρ.get (.dort .hier)).n ()).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots () (ρ.get (.dort .hier)).n ()).le_hi (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · have hr : r4P.rumpf r4Ein = r4RumpfEin := rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [r4Schreib, execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact r4_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [r4RetEin, execEnd] at h2
        cases h2

/-- **The new obligation is strictly weaker**: on `einzahlen` of
    `104-referenz.gab` it holds, the old one fails. -/
theorem r4_rahmen_echt_schwaecher : KoerperGutR r4P 0 r4Ein ∧ ¬ KoerperGutV r4P 0 r4Ein :=
  ⟨r4_einzahlen_R, r4_einzahlen_nicht_V⟩

/-- Every function of the translation meets `KoerperGutR`: `einzahlen`
    directly, `lies`, the driver and the idle function through their old
    obligations (`koerperGutR_of_V`). -/
theorem r4P_koerperR : ∀ f : r4D.Fn, KoerperGutR r4P 0 f
  | .einzahlen => r4_einzahlen_R
  | .lies => koerperGutR_of_V r4P_koerper_lies
  | .treiber => koerperGutR_of_V r4P_koerper_treiber
  | .ruhe => koerperGutR_of_V r4P_koerper_ruhe

/-! ## 2. The remaining premises -/

/-- The declaration has no register and no global: the oracle is local. -/
theorem r4O_lokal : RegLokal r4O := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

theorem r4P_fragmentG : programmImFragmentG r4P r4Fs = true := by decide

theorem r4P_fussG : fussOrtGB r4P r4Fs = true := by decide

/-- The declaration has a lock: a trace event exists. -/
def r4E0 : Ereignis r4D := .nimmt () []

/-! ## 3. The certificate -/

/-- **`ziel_ort_rahmen_ref104` -- `beispiele/104-referenz.gab` certified.**
    On the hand translation `r4P` (with the flagged driver and idle
    function), ALL premises of `ziel_ort_rahmen` hold jointly: the hardware
    facts `GutO`/`RegLokal` of the oracle, the complete member list, the
    decided fragment and footprint check, the user obligation `KoerperGutR`
    of every function (`einzahlen` included), the start contracts and the
    exclusive start. Hence the goal theorem's conclusion holds on EVERY
    reachable machine; and on the reached run of `Referenz104.lean` (memory
    `0 -> 100`, the return of `einzahlen` logged) it holds there too, in
    particular the `ensures` of `einzahlen` at its logged return. -/
theorem ziel_ort_rahmen_ref104 :
    GutO r4O ∧ RegLokal r4O ∧ (∀ g : r4D.Fn, g ∈ r4Fs) ∧
    programmImFragmentG r4P r4Fs = true ∧ fussOrtGB r4P r4Fs = true ∧
    (∀ f : r4D.Fn, KoerperGutR r4P 0 f) ∧ StartGut r4P r4Sp r4Init ∧
    StartExklusiv (D := r4D) r4Init ∧
    (∀ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M →
      VertragAmOrtG r4P M) ∧
    ∃ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
      (r4Sp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
        RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck r4P r4Ein s0 s1 rho ()) ∧
      VertragAmOrtG r4P M := by
  have hZ := ziel_ort_rahmen r4P r4O 0 r4Fs r4Sp r4Init r4E0 r4O_gut r4O_lokal r4Fs_voll
    r4P_fragmentG r4P_fussG r4P_koerperR r4P_start r4Init_exklusiv
  obtain ⟨M, hr, hsp, ⟨rho, s0, s1, hlog⟩, _⟩ := r4Lauf
  have hV := hZ M hr
  refine ⟨r4O_gut, r4O_lokal, r4Fs_voll, r4P_fragmentG, r4P_fussG, r4P_koerperR, r4P_start,
    r4Init_exklusiv, hZ, M, hr, rfl, hsp, ⟨rho, s0, s1, hlog, ?_⟩, hV⟩
  exact (hV 0 _ hlog).2 r4Ein rho () s0 s1 rfl

/-! ## CUTS:

  What is proved: `einzahlen` of `104-referenz.gab` meets `KoerperGutR`
  (`r4_einzahlen_R`), so the new obligation is strictly weaker than
  `KoerperGutV` (`r4_rahmen_echt_schwaecher`); every premise of
  `ziel_ort_rahmen` holds jointly on the hand translation `r4P`, the
  conclusion `VertragAmOrtG` follows for every reachable machine, and on the
  reached run of `r4Lauf` the `ensures` of `einzahlen` holds at its logged
  return -- now from the goal theorem, not by direct computation
  (`ziel_ort_rahmen_ref104`).

  What is NOT covered: the translation is by hand (`Referenz104.lean`, its
  construct table and its NO-FORM constructs: module, named constants,
  carrier widths, address spaces, the lock hold budget, the `reads` effect,
  the implicit fall-off return, the `rw`-to-`r` pointer coercion, `old(p->f)`
  through a pointer); the driver `treiber` and the idle function `ruhe` are
  flagged additions; the declared costs are checked by `kostenPasst`
  (`r4P_kostenPasst`) separately, not by this theorem. No emitter or checker
  computes these premises for the corpus file.
-/

#print axioms Gabbro.Grammatik.r4_einzahlen_R
#print axioms Gabbro.Grammatik.r4_rahmen_echt_schwaecher
#print axioms Gabbro.Grammatik.r4P_fragmentG
#print axioms Gabbro.Grammatik.r4P_fussG
#print axioms Gabbro.Grammatik.ziel_ort_rahmen_ref104

end Gabbro.Grammatik
