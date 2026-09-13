/-
  File:      Grammatik/AuditZiel.lean
  Subject:   AUDIT of the goal theorem `ziel_ort` (ZielOrtBeweis.lean) and of
             the G repairs -- adversarial probes and counter-lemmas.

   Verdicts (full table in MUSE-REPORT-131.md):
   * `VertragAmOrtG` says requires at entry / ensures at return with the
     ACTUAL logged values -- nothing quantified away (probe E below).
   * `KoerperGut` quantifies over handlers `R`, not over program syntax;
     the domain is inhabited (probe A) and calling bodies satisfy it
     (`zP_koerper_wrap`, cited).
   * `StartExklusiv` over infinite `Faden` is not a decidable program fact;
     for the actual constant thread assignment it collapses to a finite
     check (probe B) -- which EXCLUDES two threads running the same
     lock-holding function (counter-lemma B2, and `ziel_ort_form_falsch`).
   * `e0` is load-bearing (probe F); it excludes carrier-less declarations
     (admitted in the file's CUTS).
   * G models both lock-taking (`locks`, probe D) and signature-held
     functions (probe C); the witness run interleaves two threads (probe E).
-/
import Grammatik.ZielOrtZeuge

namespace Gabbro.Grammatik

/-! ## A. The handler domain of `KoerperGut` is inhabited -/

/-- The empty record defines a handler that respects every contract of `zP`
    (vacuously: no recorded answers to break) and never blames a caller.
    So the `∀ R` of `KoerperGut` ranges over a non-empty domain. -/
theorem audit_handler_inhabited :
    RespektiertVertraege zP (rufAus (D := zD) []) ∧
    OhneVorbedingung (rufAus (D := zD) []) :=
  ⟨rufAus_respektiert (vertraegeOk_nil zP), rufAus_ohneVorbedingung []⟩

/-! ## B. `StartExklusiv`: what it is and what it excludes -/

/-- For a constant thread assignment (every thread starts in `f`), the
    start fact over the infinite `Faden = Nat` collapses to a finite check
    on the signature locks: it holds iff `f` holds no lock at all. So for
    the program's actual (constant) assignment it IS decided by the held
    list -- but the price is exclusion (see `audit_same_lock_start_excluded`
    below). Both directions use every hypothesis. -/
theorem audit_startExklusiv_const (f : zD.Fn) (rho : Env zD (zD.params f)) :
    StartExklusiv (D := zD) (fun _ => ⟨f, rho⟩) ↔
    (∀ L : zD.Lock, L ∈ zD.haelt f → L ∉ zD.haelt f) := by
  constructor
  · intro h L h1 h2
    exact h 0 1 (by decide) L h1 h2
  · intro h t u htu L h1 h2
    exact h L h1 h2

/-- **Counter-lemma.** Two threads running the same lock-holding function
    (`zEin` holds `()` by signature) can never satisfy `StartExklusiv`:
    the most ordinary multithreaded shape -- the same routine on two
    threads -- is outside `ziel_ort` unless the routine holds no lock.
    The lock-free entry `zHaupt` (`zInit_exklusiv`) is not decoration. -/
theorem audit_same_lock_start_excluded :
    ¬ StartExklusiv (D := zD) (fun _ => ⟨zEin, .nil⟩) := by
  intro h
  have hfin := (audit_startExklusiv_const zEin .nil).mp h
  exact hfin () List.mem_cons_self List.mem_cons_self

/-! ## C/D. Both lock disciplines execute on the repaired G -/

/-- A function that relies on the CALLER holding the lock (`zLies` holds
    `()` by signature, `requires Held`) runs on G holding it: the witness
    run reaches a machine whose thread 0 is inside `zLies` holding the lock
    while thread 1 does not. Uses the run, the reachability and both facts. -/
theorem audit_sig_held_executes : ∃ M : RufMaschineG zD,
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
    (M.faeden 0).kopf.f = zLies ∧ (() : zD.Lock) ∈ offen (M.faeden 0).spur ∧
    (() : zD.Lock) ∉ offen (M.faeden 1).spur := by
  obtain ⟨M9, M17, _, h9, h17, _, _, _, _, _, hf, hin, hout, _, _, _⟩ := zLauf
  exact ⟨M17, rufErreichbarG_trans h9 h17, hf, hin, hout⟩

/-- A function that TAKES the lock itself (`zHaupt` holds no lock and runs
    `locks { … }`, the `effects { locks L }` kind) runs on G: thread 0
    starts lock-free and reaches a machine holding the lock. So the repair
    (no bare `nimmt`) did not remove the taking discipline -- it moved it
    into `dannLocks`, which the run fires. -/
theorem audit_takes_lock_executes : ∃ M : RufMaschineG zD,
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
    (() : zD.Lock) ∉ offen ((RufStartG zP zSp zInit).faeden 0).spur ∧
    (() : zD.Lock) ∈ offen (M.faeden 0).spur := by
  obtain ⟨M9, M17, _, h9, h17, _, _, _, _, _, _, hin, _, _, _, _⟩ := zLauf
  refine ⟨M17, rufErreichbarG_trans h9 h17, ?_, hin⟩
  rw [zM0_faden]
  exact List.not_mem_nil

/-! ## E. The witness run is non-degenerate and the conclusion is about actual values -/

/-- Thread 1 writes `konto[0] := 100` while thread 0 has logged nothing but
    its own start; afterwards thread 0 runs `lies` and returns the value
    100 -- a value no step of its own wrote -- and `EnsAmRueck` holds at
    that LOGGED return with the ACTUAL `s0`, `s1`, `rho`, `v`. So the
    witness is non-degenerate (memory moves, calls and returns are logged,
    two threads interleave) and `VertragAmOrtG` quantifies nothing away. -/
theorem audit_cross_thread_return : ∃ M9 M18 : RufMaschineG zD,
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M9 ∧
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M18 ∧
    (M9.speicher.slots () 0 ()).n = 100 ∧
    (M9.faeden 0).log = [RufEreignisF.eintritt zHaupt .nil (zSp.welt [])] ∧
    ∃ (rho : Env zD (zD.params zLies)) (v : ErgVal zD (zD.erg zLies))
      (s0 s1 : World zD),
      RufEreignisF.rueck zLies rho v s0 s1 ∈ (M18.faeden 0).log ∧
      (show Zahl 0 100 from v).n = 100 ∧ (s1.slots () 0 ()).n = 100 ∧
      EnsAmRueck zP zLies s0 s1 rho v := by
  obtain ⟨M9, M17, M18, h9, h17, h18, _, hsp, _, hlog0, _, _, _,
    rho, v, s0, s1, hm, hv, hs, hens⟩ := ziel_ort_zeuge_interferenz
  exact ⟨M9, M18, h9, rufErreichbarG_trans (rufErreichbarG_trans h9 h17) h18,
    hsp, hlog0, rho, v, s0, s1, hm, hv, hs, hens⟩

/-! ## F. `e0` is load-bearing -/

/-- A recorded answer sits one fresh trace event past its key: `e0` is the
    event that keeps the record a function of the key (`funk_append`). -/
theorem audit_antwortWelt_uses_e0 (e0 : Ereignis zD) (s1 κ : World zD) :
    (antwortWelt e0 s1 κ).spur = e0 :: κ.spur := rfl

/-! ## CUTS:

   Proved here:
   * A (`audit_handler_inhabited`): the `∀ R` domain of `KoerperGut` is
     inhabited -- the empty record defines a contract-respecting handler
     that never blames a caller.
   * B (`audit_startExklusiv_const`): for a constant thread assignment
     `StartExklusiv` collapses to a finite check on the signature locks;
     (`audit_same_lock_start_excluded`, counter-lemma): two threads in the
     same lock-holding function never satisfy it.
   * C (`audit_sig_held_executes`): a signature-held function runs holding
     the lock while another thread does not.
   * D (`audit_takes_lock_executes`): a lock-free entry takes the lock
     itself through `locks` -- the taking discipline survived the repair.
   * E (`audit_cross_thread_return`): the witness interleaves two threads
     (thread 0 returns a value written by thread 1) and `EnsAmRueck` holds
     at the logged return with the actual values.
   * F (`audit_antwortWelt_uses_e0`): `e0` supplies the fresh trace position
     of every recorded answer.

   NOT proved here (report findings, no Lean claim):
   * decidability of `StartExklusiv` for non-constant assignments
     (`Faden = Nat` is infinite; only the constant case collapses);
   * carrier-less declarations (no `Ereignis D`, hence no `e0`) -- admitted
     in the CUTS of `ZielOrtBeweis.lean`;
   * loops/axioms/error channel (outside `kOk`; an Opus lane owns G now).
-/

#print axioms Gabbro.Grammatik.audit_handler_inhabited
#print axioms Gabbro.Grammatik.audit_startExklusiv_const
#print axioms Gabbro.Grammatik.audit_same_lock_start_excluded
#print axioms Gabbro.Grammatik.audit_sig_held_executes
#print axioms Gabbro.Grammatik.audit_takes_lock_executes
#print axioms Gabbro.Grammatik.audit_cross_thread_return
#print axioms Gabbro.Grammatik.audit_antwortWelt_uses_e0

end Gabbro.Grammatik
