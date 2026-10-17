/- Part 9 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T8

namespace Gabbro.Grammatik.Extraktion

variable {D : Deklaration}

/-- The hwit prefix fold over whole `PCReach` runs, non-oracle leaves: the
    prefix witness duty (`hwit_old` shape) holds at the end of a single-thread
    run whose every fired leaf meets the producer premises. The scheduler
    steps accumulate as a bare list (`[]` at `start` via `hwit_leer` over the
    posited empty joint run `J₀`, `++ [f]` per step via `hwit_alt_schritt`);
    foreign steps are ruled out by counter routing (`hsingle_prog`); each
    fired leaf discharges through `hwit_aus_feuerung_ohne_axiomCall`
    (`hax_all` kills the oracle case, `hmem_all` names the carrier,
    `hbytes_all` feeds the byte case); lock steps inherit the posited prefix
    witness (`hwit_lock`). Every premise is load-bearing. -/
theorem hwit_alt_faltung
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Nb : Nebeneinander) (J₀ : GemeinsamerLauf (D := D) Nb)
    (hempty : J₀.schrittFaden = [])
    (code : Faden → D.Fn) (hcode : J₀.code = code)
    (t₀ : D.Tab) (f : Faden)
    (tabs : List D.Tab) (globs : List D.Glob)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hax_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      (match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True))
    (hmem_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'),
      (match s with | .putBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True))
    (hwit_lock : ∀ (Mx : GenMaschine D) (pcx : PCStand),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        Mx.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)))
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    ∃ (sched : List Faden),
      ∀ (k : Nat) (g : Faden), sched[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  induction h with
  | start =>
    have hbase := hwit_leer Nb J₀ (GenStart sp).lauf t₀ hempty
    rw [hempty, hcode] at hbase
    exact ⟨[], hbase⟩
  | step Mmid Mend pcmid pcend g hmid hs ih =>
    obtain ⟨sched, hduty⟩ := ih
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine ⟨sched ++ [f], ?_⟩
      show ∀ (k : Nat) (g : Faden), (sched ++ [f])[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          (Mmid.lauf ++ genEigen f neu)[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he))
      have hnew : TraegerSchreibt (code f) (.inl t₀) = true →
          ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
            (Mmid.lauf ++ genEigen f neu)[j]? =
              some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
        intro _
        obtain ⟨w, Λw, hwL, hmem_neu⟩ :=
          hwit_aus_feuerung_ohne_axiomCall O passes s hleaf
            (hax_all V l Γ Λ Λ' s hleaf) tabs globs t₀
            (hmem_all V l Γ Λ Λ' s hleaf) (hbytes_all V l Γ Λ Λ' s)
            (Mmid.weltVon f) ρ σ' neu hstep hneu
        obtain ⟨j, hj⟩ := hwit_alt_transport Mmid.lauf f neu _ hmem_neu
        exact ⟨j, w, Λw, hwL, hj⟩
      exact hwit_alt_schritt code sched Mmid.lauf f neu t₀ hduty hnew
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine ⟨sched ++ [f], ?_⟩
      show ∀ (k : Nat) (g : Faden), (sched ++ [f])[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          (Mmid.lauf ++ genEigen f [Ereignis.nimmt L (offen (Mmid.spuren f))])[j]? =
            some (Schritt.mk g (.zugriff t₀ w Λe he))
      have hnew : TraegerSchreibt (code f) (.inl t₀) = true →
          ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
            (Mmid.lauf ++ genEigen f [Ereignis.nimmt L (offen (Mmid.spuren f))])[j]? =
              some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
        intro hwr
        obtain ⟨j, w, Λe, he, hw⟩ := hwit_lock Mmid pcmid hmid hwr
        have hjlt : j < Mmid.lauf.length := by
          by_cases h : j < Mmid.lauf.length
          · exact h
          · have hle : Mmid.lauf.length ≤ j := by omega
            rw [List.getElem?_eq_none hle] at hw
            simp at hw
        refine ⟨j, w, Λe, he, ?_⟩
        rw [List.getElem?_append_left hjlt]
        exact hw
      exact hwit_alt_schritt code sched Mmid.lauf f
        [Ereignis.nimmt L (offen (Mmid.spuren f))] t₀ hduty hnew
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine ⟨sched ++ [f], ?_⟩
      show ∀ (k : Nat) (g : Faden), (sched ++ [f])[k]? = some g →
        TraegerSchreibt (code g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          (Mmid.lauf ++ genEigen f [Ereignis.gibt L])[j]? =
            some (Schritt.mk g (.zugriff t₀ w Λe he))
      have hnew : TraegerSchreibt (code f) (.inl t₀) = true →
          ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
            (Mmid.lauf ++ genEigen f [Ereignis.gibt L])[j]? =
              some (Schritt.mk f (.zugriff t₀ w Λe he)) := by
        intro hwr
        obtain ⟨j, w, Λe, he, hw⟩ := hwit_lock Mmid pcmid hmid hwr
        have hjlt : j < Mmid.lauf.length := by
          by_cases h : j < Mmid.lauf.length
          · exact h
          · have hle : Mmid.lauf.length ≤ j := by omega
            rw [List.getElem?_eq_none hle] at hw
            simp at hw
        refine ⟨j, w, Λe, he, ?_⟩
        rw [List.getElem?_append_left hjlt]
        exact hw
      exact hwit_alt_schritt code sched Mmid.lauf f
        [Ereignis.gibt L] t₀ hduty hnew

#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_transport
#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_schritt
#print axioms Gabbro.Grammatik.Extraktion.hwit_alt_faltung

/-! ## 21. Witness duties from firing: `hwit_aus_lauf`

    The fold `kette_aus_lauf_bezeugt` (`MaschinenKette.lean`, read-only here)
    takes two witness duties as hypotheses at every step: per firing
    (`hwit_leaf`: the fired leaf records its access) and per prefix
    (`hwit_lock`: the prefix already records one). As STATED they are not
    theorems but scheduler/witness duties, and they cannot be -- the
    `hwit_leaf` quantifier leaves `neu` free (`hstep` does not mention it,
    so `neu = []` refutes the instance), and the `hwit_lock` quantifier
    ranges over the start machine (whose run is empty, so no `zugriff`
    step exists to exhibit). This section discharges both duties over the
    fragment where firing produces: non-oracle single-thread table runs
    over lock-free programs. Nothing existing moves; read-only reuse of
    `hwit_aus_feuerung_ohne_axiomCall` (§19), `hwit_alt_transport` (§20),
    and the `PCSchritt` fired-step shapes (`Maschine.lean`).

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `hwit_aus_lauf_blatt` (leaf leg): every fired producing leaf
      satisfies the `hwit_leaf` CONCLUSION -- `neu` carries a `zugriff`
      event for `t₀`. One positional application of the §19 producer with
      the pre-world fixed to the acting thread's machine world
      (`M.weltVon f`); the `hneu` spur equation rides the fired step, as
      in §20. The `hwit_leaf` code predicate (`TraegerSchreibt`) is
      VACUOUS here and hence dropped, not carried: the event exists
      whenever the writing leaf fires, as §19 already books. The
      held-footprint premise (`HeldGenau`) is not needed either --
      production is by `execStmt` construction alone -- so the leg is
      strictly stronger than the duty instance. Every premise is
      load-bearing.
    - `hwit_aus_lauf` (prefix leg): every prefix of a single-thread run
      over a lock-free program whose every fired leaf meets the producer
      premises EITHER is empty OR satisfies the `hwit_lock` conclusion
      (a `zugriff` step for `t₀` sits in its run). Induction over
      `PCReach`: the base holds by `rfl` (the start run is empty);
      foreign steps die by counter routing (`hsingle_prog`); leaf steps
      establish the right leg through the blatt leg plus transport; lock
      steps are impossible (`hlockfree` contradicts the pointed-to
      `take`/`rel` atom). Every premise is load-bearing, and there is no
      `have _ :=` discard.

    Coverage (exactly): single-thread `PCReach` runs over programs with
    no `take`/`rel` atom on the acting thread, whose every fired leaf is
    a non-oracle leaf writing the tracked TABLE carrier `t₀` (with
    `0 < n` for `schreibBytes`).

    Remainder (booked, not hidden): `axiomCall` leaves (killed by
    `hax_all`, same class as the §19 remainder); leaves that write no
    table and empty `schreibBytes` (no event exists to produce);
    globals (`gzugriff`); programs WITH lock atoms (the lock step from
    an empty prefix genuinely records no `zugriff`, so the unconditional
    prefix duty is false there -- the disjunction marks exactly this);
    the empty prefix itself (left leg of the disjunction); multi-thread
    runs.
-/

/-- Every fired producing leaf satisfies the `hwit_leaf` conclusion:
    `neu` carries a `zugriff` event for `t₀`. The §19 producer applied
    positionally with the pre-world fixed to the acting thread's machine
    world; the duty's code predicate is vacuous once the leaf produces
    and is hence dropped. Every premise is load-bearing: `hleaf` kills
    the compounds, `hax` the oracle case, `hmem` names the carrier,
    `hbytes` feeds the byte case, `hstep`/`hneu` give the spur equation
    of the fired step. -/
theorem hwit_aus_lauf_blatt
    (O : Orakel D) (passes : Nat)
    (M : GenMaschine D) (f : Faden)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true)
    (hax : match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True)
    (tabs : List D.Tab) (globs : List D.Glob)
    (t₀ : D.Tab) (hmem : .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes : match s with | .putBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True)
    (ρ : Env D Γ)
    (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ M.spuren f) :
    ∃ (w : Bool) (Λw : List (Res D)) (hwL : List D.Lock),
      Ereignis.zugriff t₀ w Λw hwL ∈ neu :=
  hwit_aus_feuerung_ohne_axiomCall O passes s hleaf hax tabs globs t₀ hmem hbytes
    (M.weltVon f) ρ σ' neu hstep hneu

#print axioms Gabbro.Grammatik.Extraktion.hwit_aus_lauf_blatt

/-- Every prefix of a single-thread lock-free run with producing leaves
    either is empty or satisfies the `hwit_lock` conclusion: a `zugriff`
    step for `t₀` sits in its run. The base is the empty start run
    (`Or.inl rfl`); each leaf step establishes the right leg through
    `hwit_aus_lauf_blatt` plus `hwit_alt_transport`; lock steps die at
    `hlockfree`, foreign steps at `hsingle_prog`. Every premise is
    load-bearing. -/
theorem hwit_aus_lauf
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (code : Faden → D.Fn) (t₀ : D.Tab) (f : Faden)
    (tabs : List D.Tab) (globs : List D.Glob)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hlockfree : ∀ (n : Nat) (L : D.Lock),
      (prog f)[n]? ≠ some (PCAtom.take L) ∧ (prog f)[n]? ≠ some (PCAtom.rel L))
    (hax_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      (match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True))
    (hmem_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      .inl t₀ ∈ stmtTraeger tabs globs s)
    (hbytes_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'),
      (match s with | .putBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True))
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    M.lauf = [] ∨ (TraegerSchreibt (code f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        M.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he))) := by
  induction h with
  | start =>
    exact Or.inl rfl
  | step Mmid Mend pcmid pcend g _hmid hs _ih =>
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      refine Or.inr ?_
      intro _
      obtain ⟨w, Λw, hwL, hmem_neu⟩ :=
        hwit_aus_lauf_blatt O passes Mmid f s hleaf
          (hax_all V l Γ Λ Λ' s hleaf) tabs globs t₀
          (hmem_all V l Γ Λ Λ' s hleaf) (hbytes_all V l Γ Λ Λ' s)
          ρ σ' neu hstep hneu
      obtain ⟨j, hj⟩ := hwit_alt_transport Mmid.lauf f neu _ hmem_neu
      show ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        (Mmid.lauf ++ genEigen f neu)[j]? =
          some (Schritt.mk f (.zugriff t₀ w Λe he))
      exact ⟨j, w, Λw, hwL, hj⟩
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      exact absurd hpc (hlockfree (pcmid f) L).1
    · have hact : f = g := by
        by_cases hgf : g = f
        · exact hgf.symm
        · have hprog_empty : prog g = [] := hsingle_prog g hgf
          rw [hprog_empty] at hpc
          simp at hpc
      subst hact
      exact absurd hpc (hlockfree (pcmid f) L).2

#print axioms Gabbro.Grammatik.Extraktion.hwit_aus_lauf

/-! ## 22. The memory-contract instance: `SpeicherVertrag` over `QRequires` / `QEnsures`

    The downstream fold of the §23 engine (`InterferenzAllgemein.lean`,
    read-only here): a `World.speicher` equality unfolds into slot and global
    agreements, and the contract predicates fold over the diagonal
    (`eval_liest_nur_speicher_diag`).

    What is proved (no `sorry`, no `admit`, no `axiom`):

    - `speicherVertrag_aus_Q`: the contracts of `P` at `f` -- `QRequires P`
      as `Pre`, `QEnsures P` as `Post` -- read only live memory. Both legs
      unfold the memory equality into pointwise slot/global agreement
      (`congrArg` on the `Speicher` projections) and fold the contract
      predicate over the diagonal: `requires` quantifies over parameter
      environments, `ensures` over return values and parameter environments,
      and each instance meets the diagonal at exactly its environment.
      Every premise is load-bearing: `hmem` feeds both `hS` and `hG`,
      and both fire in every diagonal call.

    Coverage (exactly): both `SpeicherVertrag` legs (`memPre`, `memPost`)
    for every program `P` and every function `f`, with no footprint premise.

    Remainder (booked, not hidden): none -- the fold closes fully.
-/

/-- The contracts of `P` at `f` read only live memory: worlds over the same
    memory agree on `requires` and on `ensures`. The memory equality unfolds
    into pointwise slot/global agreement; each contract predicate then folds
    over the `eval` diagonal at its own environment. -/
theorem speicherVertrag_aus_Q (P : Programm D) (f : D.Fn) :
    SpeicherVertrag (QRequires P) (QEnsures P) f :=
  { memPre := by
      intro σ σ' hmem
      have hS : ∀ t : D.Tab, ∀ (k : Int) (f' : D.Feld t),
          σ.slots t k f' = σ'.slots t k f' :=
        fun t k f' => congrArg (fun s : Speicher D => s.slots t k f') hmem
      have hG : ∀ g : D.Glob, σ.globs g = σ'.globs g :=
        fun g => congrArg (fun s : Speicher D => s.globs g) hmem
      simp only [QRequires, QExpr]
      constructor
      · intro h ρ
        have he := eval_liest_nur_speicher_diag (P.requires f) σ σ' ρ hS hG
        rw [← he]
        exact h ρ
      · intro h ρ
        have he := eval_liest_nur_speicher_diag (P.requires f) σ σ' ρ hS hG
        rw [he]
        exact h ρ
    , memPost := by
      intro σ σ' hmem
      have hS : ∀ t : D.Tab, ∀ (k : Int) (f' : D.Feld t),
          σ.slots t k f' = σ'.slots t k f' :=
        fun t k f' => congrArg (fun s : Speicher D => s.slots t k f') hmem
      have hG : ∀ g : D.Glob, σ.globs g = σ'.globs g :=
        fun g => congrArg (fun s : Speicher D => s.globs g) hmem
      simp only [QEnsures]
      constructor
      · intro h v ρ
        have he := eval_liest_nur_speicher_diag (P.ensures f) σ σ'
          (ergEnv (D.erg f) v ρ) hS hG
        rw [← he]
        exact h v ρ
      · intro h v ρ
        have he := eval_liest_nur_speicher_diag (P.ensures f) σ σ'
          (ergEnv (D.erg f) v ρ) hS hG
        rw [he]
        exact h v ρ }

#print axioms Gabbro.Grammatik.Extraktion.speicherVertrag_aus_Q



end Gabbro.Grammatik.Extraktion
