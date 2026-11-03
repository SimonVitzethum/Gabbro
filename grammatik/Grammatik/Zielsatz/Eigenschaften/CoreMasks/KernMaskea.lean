/-
  File:      Grammatik/Zielsatz/Eigenschaften/KernMaske.lean
  Subject:   THE PER-CORE INTERRUPT-MASK STATE OF MACHINE G (Simon's decision, 2026-10-18; OFFEN
             O19, the rest): the layer `KernZ` over `RufMaschineG`, its step relation
             `KernSchritt`, and `KernHaltE`'s sentence PROVED over it with no schedule premise.

  WHAT WAS MISSING. Machine G keeps no interrupt-mask state. `KernHaltE` (Spec.lean) reads the
  core hardware's two facts -- a handler is entered only where no thread of its core holds a lock
  declared `masks irqs`, and it runs to completion -- as a PREMISE on the run (`KernPlan`). The
  premise was named, not derived: nothing in any machine made a run obey it.

  THE LAYER (outside the statement: `Spec.lean`, `Ziel` and `gabbro_ziel` are not touched; the
  new modules import Spec.lean and nothing imports them).
  * `MaskeKern D = Nat → List (Faden × D.Lock)`: per core, the (thread, lock) pairs that mask it,
    one pair per masking lock a thread of that core holds. A core is masked iff its list is
    nonempty, so NESTING needs no saved bit: a lock released while another masking lock is held
    leaves the core masked, and the last release unmasks (`maske_nichtleer_iff`). ISA-neutral:
    nothing here names an instruction.
  * `KernZ`: a G machine, the mask state, and the set of threads that have stepped.
  * `KernSchritt kern H`: a G step of thread `f` that also (1) ENTRY ONLY WHEN UNMASKED: the
    first step of a handler (`H f`, not begun) needs the mask of its core empty; (2) RUN TO
    COMPLETION: no other thread of the core steps while a begun handler of that core is
    unfinished; (3) acquisition masks and release unmasks: the mask of the acting thread's core
    is recomputed from the thread's new held locks (`maskeNach`). `kern` is the core assignment,
    `H` the handler set (`HandlerVon`).
  * `KernHaltM` is `KernHaltE` over guarded runs `KernLauf`, with NO `KernPlan` premise:
    `kernPlan_aus_lauf` derives the plan from the guards, so `kernHaltM_aus` is `kernHaltE_aus`
    with the schedule PROVED. What stays a premise is what only the program can supply: the
    discipline (a) `AkzeptiertSpec.masken` -- every lock a handler's call graph takes masks --
    and the closure `abg`. Without it a handler enters at an unmasked lock its core's thread
    holds (`KernMaskeZeuge.lean`: the same program deadlocks when the lock does not mask and
    cannot when it does).

  EMBEDDING. Every guarded run IS a G run (`kernLauf_laufG`), so every leg of `Ziel` holds on it.
  Conversely, with no handler every G run lifts to a guarded run (`laufG_kernLauf`), and with no
  `masks irqs` lock the mask list is empty at every machine (`mask_leer_ohne`): programs without
  masked locks and handlers keep exactly the runs they had.

  NOT CLAIMED: that `Spec.lean`'s `KernHaltE` itself is replaced (it still carries `KernPlan`;
  the proposal is in dokumente/PLAN-DYNAMIC.md section 8a.4); the lowering of the mask
  (Code/Conc/KernMaske.lean); handler re-entry and handler-on-handler preemption (a handler runs
  once, and no other thread of its core steps meanwhile, exactly as in `KernPlan`).
-/
module
public import Grammatik.Zielsatz.Eigenschaften.Masken
@[expose] public section


namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. A finished thread never steps, so it stays finished -/

theorem stmt_rueck_nicht_ok {O : Orakel D} {passes : Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : s.istRueck = true) (σ σ' : World D) (ρ ρ' : Env D Γ) :
    execStmt O passes R s σ ρ ≠ Ausgang.ok σ' ρ' := by
  cases s <;> simp_all [Stmt.istRueck, execStmt]

theorem entfaltbar_nicht_rueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : GEntfaltbar s = true) : s.istRueck = false := by
  cases s <;> simp_all [Stmt.istRueck, GEntfaltbar]

/-- **A finished thread has no step**: its stack is empty and its residue stands at a return;
    every step constructor needs a nonempty stack, or a residue that is not a return. -/
theorem fertig_kein_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (hF : FertigG M f) : False := by
  obtain ⟨hst, hr⟩ := hF
  cases hs with
  | g1 hs =>
    cases hs with
    | endeForm l Γ Λ e ρ hl hent hhead =>
      rw [hhead] at hr
      cases e <;> simp_all [GRest.anRueck, Endblock.istRueck, EndEntfaltbar]
    | _ =>
      first
      | (have hp := ‹(M.faeden f).stapel = _ :: _›; rw [hst] at hp; exact absurd hp (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true]))
      | (rw [‹(M.faeden f).kopf.rest = _›] at hr
         simp only [GRest.anRueck, Block.istRueck, Endblock.istRueck] at hr
         first
         | (simp only [Stmt.istRueck, Bool.false_eq_true] at hr; done)
         | exact stmt_rueck_nicht_ok _ hr _ _ _ _ ‹_›
         | (rw [entfaltbar_nicht_rueck _ ‹GEntfaltbar _ = true›] at hr
            exact Bool.noConfusion hr))
  | g2 hs =>
    cases hs with
    | _ =>
      first
      | (have hp := ‹(M.faeden f).stapel = _ :: _›; rw [hst] at hp; exact absurd hp (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true]))
      | (rw [‹(M.faeden f).kopf.rest = _›] at hr
         simp only [GRest.anRueck, Block.istRueck, Endblock.istRueck] at hr
         first
         | (simp only [Stmt.istRueck, Bool.false_eq_true] at hr; done)
         | exact stmt_rueck_nicht_ok _ hr _ _ _ _ ‹_›
         | (rw [entfaltbar_nicht_rueck _ ‹GEntfaltbar _ = true›] at hr
            exact Bool.noConfusion hr))
  | g3 hs =>
    cases hs with
    | _ =>
      first
      | (have hp := ‹(M.faeden f).stapel = _ :: _›; rw [hst] at hp; exact absurd hp (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true]))
      | (rw [‹(M.faeden f).kopf.rest = _›] at hr
         simp only [GRest.anRueck, Block.istRueck, Endblock.istRueck] at hr
         first
         | (simp only [Stmt.istRueck, Bool.false_eq_true] at hr; done)
         | exact stmt_rueck_nicht_ok _ hr _ _ _ _ ‹_›
         | (rw [entfaltbar_nicht_rueck _ ‹GEntfaltbar _ = true›] at hr
            exact Bool.noConfusion hr))
  | g4 hs =>
    cases hs with
    | _ =>
      first
      | (have hp := ‹(M.faeden f).stapel = _ :: _›; rw [hst] at hp; exact absurd hp (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true]))
      | (rw [‹(M.faeden f).kopf.rest = _›] at hr
         simp only [GRest.anRueck, Block.istRueck, Endblock.istRueck] at hr
         first
         | (simp only [Stmt.istRueck, Bool.false_eq_true] at hr; done)
         | exact stmt_rueck_nicht_ok _ hr _ _ _ _ ‹_›
         | (rw [entfaltbar_nicht_rueck _ ‹GEntfaltbar _ = true›] at hr
            exact Bool.noConfusion hr))
  | g5 hs =>
    cases hs with
    | _ =>
      first
      | (have hp := ‹(M.faeden f).stapel = _ :: _›; rw [hst] at hp; exact absurd hp (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true]))
      | (rw [‹(M.faeden f).kopf.rest = _›] at hr
         simp only [GRest.anRueck, Block.istRueck, Endblock.istRueck] at hr
         first
         | (simp only [Stmt.istRueck, Bool.false_eq_true] at hr; done)
         | exact stmt_rueck_nicht_ok _ hr _ _ _ _ ‹_›
         | (rw [entfaltbar_nicht_rueck _ ‹GEntfaltbar _ = true›] at hr
            exact Bool.noConfusion hr))
  | g6 hs =>
    cases hs with
    | _ =>
      first
      | (have hp := ‹(M.faeden f).stapel = _ :: _›; rw [hst] at hp; exact absurd hp (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true]))
      | (rw [‹(M.faeden f).kopf.rest = _›] at hr
         simp only [GRest.anRueck, Block.istRueck, Endblock.istRueck] at hr
         first
         | (simp only [Stmt.istRueck, Bool.false_eq_true] at hr; done)
         | exact stmt_rueck_nicht_ok _ hr _ _ _ _ ‹_›
         | (rw [entfaltbar_nicht_rueck _ ‹GEntfaltbar _ = true›] at hr
            exact Bool.noConfusion hr))

  | g7 hs =>
    cases hs with
    | rueckScopedWert ρ r e R hhead hret
    | rueckScopedWertDirekt ρ r e R hhead hret =>
      rcases GRest.scopedWert_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r <;>
        rw [hhead] at hr <;> simp only [GRest.anRueck, Endblock.istRueck, Block.istRueck, Stmt.istRueck, Bool.false_eq_true, reduceCtorEq] at hr
    | rueckScopedGrund ρ r grund R hhead hret
    | rueckScopedGrundDirekt ρ r grund R hhead hret =>
      rcases GRest.scopedGrund_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;> subst r <;>
        rw [hhead] at hr <;> simp only [GRest.anRueck, Endblock.istRueck, Block.istRueck, Stmt.istRueck, Bool.false_eq_true, reduceCtorEq] at hr
    | _ =>
      rw [‹(M.faeden f).kopf.rest = _›] at hr
      simp only [GRest.anRueck, Endblock.istRueck, Block.istRueck, Stmt.istRueck, Bool.false_eq_true] at hr

/-- A finished thread stays finished: other threads leave it alone, and it does not step. -/
theorem fertig_bleibt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f g : Faden} (hs : RufSchrittG P O passes M f M')
    (hF : FertigG M g) : FertigG M' g := by
  by_cases hg : g = f
  · subst hg
    exact (fertig_kein_schritt hs hF).elim
  · have e := rufSchrittG_fremd hs g hg
    unfold FertigG
    rw [e]
    exact hF

theorem fertig_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n) {g : Faden} {k : Nat} (hk : FertigG (ms k) g) :
    ∀ j, k ≤ j → j ≤ n → FertigG (ms j) g := by
  have key : ∀ d, k + d ≤ n → FertigG (ms (k + d)) g := by
    intro d
    induction d with
    | zero => intro _; exact hk
    | succ d ih =>
        intro hjn
        exact fertig_bleibt (hl.2 (k + d) (by omega)) (ih (by omega))
  intro j hkj hjn
  have e : k + (j - k) = j := by omega
  have := key (j - k) (by omega)
  rw [e] at this
  exact this

/-! ## 2. The mask state -/

/-- **Per-core interrupt-mask state**: for each core, the (thread, lock) pairs that mask it. -/
abbrev MaskeKern (D : Deklaration) := Nat → List (Faden × D.Lock)

/-- The masking entries of thread `f` holding the locks of trace `s`: one per held lock declared
    `masks irqs`. -/
def maskEintr (f : Faden) (s : List (Ereignis D)) : List (Faden × D.Lock) :=
  ((offen s).filter fun L => D.maskiert L).map fun L => (f, L)

/-- **The mask transition of a step of thread `f`** whose new trace is `s`: on `f`'s core the old
    entries of `f` are replaced by the entries of its new held locks -- a taken masking lock adds
    its entry (ACQUISITION MASKS), a released one drops it (RELEASE UNMASKS), the entries of the
    locks still held stay (NESTING). Every other core is untouched. -/
def maskeNach (kern : Faden → Nat) (mk : MaskeKern D) (f : Faden) (s : List (Ereignis D)) :
    MaskeKern D :=
  fun c => if c = kern f then (mk c).filter (fun e => decide (e.1 ≠ f)) ++ maskEintr f s else mk c

theorem mem_maskEintr {f f' : Faden} {L : D.Lock} {s : List (Ereignis D)} :
    (f', L) ∈ maskEintr f s ↔ f' = f ∧ D.maskiert L = true ∧ L ∈ offen s := by
  unfold maskEintr
  simp only [List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨L', ⟨h1, h2⟩, rfl, rfl⟩
    exact ⟨rfl, h2, h1⟩
  · rintro ⟨rfl, h2, h1⟩
    exact ⟨L, ⟨h1, h2⟩, rfl, rfl⟩

/-- **The mask state is consistent with the machine**: a pair is in the list of a core iff the
    thread runs on that core, holds the lock, and the lock is declared `masks irqs`. -/
def MaskeOk (kern : Faden → Nat) (M : RufMaschineG D) (mk : MaskeKern D) : Prop :=
  ∀ (c : Nat) (f : Faden) (L : D.Lock), (f, L) ∈ mk c ↔
    (kern f = c ∧ D.maskiert L = true ∧ L ∈ offen (M.faeden f).spur)

/-- **The transition keeps the state consistent**: only the acting thread's trace moves in a G
    step (`rufSchrittG_fremd`). -/
theorem maskeOk_schritt {P : Programm D} {O : Orakel D} {passes : Nat} {kern : Faden → Nat}
    {M M' : RufMaschineG D} {f : Faden} {mk : MaskeKern D}
    (hs : RufSchrittG P O passes M f M') (h : MaskeOk kern M mk) :
    MaskeOk kern M' (maskeNach kern mk f (M'.faeden f).spur) := by
  intro c f' L
  unfold maskeNach
  by_cases hc : c = kern f
  · rw [if_pos hc, List.mem_append, List.mem_filter, mem_maskEintr]
    by_cases hf : f' = f
    · subst hf
      constructor
      · rintro (⟨_, h2⟩ | ⟨_, h2, h3⟩)
        · simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true] at h2
        · exact ⟨hc.symm, h2, h3⟩
      · rintro ⟨_, h2, h3⟩
        exact Or.inr ⟨rfl, h2, h3⟩
    · rw [rufSchrittG_fremd hs f' hf]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
        · exact (h c f' L).1 h1
        · exact absurd h1 hf
      · intro h1
        exact Or.inl ⟨(h c f' L).2 h1, by simpa using hf⟩
  · rw [if_neg hc]
    by_cases hf : f' = f
    · subst hf
      constructor
      · intro hm
        exact absurd ((h c f' L).1 hm).1.symm hc
      · rintro ⟨h1, _⟩
        exact absurd h1.symm hc
    · rw [rufSchrittG_fremd hs f' hf]
      exact h c f' L


end Gabbro.Grammatik.Zielsatz
