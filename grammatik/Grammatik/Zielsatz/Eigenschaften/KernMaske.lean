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
  the proposal is in dokumente/PLAN-DYNAMISCH.md section 8a.4); the lowering of the mask
  (Code/Conc/KernMaske.lean); handler re-entry and handler-on-handler preemption (a handler runs
  once, and no other thread of its core steps meanwhile, exactly as in `KernPlan`).
-/
import Grammatik.Zielsatz.Eigenschaften.Masken

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
  | endeForm l Γ Λ e ρ hl hent hhead =>
    rw [hhead] at hr
    cases e <;> simp_all [GRest.anRueck, Endblock.istRueck, EndEntfaltbar]
  | _ =>
    first
    | (have hp := ‹(M.faeden f).stapel = _ :: _›; rw [hst] at hp; exact absurd hp (by simp))
    | (rw [‹(M.faeden f).kopf.rest = _›] at hr
       simp only [GRest.anRueck, Block.istRueck, Endblock.istRueck] at hr
       first
       | (simp [Stmt.istRueck] at hr; done)
       | exact stmt_rueck_nicht_ok _ hr _ _ _ _ ‹_›
       | (rw [entfaltbar_nicht_rueck _ ‹GEntfaltbar _ = true›] at hr
          exact Bool.noConfusion hr))

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
        · simp at h2
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

/-- **A core is masked iff some thread of it holds a masking lock** (the state is no more and no
    less than that, nesting included). -/
theorem maske_nichtleer_iff {kern : Faden → Nat} {M : RufMaschineG D} {mk : MaskeKern D}
    (h : MaskeOk kern M mk) (c : Nat) :
    mk c ≠ [] ↔ ∃ (f : Faden) (L : D.Lock), kern f = c ∧ D.maskiert L = true ∧
      L ∈ offen (M.faeden f).spur := by
  constructor
  · intro hne
    obtain ⟨⟨f, L⟩, he⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨f, L, (h c f L).1 he⟩
  · rintro ⟨f, L, h1⟩ hnil
    have := (h c f L).2 h1
    rw [hnil] at this
    exact List.not_mem_nil this

/-- **Without a lock declared `masks irqs` no core is ever masked.** -/
theorem mask_leer_ohne {kern : Faden → Nat} {M : RufMaschineG D} {mk : MaskeKern D}
    (hmk : ∀ L : D.Lock, D.maskiert L = false) (h : MaskeOk kern M mk) (c : Nat) : mk c = [] := by
  by_cases hnil : mk c = []
  · exact hnil
  · obtain ⟨f, L, _, hm, _⟩ := (maske_nichtleer_iff h c).1 hnil
    rw [hmk L] at hm
    exact Bool.noConfusion hm

/-- With no masking lock the empty state is consistent with every machine. -/
theorem maskeOk_leer_ohne {kern : Faden → Nat} {M : RufMaschineG D}
    (hmk : ∀ L : D.Lock, D.maskiert L = false) : MaskeOk kern M (fun _ => []) := by
  intro c f L
  constructor
  · intro hm
    exact absurd hm List.not_mem_nil
  · rintro ⟨_, hm, _⟩
    rw [hmk L] at hm
    exact Bool.noConfusion hm

/-! ## 3. The guarded machine -/

/-- **G with the mask state**: a G machine, the per-core mask, and the threads that have stepped. -/
structure KernZ (D : Deklaration) where
  m : RufMaschineG D
  mask : MaskeKern D
  begonnen : Faden → Prop

/-- **One step of the machine with the mask state.** `kern` assigns the cores, `H` says which
    threads are interrupt handlers (`HandlerVon`). -/
structure KernSchritt (P : Programm D) (O : Orakel D) (passes : Nat) (kern : Faden → Nat)
    (H : Faden → Prop) (Z : KernZ D) (f : Faden) (Z' : KernZ D) : Prop where
  /-- the step is a step of machine G -/
  schritt : RufSchrittG P O passes Z.m f Z'.m
  /-- ENTRY ONLY WHEN UNMASKED: a handler's first step needs its core's mask empty -/
  eintritt : H f → ¬ Z.begonnen f → Z.mask (kern f) = []
  /-- RUN TO COMPLETION: while a begun handler of the core is unfinished, only it steps -/
  vollendung : ∀ g, H g → Z.begonnen g → ¬ FertigG Z.m g → kern g = kern f → g = f
  /-- acquisition masks, release unmasks -/
  maske : Z'.mask = maskeNach kern Z.mask f (Z'.m.faeden f).spur
  /-- the acting thread has begun -/
  begonnen : Z'.begonnen = fun g => g = f ∨ Z.begonnen g

/-- A run of `n` guarded steps, by index. -/
def KernLauf (P : Programm D) (O : Orakel D) (passes : Nat) (kern : Faden → Nat)
    (H : Faden → Prop) (Z0 : KernZ D) (zs : Nat → KernZ D) (fs : Nat → Faden) (n : Nat) : Prop :=
  zs 0 = Z0 ∧ ∀ k, k < n → KernSchritt P O passes kern H (zs k) (fs k) (zs (k + 1))

/-- The start: the machine `M0`, a mask state consistent with it, no thread begun. -/
def KernStart (kern : Faden → Nat) (M0 : RufMaschineG D) (Z0 : KernZ D) : Prop :=
  Z0.m = M0 ∧ MaskeOk kern M0 Z0.mask ∧ ∀ g, ¬ Z0.begonnen g

/-- The guarded successor of `Z` when thread `f` steps to the machine `M'`. -/
def KernZ.weiter (kern : Faden → Nat) (Z : KernZ D) (f : Faden) (M' : RufMaschineG D) : KernZ D :=
  ⟨M', maskeNach kern Z.mask f (M'.faeden f).spur, fun g => g = f ∨ Z.begonnen g⟩

/-- A G step is a guarded step to `Z.weiter` as soon as the two guards hold. -/
theorem kernSchritt_weiter {P : Programm D} {O : Orakel D} {passes : Nat} {kern : Faden → Nat}
    {H : Faden → Prop} {Z : KernZ D} {f : Faden} {M' : RufMaschineG D}
    (hs : RufSchrittG P O passes Z.m f M') (he : H f → ¬ Z.begonnen f → Z.mask (kern f) = [])
    (hv : ∀ g, H g → Z.begonnen g → ¬ FertigG Z.m g → kern g = kern f → g = f) :
    KernSchritt P O passes kern H Z f (Z.weiter kern f M') :=
  ⟨hs, he, hv, rfl, rfl⟩

variable {P : Programm D} {O : Orakel D} {passes : Nat} {kern : Faden → Nat}
  {H : Faden → Prop} {M0 : RufMaschineG D} {Z0 : KernZ D} {zs : Nat → KernZ D}
  {fs : Nat → Faden} {n : Nat}

/-- **A guarded run is a G run**: every statement about G runs (all legs of `Ziel`) holds on it. -/
theorem kernLauf_laufG (h0 : KernStart kern M0 Z0) (hl : KernLauf P O passes kern H Z0 zs fs n) :
    LaufG P O passes M0 (fun k => (zs k).m) fs n :=
  ⟨by show (zs 0).m = M0; rw [hl.1]; exact h0.1, fun k hk => (hl.2 k hk).schritt⟩

/-- The mask state stays consistent along a guarded run. -/
theorem kernLauf_maskeOk (h0 : KernStart kern M0 Z0)
    (hl : KernLauf P O passes kern H Z0 zs fs n) :
    ∀ k, k ≤ n → MaskeOk kern (zs k).m (zs k).mask
  | 0, _ => by rw [hl.1, h0.1]; exact h0.2.1
  | k + 1, hk => by
      have hs := hl.2 k (by omega)
      rw [hs.maske]
      exact maskeOk_schritt hs.schritt (kernLauf_maskeOk h0 hl k (by omega))

/-- The threads that have begun are exactly the actors so far. -/
theorem kernLauf_begonnen (h0 : KernStart kern M0 Z0)
    (hl : KernLauf P O passes kern H Z0 zs fs n) :
    ∀ k, k ≤ n → ∀ g, (zs k).begonnen g ↔ ∃ i, i < k ∧ fs i = g
  | 0, _, g => by
      rw [hl.1]
      exact ⟨fun h => absurd h (h0.2.2 g), fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, hk, g => by
      have hs := hl.2 k (by omega)
      have e : (zs (k + 1)).begonnen g = (g = fs k ∨ (zs k).begonnen g) :=
        congrFun hs.begonnen g
      rw [e, kernLauf_begonnen h0 hl k (by omega) g]
      constructor
      · rintro (h | ⟨i, hi, hig⟩)
        · exact ⟨k, by omega, h.symm⟩
        · exact ⟨i, by omega, hig⟩
      · rintro ⟨i, hi, hig⟩
        by_cases hik : i = k
        · subst hik
          exact Or.inl hig.symm
        · exact Or.inr ⟨i, by omega, hig⟩

/-- **THE CORE SCHEDULE IS DERIVED, NOT ASSUMED**: every guarded run meets `KernPlan`. Its first
    clause is the entry guard plus the consistency of the mask state; its second is the
    run-to-completion guard plus "a finished thread stays finished". -/
theorem kernPlan_aus_lauf (h0 : KernStart kern M0 Z0)
    (hl : KernLauf P O passes kern H Z0 zs fs n) :
    KernPlan kern H (fun k => (zs k).m) fs n := by
  have hmo := kernLauf_maskeOk h0 hl
  have hbg := kernLauf_begonnen h0 hl
  have hG := kernLauf_laufG h0 hl
  constructor
  · intro i hi hH hmin f L hne hk hL
    have hs := hl.2 i hi
    have hnb : ¬ (zs i).begonnen (fs i) := by
      rw [hbg i (Nat.le_of_lt hi)]
      rintro ⟨j, hj, hjf⟩
      exact hmin j hj hjf
    have hleer := hs.eintritt hH hnb
    cases hm : D.maskiert L with
    | false => rfl
    | true =>
        have hin := (hmo i (Nat.le_of_lt hi) (kern f) f L).2 ⟨rfl, hm, hL⟩
        rw [hk, hleer] at hin
        exact absurd hin List.not_mem_nil
  · intro g i j k hHg hig hmin hik hkj hjn hnf hkern
    by_cases hki : k = i
    · rw [hki]
      exact hig
    · have hs := hl.2 k (by omega)
      have hb : (zs k).begonnen g := by
        rw [hbg k (by omega)]
        exact ⟨i, by omega, hig⟩
      have hnfk : ¬ FertigG (zs k).m g := fun hF => hnf (fertig_lauf hG hF j (Nat.le_of_lt hkj) hjn)
      exact (hs.vollendung g hHg hb hnfk hkern.symm).symm

/-! ## 4. The sentence over the guarded machine -/

/-- **No same-core interrupt deadlock over the guarded machine** (the leg `KernHaltE`, with the
    schedule inside the machine and no `KernPlan` premise): on every guarded run from a start
    `Z0` of `M0`, a handler never stands at a lock another thread of its own core holds. -/
def KernHaltM (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (Z0 : KernZ D) (zs : Nat → KernZ D) (fs : Nat → Faden) (n : Nat),
    KernStart kern M0 Z0 → KernLauf P O passes kern (HandlerVon P M0) Z0 zs fs n →
    (zs n).m = M →
    ∀ (g f : Faden) (L : D.Lock), HandlerVon P M0 g → f ≠ g → kern f = kern g →
      AnSperre M g L → L ∉ offen ((M.faeden f).spur)

/-- **THE SENTENCE, FROM THE MODEL** (from (a) as `kernHaltE_aus`, with the schedule proved):
    the premises that remain are the closure and the lock discipline of the handlers. -/
theorem kernHaltM_aus [DecidableEq D.Fn] {fl : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fl) (hAbg : ∀ w, AbgK P fl (reachB P fl w))
    (hMask : MaskenDisziplin P fl) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D) :
    KernHaltM P O passes (RufStartG P sp init) M := by
  intro kern Z0 zs fs n h0 hl hM g f L hH hfg hk hA
  exact kernHaltE_aus hvoll hAbg hMask sp init M kern (fun k => (zs k).m) fs n
    (kernLauf_laufG h0 hl) hM (kernPlan_aus_lauf h0 hl) g f L hH hfg hk hA

/-! ## 5. Nothing changes for programs without handlers or without masking locks -/

/-- The mask state along a G run, by recursion: the transition of each step. -/
def maskLauf (kern : Faden → Nat) (ms : Nat → RufMaschineG D) (fs : Nat → Faden)
    (mk0 : MaskeKern D) : Nat → MaskeKern D
  | 0 => mk0
  | k + 1 => maskeNach kern (maskLauf kern ms fs mk0 k) (fs k) ((ms (k + 1)).faeden (fs k)).spur

/-- The begun set along a G run: the actors so far. -/
def begLauf (fs : Nat → Faden) : Nat → Faden → Prop
  | 0 => fun _ => False
  | k + 1 => fun g => g = fs k ∨ begLauf fs k g

/-- **EMBEDDING: with no handler every G run lifts to a guarded run, machine for machine.** The
    guards only bind handlers, so a unit with no `entry … via idt` keeps exactly its runs; the
    mask state is bookkeeping alongside. -/
theorem laufG_kernLauf (hH : ∀ g, ¬ H g) {ms : Nat → RufMaschineG D}
    (hl : LaufG P O passes M0 ms fs n) (mk0 : MaskeKern D) :
    ∃ zs : Nat → KernZ D,
      KernLauf P O passes kern H ⟨M0, mk0, fun _ => False⟩ zs fs n ∧
        ∀ k, k ≤ n → (zs k).m = ms k := by
  refine ⟨fun k => ⟨ms k, maskLauf kern ms fs mk0 k, begLauf fs k⟩, ⟨?_, fun k hk => ?_⟩,
    fun k _ => rfl⟩
  · show (⟨ms 0, mk0, fun _ => False⟩ : KernZ D) = _
    rw [hl.1]
  · exact ⟨hl.2 k hk, fun hf _ => absurd hf (hH _), fun g hg => absurd hg (hH g), rfl, rfl⟩

/-- **No masking lock: every core stays unmasked, on every guarded run.** So the entry guard is
    vacuous and a program with handlers but no `masks irqs` lock is restricted only by run to
    completion. -/
theorem kernLauf_ungemaskt (hmk : ∀ L : D.Lock, D.maskiert L = false) (h0 : KernStart kern M0 Z0)
    (hl : KernLauf P O passes kern H Z0 zs fs n) :
    ∀ k, k ≤ n → ∀ c, (zs k).mask c = [] :=
  fun k hk c => mask_leer_ohne hmk (kernLauf_maskeOk h0 hl k hk) c

#print axioms Gabbro.Grammatik.Zielsatz.fertig_kein_schritt
#print axioms Gabbro.Grammatik.Zielsatz.fertig_lauf
#print axioms Gabbro.Grammatik.Zielsatz.maskeOk_schritt
#print axioms Gabbro.Grammatik.Zielsatz.maske_nichtleer_iff
#print axioms Gabbro.Grammatik.Zielsatz.kernLauf_laufG
#print axioms Gabbro.Grammatik.Zielsatz.kernPlan_aus_lauf
#print axioms Gabbro.Grammatik.Zielsatz.kernHaltM_aus
#print axioms Gabbro.Grammatik.Zielsatz.laufG_kernLauf
#print axioms Gabbro.Grammatik.Zielsatz.kernLauf_ungemaskt

end Gabbro.Grammatik.Zielsatz
