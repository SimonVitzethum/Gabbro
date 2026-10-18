/-
  File:      Grammatik/Zielsatz/Eigenschaften/RwSchritt.lean
  Subject:   THE READER/WRITER LOCK, STEP ONE (Simon's decision, 2026-10-18): the layer `RwSchritt`
             over machine G, its embedding of G, the proof that a program with no shared acquisition
             keeps exactly its runs, and the exclusion invariant "many readers XOR one writer".

  WHY A LAYER. `Stmt.locks`, `Res.held`, the events `nimmt`/`gibt` and `RufFreiG` carry no mode:
  every holding is exclusive. A mode in the statement forms is a root change of `Kern/Syntax` (714
  modules) and of every proof about `offen`. The mask state (`KernMaske.lean`) showed the other
  way: a layer that lives over the existing types, with its own step relation, proved to embed
  machine G. The reader/writer lock lives in the same place. The proposal for the final form (the
  mode inside `Stmt.locks`/`Res.held`, the spelling, the `Spec.lean` diff) is in
  dokumente/PLAN-DYNAMISCH.md, section 8a.5; nothing in `Zielsatz/Kern/` changes here.

  THE DESIGN (the smallest sound one).
  * `lese : Faden → D.Lock → Prop` -- the layer parameter: thread `t` takes lock `L` SHARED (as a
    reader). Every other acquisition is exclusive (as a writer). One mode per (thread, lock): a
    thread that takes `L` shared never takes it exclusively. (In the final language the mode is a
    property of the acquisition site; this restriction is the layer's, and it is named.)
  * An acquisition is still the event `nimmt L` and a held lock is still an entry of `offen`, so
    rank order (`hr`, `hrang`), release (`freiGib`, the peels), the trace and the call log are
    machine G's, unchanged.
  * `RwSchritt`: a step of machine G (exclusive acquisition keeps `RufFreiG`: NO other thread
    holds the lock, a reader included), or a SHARED ACQUISITION `RwAcq`: the acting thread is a
    reader of `L`, and every other thread that holds `L` is a reader of `L` too. Its content is
    machine G's own `dannLocks` step: `RwAcq` is the G step of the acting thread in the machine
    `ohneFremde`, in which the other threads' traces are blank (so `RufFreiG` holds there), and
    the result keeps the other threads as they are. Nothing about the acquisition is restated.
  * `RwExkl`: whenever two different threads hold `L`, both are readers of `L`. So a writer
    holds `L` alone, and readers share it only with readers (`rwExkl_lauf`, along every run).

  PROVED HERE (every theorem: `propext`, `Classical.choice`, `Quot.sound` at most).
  * `rwSchritt_of_G`, `rwLauf_of_laufG`: every G step and every G run is a layer step and run.
  * `rwSchritt_ohne_leser`, `rwLauf_ohne_leser`: with no reader (`fun _ _ => False`) the layer's step
    IS machine G's step, and its runs ARE `LaufG`: a program that never takes a lock shared keeps
    exactly the meaning it had. `rwExkl_ohne_leser` is then the old exclusivity of G.
  * `rw_nimmt`: the acquisition lemma of the layer: a lock that enters the acting thread's held
    set was free (G) or was held only by readers while the actor is a reader (shared).
  * `rwExkl_schritt`, `rwExkl_lauf`: the exclusion invariant, from the start.

  NOT CLAIMED: the mode is not in the statement forms (the layer parameter stands in for it); no
  Rust, no `SYNTAX.md`; `Spec.lean`/`gabbro_ziel` are untouched.
-/
import Grammatik.Zielsatz.Eigenschaften.KernMaske
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T2
import Grammatik.Logik.Fortschritt.Lebendigkeit.T1

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The layer: modes, the blank machine, the shared acquisition -/

/-- **Who reads.** `lese t L`: thread `t` takes lock `L` shared; every other acquisition is exclusive. -/
abbrev Lese (D : Deklaration) := Faden → D.Lock → Prop

/-- **The machine as the acting thread `f` sees an acquisition**: `f` unchanged, every other thread's
    trace blank, so no other thread holds anything. Only `f`'s own record and the shared memory are
    read by a step of `f` except at the exclusive acquisition's freedom test. -/
def ohneFremde (M : RufMaschineG D) (f : Faden) : RufMaschineG D :=
  { M with faeden := fun g => if g = f then M.faeden f else { M.faeden g with spur := [] } }

theorem ohneFremde_self (M : RufMaschineG D) (f : Faden) : (ohneFremde M f).faeden f = M.faeden f := by
  simp [ohneFremde]

theorem ohneFremde_speicher (M : RufMaschineG D) (f : Faden) : (ohneFremde M f).speicher = M.speicher := rfl

theorem ohneFremde_frei (M : RufMaschineG D) (f : Faden) (L : D.Lock) : RufFreiG (ohneFremde M f) f L := by
  intro g hg
  have : (ohneFremde M f).faeden g = { M.faeden g with spur := [] } := by simp [ohneFremde, hg]
  rw [this]
  exact List.not_mem_nil

/-- **A SHARED ACQUISITION of `L` by `f`**: `f` is a reader of `L`; every other thread holding `L` is a
    reader of `L`; `f` did not hold `L` and holds it after; and the step is machine G's own step of
    `f` in the blank machine (it is the `dannLocks` step: `f` stands at `locks L`, the rank
    premises are G's), the other threads kept as they are. -/
structure RwAcq (P : Programm D) (O : Orakel D) (passes : Nat) (lese : Lese D)
    (M : RufMaschineG D) (f : Faden) (L : D.Lock) (M' : RufMaschineG D) : Prop where
  leser : lese f L
  andere : ∀ g, g ≠ f → L ∈ offen (M.faeden g).spur → lese g L
  neu : L ∉ offen (M.faeden f).spur ∧ L ∈ offen (M'.faeden f).spur
  schritt : ∃ Mh : RufMaschineG D, RufSchrittG P O passes (ohneFremde M f) f Mh ∧
    M' = { Mh with faeden := rufUpdateG M.faeden f (Mh.faeden f) }

/-- **One step of the layer**: a step of machine G, or a shared acquisition. -/
def RwSchritt (P : Programm D) (O : Orakel D) (passes : Nat) (lese : Lese D)
    (M : RufMaschineG D) (f : Faden) (M' : RufMaschineG D) : Prop :=
  RufSchrittG P O passes M f M' ∨ ∃ L, RwAcq P O passes lese M f L M'

/-- A run of `n` layer steps, by index. -/
def RwLauf (P : Programm D) (O : Orakel D) (passes : Nat) (lese : Lese D) (M0 : RufMaschineG D)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat) : Prop :=
  ms 0 = M0 ∧ ∀ k, k < n → RwSchritt P O passes lese (ms k) (fs k) (ms (k + 1))

variable {P : Programm D} {O : Orakel D} {passes : Nat} {lese : Lese D}

/-! ## 2. Embedding, and no change without a reader -/

theorem rwSchritt_of_G {M M' : RufMaschineG D} {f : Faden} (h : RufSchrittG P O passes M f M') :
    RwSchritt P O passes lese M f M' := Or.inl h

theorem rwLauf_of_laufG {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (h : LaufG P O passes M0 ms fs n) : RwLauf P O passes lese M0 ms fs n :=
  ⟨h.1, fun k hk => Or.inl (h.2 k hk)⟩

/-- **No reader, no change**: with `lese` empty the layer's step is machine G's step. -/
theorem rwSchritt_ohne_leser {M M' : RufMaschineG D} {f : Faden} :
    RwSchritt P O passes (fun _ _ => False) M f M' ↔ RufSchrittG P O passes M f M' := by
  constructor
  · rintro (h | ⟨L, h⟩)
    · exact h
    · exact h.leser.elim
  · exact Or.inl

/-- **A program that takes no lock shared keeps exactly its runs.** -/
theorem rwLauf_ohne_leser {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden}
    {n : Nat} : RwLauf P O passes (fun _ _ => False) M0 ms fs n ↔ LaufG P O passes M0 ms fs n :=
  ⟨fun h => ⟨h.1, fun k hk => rwSchritt_ohne_leser.mp (h.2 k hk)⟩,
   fun h => ⟨h.1, fun k hk => rwSchritt_ohne_leser.mpr (h.2 k hk)⟩⟩

/-! ## 3. What one layer step does -/

/-- **Every layer step is a G step of the acting thread**, in a machine that agrees with `M` on the
    acting thread and on the memory, with the result agreeing with `M'` on both. This is how every
    statement about the acting thread's own record transfers to the layer. -/
theorem rwSchritt_akteur {M M' : RufMaschineG D} {f : Faden} (h : RwSchritt P O passes lese M f M') :
    ∃ Mh Mh' : RufMaschineG D, RufSchrittG P O passes Mh f Mh' ∧ Mh.faeden f = M.faeden f ∧
      Mh.speicher = M.speicher ∧ Mh'.faeden f = M'.faeden f ∧ Mh'.speicher = M'.speicher := by
  rcases h with h | ⟨L, h⟩
  · exact ⟨M, M', h, rfl, rfl, rfl, rfl⟩
  · obtain ⟨Mh', hs, rfl⟩ := h.schritt
    exact ⟨ohneFremde M f, Mh', hs, ohneFremde_self M f, rfl, (rufUpdateG_self _ _ _).symm, rfl⟩

/-- A layer step leaves every other thread untouched. -/
theorem rwSchritt_fremd {M M' : RufMaschineG D} {f : Faden} (h : RwSchritt P O passes lese M f M')
    (g : Faden) (hg : g ≠ f) : M'.faeden g = M.faeden g := by
  rcases h with h | ⟨L, h⟩
  · exact rufSchrittG_fremd h g hg
  · obtain ⟨Mh', _, rfl⟩ := h.schritt
    exact rufUpdateG_noteq _ _ _ hg _

/-- **The trace delta of a layer step** (`schritt_delta`, over the layer). -/
theorem rwSchritt_delta (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (h : RwSchritt P O passes lese M f M') :
    ZugriffsDelta (M.faeden f).spur (M'.faeden f).spur ∨
      (SperrDelta (M.faeden f).spur (M'.faeden f).spur ∧ M'.speicher = M.speicher) := by
  obtain ⟨Mh, Mh', hs, h1, h2, h3, h4⟩ := rwSchritt_akteur h
  have := schritt_delta hO hs
  rw [h1, h3, h2, h4] at this
  exact this

/-- A shared acquisition touches no memory. -/
theorem rwAcq_speicher (hO : GutO O) {M M' : RufMaschineG D} {f : Faden} {L : D.Lock}
    (h : RwAcq P O passes lese M f L M') : M'.speicher = M.speicher := by
  rcases rwSchritt_delta hO (Or.inr ⟨L, h⟩) with ⟨X, _, _, _, _, hoff⟩ | ⟨_, hsp⟩
  · exact absurd (by have := h.neu.2; rw [hoff] at this; exact this) h.neu.1
  · exact hsp

/-- **The acquisition lemma of the layer.** A lock that enters the acting thread's held set was
    free (exclusive acquisition, and the machine-G rule), or the actor is a reader of it and every
    other holder is a reader of it. -/
theorem rw_nimmt (hO : GutO O) {M M' : RufMaschineG D} {f : Faden} {L : D.Lock}
    (h : RwSchritt P O passes lese M f M') (h0 : L ∉ offen (M.faeden f).spur)
    (h1 : L ∈ offen (M'.faeden f).spur) :
    RufFreiG M f L ∨ (lese f L ∧ ∀ g, g ≠ f → L ∈ offen (M.faeden g).spur → lese g L) := by
  rcases h with h | ⟨K, hK⟩
  · exact Or.inl (sperre_schritt (nimmt_an_sperre hO h h0 h1) h).1
  · obtain ⟨Mh, hs, hM⟩ := hK.schritt
    have hMf : M'.faeden f = Mh.faeden f := by subst hM; exact rufUpdateG_self _ _ _
    have h0' : L ∉ offen ((ohneFremde M f).faeden f).spur := by rw [ohneFremde_self]; exact h0
    have hK0' : K ∉ offen ((ohneFremde M f).faeden f).spur := by
      rw [ohneFremde_self]; exact hK.neu.1
    have hAL := nimmt_an_sperre hO hs h0' (by rw [← hMf]; exact h1)
    have hAK := nimmt_an_sperre hO hs hK0' (by rw [← hMf]; exact hK.neu.2)
    have eL := (sperre_schritt hAL hs).2
    have eK := (sperre_schritt hAK hs).2
    have hKL : K = L := by
      have := eK.symm.trans eL
      exact (Ereignis.nimmt.inj (List.cons.inj this).1).1
    subst hKL
    exact Or.inr ⟨hK.leser, hK.andere⟩

/-! ## 4. The exclusion invariant: many readers XOR one writer -/

/-- **Exclusion**: whenever two different threads hold `L`, both are readers of `L`. A thread that holds
    `L` and is not a reader of it (a writer) holds it alone. -/
def RwExkl (lese : Lese D) (M : RufMaschineG D) : Prop :=
  ∀ (t u : Faden) (L : D.Lock), t ≠ u → L ∈ offen (M.faeden t).spur → L ∈ offen (M.faeden u).spur →
    lese t L ∧ lese u L

theorem rwExkl_schritt (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (h : RwSchritt P O passes lese M f M') (hx : RwExkl lese M) : RwExkl lese M' := by
  -- the acting thread's side: a lock it holds after the step, against another holder
  have key : ∀ (g : Faden) (L : D.Lock), g ≠ f → L ∈ offen (M'.faeden f).spur →
      L ∈ offen (M'.faeden g).spur → lese f L ∧ lese g L := by
    intro g L hg hf hgL
    rw [rwSchritt_fremd h g hg] at hgL
    by_cases hold : L ∈ offen (M.faeden f).spur
    · exact hx f g L (Ne.symm hg) hold hgL
    · rcases rw_nimmt hO h hold hf with hfrei | ⟨hl, hall⟩
      · exact absurd hgL (hfrei g hg)
      · exact ⟨hl, hall g hg hgL⟩
  intro t u L htu ht hu
  by_cases htf : t = f
  · subst htf
    exact key u L (Ne.symm htu) ht hu
  · by_cases huf : u = f
    · subst huf
      exact (key t L htu hu ht).symm
    · rw [rwSchritt_fremd h t htf] at ht
      rw [rwSchritt_fremd h u huf] at hu
      exact hx t u L htu ht hu

theorem rwExkl_lauf (hO : GutO O) {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D}
    {fs : Nat → Faden} {n : Nat} (hl : RwLauf P O passes lese M0 ms fs n) (h0 : RwExkl lese M0) :
    ∀ k, k ≤ n → RwExkl lese (ms k)
  | 0, _ => by rw [hl.1]; exact h0
  | k + 1, hk => rwExkl_schritt hO (hl.2 k (by omega)) (rwExkl_lauf hO hl h0 k (by omega))

/-- With no reader the invariant is machine G's old exclusivity: no lock is held by two threads. -/
theorem rwExkl_ohne_leser {M : RufMaschineG D} :
    RwExkl (fun _ _ => False) M ↔
      ∀ (t u : Faden) (L : D.Lock), t ≠ u → L ∈ offen (M.faeden t).spur → L ∉ offen (M.faeden u).spur := by
  constructor
  · intro h t u L htu ht hu
    exact (h t u L htu ht hu).1
  · intro h t u L htu ht hu
    exact absurd hu (h t u L htu ht)

/-- A writer holds the lock alone. -/
theorem rw_schreiber_allein {M : RufMaschineG D} (hx : RwExkl lese M) {t : Faden} {L : D.Lock}
    (ht : L ∈ offen (M.faeden t).spur) (hw : ¬ lese t L) (u : Faden) (hu : u ≠ t) :
    L ∉ offen (M.faeden u).spur :=
  fun h => hw (hx t u L (Ne.symm hu) ht h).1

/-- Readers hold the lock only among readers. -/
theorem rw_leser_unter_sich {M : RufMaschineG D} (hx : RwExkl lese M) {t u : Faden} {L : D.Lock}
    (htu : t ≠ u) (ht : L ∈ offen (M.faeden t).spur) (hu : L ∈ offen (M.faeden u).spur) :
    lese t L ∧ lese u L := hx t u L htu ht hu

/-- The exclusion invariant of the start machine, from G's start exclusivity (no two threads hold a
    common signature lock). -/
theorem rwExkl_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init) :
    RwExkl lese (RufStartG P sp init) := by
  intro t u L htu ht hu
  exact absurd ((offen_start sp init u L).mp hu) (hex t u htu L ((offen_start sp init t L).mp ht))

/-! ## 5. Building runs -/

theorem rwLauf_nil (M0 : RufMaschineG D) : RwLauf P O passes lese M0 (fun _ => M0) (fun _ => 0) 0 :=
  ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

/-- One more step at the end of a run (the witnesses build their runs with this). The earlier
    machines and actors are kept; the new actor is `f`. -/
theorem rwLauf_schritt {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden}
    {n : Nat} (hl : RwLauf P O passes lese M0 ms fs n) {M M' : RufMaschineG D} {f : Faden}
    (hm : ms n = M) (hs : RwSchritt P O passes lese M f M') :
    ∃ (ms' : Nat → RufMaschineG D) (fs' : Nat → Faden),
      RwLauf P O passes lese M0 ms' fs' (n + 1) ∧ ms' (n + 1) = M' ∧ (∀ k, k ≤ n → ms' k = ms k) ∧
        fs' n = f ∧ (∀ k, k < n → fs' k = fs k) := by
  refine ⟨fun k => if k ≤ n then ms k else M', fun k => if k < n then fs k else f, ⟨?_, ?_⟩, ?_, ?_,
    ?_, ?_⟩
  · simp only [Nat.zero_le, if_true]; exact hl.1
  · intro k hk
    by_cases hkn : k < n
    · have h1 : k ≤ n := by omega
      have h2 : k + 1 ≤ n := by omega
      simp only [h1, h2, hkn, if_true]
      exact hl.2 k hkn
    · have hk' : k = n := by omega
      subst hk'
      have h2 : ¬ k + 1 ≤ k := by omega
      simp only [Nat.le_refl, if_true, h2, hkn, if_false]
      rw [hm]
      exact hs
  · have : ¬ n + 1 ≤ n := by omega
    simp [this]
  · intro k hk
    simp [hk]
  · simp
  · intro k hk
    simp [hk]

end Gabbro.Grammatik.Zielsatz

#print axioms Gabbro.Grammatik.Zielsatz.rwExkl_lauf
#print axioms Gabbro.Grammatik.Zielsatz.rw_nimmt
#print axioms Gabbro.Grammatik.Zielsatz.rwAcq_speicher
