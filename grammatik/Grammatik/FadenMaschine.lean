/-
  File:      Grammatik/FadenMaschine.lean
  Subject:   THREADS CREATED AT RUN TIME (Opus agent A, 2026-09-26; OFFEN O21, O22).

  Machine G (RufMaschineG.lean) fixes its thread population at the start: every thread is in
  its start frame from the first machine on. The language has two statements that create
  threads DURING a run:
  * the hosted `start { f, g };` (lane 253, checker rules `N458`-`N462`, fix lane F4): one new
    thread per root, and the starter WAITS until every root has finished (join);
  * the `child { … }` region of a stack gate (lane O-1, `N446`-`N452`, fix lane F3's
    `N456`/`N457`): the region runs on the handed stack as its OWN thread, entered holding no
    lock; the parent does not wait.
  This file is the machine that runs them. It EXTENDS machine G without touching it: a thread
  machine is a G machine plus the set of live threads, the join lists, and two ghost counters.

  * A thread that is not live is a DORMANT slot: it sits, untouched, in its start frame (the
    entry of its root) until a live thread spawns it. From then on it steps by machine G's own
    rules. No G rule changes, and no G rule is added.
  * `start` -- a live thread `p` that holds NO lock (the model side of `N461`) spawns a list
    `cs` of dormant slots at once and then waits for them: `p` takes no G step until every
    `c ∈ cs` is FINISHED (`FertigG`), and the `join` step ends the wait.
  * `kind` -- a live thread spawns ONE dormant slot and continues; nothing waits.
  * `rang`/`uhr` are ghost state: every spawned thread ranks one above its spawner, and the
    clock counts spawns. They exist for the proofs (a join chain climbs in rank, and ranks are
    bounded by the clock), not for the behaviour.

  THE BRIDGE (`fadenErreichbar_G`): every run of the thread machine is a machine-G run from the
  same start machine -- a spawn and a join do not move the G state, a live step IS a G step.
  So every theorem about G's reachable machines holds on every thread-machine run, and the
  converse embedding (`fadenErreichbar_von_G`: every G run is a thread-machine run in which
  every thread is live and nothing is spawned) makes the thread machine a CONSERVATIVE
  extension -- nothing proved about G is lost.

  WHAT THE SPAWN RULES OVER-APPROXIMATE, AND WHAT THEY FIX. A spawn may fire at ANY point of a
  live thread's run where the rule's side conditions hold (G has no statement for it: the
  exporter drops `start`/`child` from the body, lean_g.rs), so every real spawn time is among
  the modelled ones, and every interleaving after it. Fixed at the start machine, as for every
  G thread: the root's ARGUMENTS (`start` roots take none, `N458`; a `child` region reads its
  handed values, which is why the exporter carries only param-free roots) and the ghost ENTRY
  WORLD of the frame (`s0`, the logged `eintritt`): a dormant slot entered at a later spawn has
  its body run on the memory of that moment -- G reads shared memory at each step -- but its
  frame remembers the start world, exactly as a declared start that is scheduled late does.
-/
import Grammatik.Verklemmung

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The machine -/

/-- **A thread machine**: a G machine, the live threads, the join lists (`wartet p` = the roots
    `p` waits for; `[]` = not joining), and the ghost rank and clock. -/
structure FadenMaschine (D : Deklaration) where
  /-- The machine-G state, every slot included. -/
  m : RufMaschineG D
  /-- Which threads are live; `false` = a dormant slot. -/
  lebt : Faden → Bool
  /-- The roots a starter waits for (`[]`: it waits for nothing). -/
  wartet : Faden → List Faden
  /-- Ghost: a spawned thread ranks one above its spawner. -/
  rang : Faden → Nat
  /-- Ghost: the number of spawns so far. -/
  uhr : Nat

/-- **One step of the thread machine.**
    * `lauf` -- a live thread that joins nothing takes one machine-G step;
    * `start` -- a live thread that joins nothing and holds NO lock spawns the dormant slots
      `cs` and waits for them (`N461`: no `start` under a held context);
    * `kind` -- a live thread that joins nothing spawns one dormant slot and continues;
    * `join` -- a waiting starter whose roots are all finished stops waiting. -/
inductive FadenSchritt (P : Programm D) (O : Orakel D) (passes : Nat) :
    FadenMaschine D → FadenMaschine D → Prop where
  | lauf (K : FadenMaschine D) (f : Faden) (M' : RufMaschineG D)
      (hf : K.lebt f = true) (hw : K.wartet f = []) (hs : RufSchrittG P O passes K.m f M') :
      FadenSchritt P O passes K ⟨M', K.lebt, K.wartet, K.rang, K.uhr⟩
  | start (K : FadenMaschine D) (p : Faden) (cs : List Faden)
      (hp : K.lebt p = true) (hw : K.wartet p = [])
      (hfrei : offen (K.m.faeden p).spur = [])
      (hcs : ∀ c ∈ cs, K.lebt c = false) :
      FadenSchritt P O passes K
        ⟨K.m, fun t => if t ∈ cs then true else K.lebt t,
         fun t => if t = p then cs else K.wartet t,
         fun t => if t ∈ cs then K.rang p + 1 else K.rang t, K.uhr + 1⟩
  | kind (K : FadenMaschine D) (p c : Faden)
      (hp : K.lebt p = true) (hw : K.wartet p = []) (hc : K.lebt c = false) :
      FadenSchritt P O passes K
        ⟨K.m, fun t => if t = c then true else K.lebt t, K.wartet,
         fun t => if t = c then K.rang p + 1 else K.rang t, K.uhr + 1⟩
  | join (K : FadenMaschine D) (p : Faden)
      (hp : K.lebt p = true) (hw : K.wartet p ≠ [])
      (hf : ∀ u ∈ K.wartet p, FertigG K.m u) :
      FadenSchritt P O passes K
        ⟨K.m, K.lebt, fun t => if t = p then [] else K.wartet t, K.rang, K.uhr⟩

/-- Reachable thread machines. -/
inductive FadenErreichbar (P : Programm D) (O : Orakel D) (passes : Nat)
    (K0 : FadenMaschine D) : FadenMaschine D → Prop where
  | start : FadenErreichbar P O passes K0 K0
  | schritt (K K' : FadenMaschine D) (h : FadenErreichbar P O passes K0 K)
      (hs : FadenSchritt P O passes K K') : FadenErreichbar P O passes K0 K'

/-- **The start of the thread machine**: machine G's start from `init` (every slot placed at
    its root), the threads `lebt0` names live, nobody joining, every rank and the clock zero. -/
def FadenStart (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (lebt0 : Faden → Bool) : FadenMaschine D :=
  ⟨RufStartG P sp init, lebt0, fun _ => [], fun _ => 0, 0⟩

/-! ## 2. The bridge to machine G, both directions -/

/-- **Every thread-machine run is a machine-G run** from the same start machine. -/
theorem fadenErreichbar_G {P : Programm D} {O : Orakel D} {passes : Nat}
    {K0 K : FadenMaschine D} (h : FadenErreichbar P O passes K0 K) :
    RufErreichbarG P O passes K0.m K.m := by
  induction h with
  | start => exact RufErreichbarG.start
  | schritt K K' _ hs ih =>
      cases hs with
      | lauf f M' _ _ hs' => exact RufErreichbarG.schritt _ _ f ih hs'
      | start => exact ih
      | kind => exact ih
      | join => exact ih

/-- The thread machine over a G machine in which every thread is live and nothing joins. -/
def FadenMaschine.alleLebend (M : RufMaschineG D) : FadenMaschine D :=
  ⟨M, fun _ => true, fun _ => [], fun _ => 0, 0⟩

/-- **The embedding: every machine-G run is a thread-machine run** in which every thread is
    live from the start and nothing is spawned. The thread machine loses no G run. -/
theorem fadenErreichbar_von_G {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} (h : RufErreichbarG P O passes M0 M) :
    FadenErreichbar P O passes (FadenMaschine.alleLebend M0) (FadenMaschine.alleLebend M) := by
  induction h with
  | start => exact FadenErreichbar.start
  | schritt M M' f _ hs ih =>
      exact FadenErreichbar.schritt _ _ ih
        (FadenSchritt.lauf (FadenMaschine.alleLebend M) f M' rfl rfl hs)

/-- The all-live start IS `FadenStart` with every thread live. -/
theorem fadenStart_alleLebend (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    FadenStart P sp init (fun _ => true) = FadenMaschine.alleLebend (RufStartG P sp init) := rfl

/-! ## 3. The invariant -/

/-- **What every reachable thread machine satisfies.** -/
structure FadenInv (P : Programm D) (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D)
    (K : FadenMaschine D) : Prop where
  /-- The G state is G-reachable. -/
  lauf : RufErreichbarG P O passes M0 K.m
  /-- A dormant slot is untouched: it is its start-machine thread. -/
  schlaeft : ∀ t, K.lebt t = false → K.m.faeden t = M0.faeden t
  /-- A joining starter holds no lock. -/
  joinFrei : ∀ t, K.wartet t ≠ [] → offen (K.m.faeden t).spur = []
  /-- A joining starter is live. -/
  joinLebt : ∀ t, K.wartet t ≠ [] → K.lebt t = true
  /-- Every awaited root is live. -/
  kindLebt : ∀ t u, u ∈ K.wartet t → K.lebt u = true
  /-- An awaited root ranks above its starter. -/
  rangSteigt : ∀ t u, u ∈ K.wartet t → K.rang t < K.rang u
  /-- Ranks are bounded by the clock. -/
  rangUhr : ∀ t, K.rang t ≤ K.uhr

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem fadenInv_start (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (lebt0 : Faden → Bool) :
    FadenInv P O passes (RufStartG P sp init) (FadenStart P sp init lebt0) where
  lauf := RufErreichbarG.start
  schlaeft _ _ := rfl
  joinFrei _ h := absurd rfl h
  joinLebt _ h := absurd rfl h
  kindLebt _ _ h := absurd h List.not_mem_nil
  rangSteigt _ _ h := absurd h List.not_mem_nil
  rangUhr _ := Nat.le_refl 0

theorem fadenInv_schritt {M0 : RufMaschineG D} {K K' : FadenMaschine D}
    (hI : FadenInv P O passes M0 K) (hs : FadenSchritt P O passes K K') :
    FadenInv P O passes M0 K' := by
  cases hs with
  | lauf f M' hf hw hs' =>
      refine ⟨RufErreichbarG.schritt _ _ f hI.lauf hs', fun t ht => ?_, fun t ht => ?_,
        hI.joinLebt, hI.kindLebt, hI.rangSteigt, hI.rangUhr⟩
      · have hne : t ≠ f := by intro e; subst e; simp_all
        rw [rufSchrittG_passt_anders P O passes K.m M' f t hne hs']
        exact hI.schlaeft t ht
      · have hne : t ≠ f := by intro e; subst e; exact ht hw
        rw [rufSchrittG_passt_anders P O passes K.m M' f t hne hs']
        exact hI.joinFrei t ht
  | start p cs hp hw hfrei hcs =>
      have hpcs : p ∉ cs := fun h => by simp [hcs p h] at hp
      -- a live thread is no spawned slot
      have hlebt_nicht : ∀ t, K.lebt t = true → t ∉ cs := fun t ht h => by
        simp [hcs t h] at ht
      refine ⟨hI.lauf, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t u hu => ?_,
        fun t u hu => ?_, fun t => ?_⟩
      · by_cases hc : t ∈ cs
        · simp [hc] at ht
        · simp only [hc, if_false] at ht
          exact hI.schlaeft t ht
      · by_cases htp : t = p
        · subst htp; exact hfrei
        · simp only [htp, if_false] at ht
          exact hI.joinFrei t ht
      · by_cases hc : t ∈ cs
        · simp [hc]
        · simp only [hc, if_false]
          by_cases htp : t = p
          · subst htp; exact hp
          · simp only [htp, if_false] at ht
            exact hI.joinLebt t ht
      · show (if u ∈ cs then true else K.lebt u) = true
        by_cases htp : t = p
        · subst htp
          simp only [if_true] at hu
          simp [hu]
        · simp only [htp, if_false] at hu
          have := hI.kindLebt t u hu
          simp [this]
      · show (if t ∈ cs then K.rang p + 1 else K.rang t) <
          (if u ∈ cs then K.rang p + 1 else K.rang u)
        by_cases htp : t = p
        · subst htp
          simp only [if_true] at hu
          simp [hpcs, hu]
        · simp only [htp, if_false] at hu
          have hu' := hlebt_nicht u (hI.kindLebt t u hu)
          have ht' := hlebt_nicht t (hI.joinLebt t (List.ne_nil_of_mem hu))
          simp only [hu', ht', if_false]
          exact hI.rangSteigt t u hu
      · show (if t ∈ cs then K.rang p + 1 else K.rang t) ≤ K.uhr + 1
        by_cases hc : t ∈ cs
        · simp only [hc, if_true]
          exact Nat.succ_le_succ (hI.rangUhr p)
        · simp only [hc, if_false]
          exact Nat.le_succ_of_le (hI.rangUhr t)
  | kind p c hp hw hc =>
      have hlebt_nicht : ∀ t, K.lebt t = true → t ≠ c := fun t ht h => by
        subst h; simp [hc] at ht
      refine ⟨hI.lauf, fun t ht => ?_, hI.joinFrei, fun t ht => ?_, fun t u hu => ?_,
        fun t u hu => ?_, fun t => ?_⟩
      · by_cases htc : t = c
        · simp [htc] at ht
        · simp only [htc, if_false] at ht
          exact hI.schlaeft t ht
      · show (if t = c then true else K.lebt t) = true
        simp [hI.joinLebt t ht]
      · show (if u = c then true else K.lebt u) = true
        simp [hI.kindLebt t u hu]
      · show (if t = c then K.rang p + 1 else K.rang t) <
          (if u = c then K.rang p + 1 else K.rang u)
        have hu' := hlebt_nicht u (hI.kindLebt t u hu)
        have ht' := hlebt_nicht t (hI.joinLebt t (List.ne_nil_of_mem hu))
        simp only [hu', ht', if_false]
        exact hI.rangSteigt t u hu
      · show (if t = c then K.rang p + 1 else K.rang t) ≤ K.uhr + 1
        by_cases htc : t = c
        · simp only [htc, if_true]
          exact Nat.succ_le_succ (hI.rangUhr p)
        · simp only [htc, if_false]
          exact Nat.le_succ_of_le (hI.rangUhr t)
  | join p hp hw hf =>
      refine ⟨hI.lauf, hI.schlaeft, fun t ht => ?_, fun t ht => ?_, fun t u hu => ?_,
        fun t u hu => ?_, hI.rangUhr⟩
      · by_cases htp : t = p
        · subst htp; simp at ht
        · simp only [htp, if_false] at ht
          exact hI.joinFrei t ht
      · by_cases htp : t = p
        · subst htp; simp at ht
        · simp only [htp, if_false] at ht
          exact hI.joinLebt t ht
      · by_cases htp : t = p
        · subst htp; simp at hu
        · simp only [htp, if_false] at hu
          exact hI.kindLebt t u hu
      · by_cases htp : t = p
        · subst htp; simp at hu
        · simp only [htp, if_false] at hu
          exact hI.rangSteigt t u hu

/-- **The invariant on every reachable thread machine.** -/
theorem fadenInv_erreichbar {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {lebt0 : Faden → Bool} {K : FadenMaschine D}
    (h : FadenErreichbar P O passes (FadenStart P sp init lebt0) K) :
    FadenInv P O passes (RufStartG P sp init) K := by
  induction h with
  | start => exact fadenInv_start sp init lebt0
  | schritt K K' _ hs ih => exact fadenInv_schritt ih hs

/-- Liveness only grows. -/
theorem faden_lebt_bleibt {K0 K : FadenMaschine D} (h : FadenErreichbar P O passes K0 K)
    (t : Faden) (ht : K0.lebt t = true) : K.lebt t = true := by
  induction h with
  | start => exact ht
  | schritt K K' _ hs ih =>
      cases hs with
      | lauf => exact ih
      | start p cs _ _ _ _ =>
          show (if t ∈ cs then true else K.lebt t) = true
          simp [ih]
      | kind p c _ _ _ =>
          show (if t = c then true else K.lebt t) = true
          simp [ih]
      | join => exact ih

/-- **A dormant slot holds nothing** when its root holds nothing by signature (the model side of
    `N456`: a spawned thread enters its root holding no lock, whatever its spawner holds). -/
theorem faden_schlafend_frei {M0 : RufMaschineG D} {K : FadenMaschine D}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hM0 : M0 = RufStartG P sp init) (hI : FadenInv P O passes M0 K) (t : Faden)
    (ht : K.lebt t = false) (hsig : D.haelt (init t).1 = []) :
    offen (K.m.faeden t).spur = [] := by
  rw [hI.schlaeft t ht, hM0]
  have hsp : ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
    simp only [RufStartG]
  rw [hsp]
  refine List.eq_nil_iff_forall_not_mem.mpr fun L hL => ?_
  rw [offen_startSpur, hsig] at hL
  exact List.not_mem_nil hL

end Inv

#print axioms Gabbro.Grammatik.fadenErreichbar_G
#print axioms Gabbro.Grammatik.fadenErreichbar_von_G
#print axioms Gabbro.Grammatik.fadenStart_alleLebend
#print axioms Gabbro.Grammatik.fadenInv_start
#print axioms Gabbro.Grammatik.fadenInv_schritt
#print axioms Gabbro.Grammatik.fadenInv_erreichbar
#print axioms Gabbro.Grammatik.faden_lebt_bleibt
#print axioms Gabbro.Grammatik.faden_schlafend_frei

end Gabbro.Grammatik
