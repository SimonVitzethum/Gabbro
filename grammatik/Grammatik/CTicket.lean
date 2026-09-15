/-
  File:      Grammatik/CTicket.lean
  Subject:   THE RUNTIME'S TICKET LOCK, AS THE RUNTIME WRITES IT, AND THE
             PREMISE IT DISCHARGES (plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`
             §7.6 item 3): `L_nimm`/`L_gib` are a ticket lock over two
             counters; every one of its steps is a step of `sperrAbstrakt`
             (`ticketLP_sperrAbstrakt`), so the clause "the lock primitive
             behaves as `sperrAbstrakt`" of `LaufzeitC` is no longer assumed
             for it but PROVED -- and the two places where the concrete lock
             says MORE or LESS than the specification are named and witnessed
             (`ticket_mehr_als_frei`, `gib_ohne_wache`).

  THE C THE RUNTIME IMPLEMENTS (the emitter writes only the two prototypes,
  `emit.rs` `ItemArt::Lock`: "the primitive itself is trust base, not
  product"; this is the body the trust base supplies):

      typedef struct { _Atomic unsigned next; _Atomic unsigned now; } L_wort;
      static L_wort L;

      void L_nimm(void) {
          unsigned my = atomic_fetch_add_explicit(&L.next, 1u,
                                                  memory_order_relaxed);
          while (atomic_load_explicit(&L.now, memory_order_acquire) != my)
              ;                                     /* spin */
      }

      void L_gib(void) {
          unsigned n = atomic_load_explicit(&L.now, memory_order_relaxed);
          atomic_store_explicit(&L.now, n + 1u, memory_order_release);
      }

  FOUR INSTRUCTIONS, FOUR RULES (`TSchritt`), one step each -- this is the
  granularity the implementation has, and it is FINER than the one step per
  `L_nimm()` call of `CNebenlaeufig.lean`:
    * `zieht` -- the `fetch_add`: the caller draws a ticket and `next` grows;
    * `dreht` -- a spin load that finds `now != my`: NOTHING changes (this is
      the step at which a waiting thread is not blocked but busy);
    * `tritt` -- the spin load that finds `now == my`: `L_nimm` RETURNS, and
      this is the one instruction at which the caller becomes the holder;
    * `gibt` -- the release store: `now` grows by one and the caller is no
      longer the holder.
  `zieht`/`tritt` carry the thread's own `my` (`TZust.zieht`: the local of
  `L_nimm`, live only between the two), `tritt`/`gibt` its position between
  the return of `L_nimm` and the call of `L_gib` (`TZust.haelt`: the caller's
  program counter, not a word of the lock).

  WHAT IS PROVED
    * `tinv_schritt` -- the invariant (`TInv`) survives every instruction:
      drawn tickets are distinct and lie in `[now, next)`, and while somebody
      holds `L` every drawn ticket is strictly above `now`.
    * `ticket_ausschluss`, `erreichbarT_exklusiv` -- MUTUAL EXCLUSION: two
      threads never hold one lock, on every reachable state.
    * `ticketLP_sperrAbstrakt` -- THE REFINEMENT: every abstract step the
      ticket lock induces is a `sperrAbstrakt` step. This is exactly the
      clause `LaufzeitC.sperre`, and it is now a theorem.
    * `schrittT_proj`, `erreichbarT_erreichbarC` -- the C program WITH the
      lock implementation inlined (`SchrittT`: the four instructions
      interleaved with the program's blocks) takes no configuration the
      abstract semantics does not take: a spin is a stutter, everything else
      is a step of `SchrittC E sperrAbstrakt`.
    * `ticket_frame` -- an instruction of the lock changes no program memory
      and no other lock's words.

  THE TWO FINDINGS, WITNESSED, NOT PATCHED AWAY (PLAN §7.6 item 3)
    * `ticket_mehr_als_frei` -- the concrete lock REVEALS MORE THAN HELD OR
      FREE. Two concrete states with the SAME abstract holder table (both
      free) and one thread that can complete its acquire in one and not in
      the other: the ticket order is visible to a waiting thread, and it is
      the arrival order of the OTHER threads. `sperrAbstrakt_nur_eigen` is a
      theorem about the SPECIFICATION and does not transfer to the
      implementation. For the safety statement of stage (b) this is
      harmless -- the refinement runs the other way, the concrete lock has
      FEWER runs -- but the entry of `NICHTINTERFERENZ.md` §10 must not be
      read as a statement about the ticket lock at this granularity.
    * `gib_ohne_wache` -- the release performs NO CHECK. `L_gib` increments
      `now` whoever calls it; the guard `L ∈ haelt t` of the rule `gibt` is
      supplied by the PROGRAM (the checker's lock discipline: a `L_gib()` is
      emitted only where the holder stands), not by the lock. A call from a
      non-holder does not fail -- it hands the lock to the next ticket while
      the holder is still inside, and two threads hold it. So the refinement
      of `.gib` is discharged only for well-nested callers, and that is a
      checker guarantee, not a runtime one.

  CUTS
    * The counters are `Nat` here and `unsigned` in C: WRAPAROUND at 2^32 is
      not modelled. The model is the implementation as long as fewer than
      2^32 tickets are outstanding for one lock.
    * The C11 orderings (acquire on the spin load, release on the release
      store) are what makes the two instructions synchronisation points; that
      every interleaving of them is SC is the named premise `DRFSC` of
      `CNebenlaeufig.lean`, not something this file proves.
    * A `dreht` step is a load of a word no program object aliases, so it
      carries the empty footprint (`Etikett.still`); the spin is invisible to
      `RennfreiC` by construction and not by an argument about atomics.
-/
import Grammatik.CNebenlaeufig

namespace Gabbro.Grammatik

/-! ## 1. A one-point update -/

/-- One entry of a function replaced. -/
def aendere {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) : α → β :=
  fun x => if x = a then v else f x

theorem aendere_eq {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) :
    aendere f a v a = v := if_pos rfl

theorem aendere_ne {α β : Type} [DecidableEq α] (f : α → β) (a x : α) (v : β) (h : x ≠ a) :
    aendere f a v x = f x := if_neg h

/-! ## 2. The lock's state and its four instructions -/

/-- **The state of the runtime's locks**: the two counters of every lock
    (`next`, `now`), the ticket a thread is spinning on (the local `my` of
    `L_nimm`, live only inside the call), and the locks a thread stands
    between the return of `L_nimm` and the call of `L_gib` for (its program
    counter, not a word of the lock). -/
structure TZust where
  next : Nat → Nat
  now : Nat → Nat
  zieht : Faden → Option (Nat × Nat)
  haelt : Faden → List Nat

/-- `my = atomic_fetch_add(&L.next, 1)`. -/
def zieheT (Z : TZust) (t : Faden) (L : Nat) : TZust :=
  { Z with next := aendere Z.next L (Z.next L + 1),
           zieht := aendere Z.zieht t (some (L, Z.next L)) }

/-- The spin load finds `now == my`: `L_nimm` returns. -/
def trittT (Z : TZust) (t : Faden) (L : Nat) : TZust :=
  { Z with zieht := aendere Z.zieht t none,
           haelt := aendere Z.haelt t (L :: Z.haelt t) }

/-- `atomic_store(&L.now, now + 1)`: the release. -/
def gibtT (Z : TZust) (t : Faden) (L : Nat) : TZust :=
  { Z with now := aendere Z.now L (Z.now L + 1),
           haelt := aendere Z.haelt t ((Z.haelt t).filter (fun L' => decide (L' ≠ L))) }

theorem mem_gibtT {l : List Nat} {a L : Nat} :
    a ∈ l.filter (fun L' => decide (L' ≠ L)) ↔ a ∈ l ∧ a ≠ L := by
  rw [List.mem_filter]
  exact ⟨fun h => ⟨h.1, of_decide_eq_true h.2⟩, fun h => ⟨h.1, decide_eq_true h.2⟩⟩

/-- **ONE INSTRUCTION OF THE TICKET LOCK**, by thread `t`. The second
    argument is what the ABSTRACT semantics sees of it: nothing (`none`: the
    ticket draw and a failed spin load), or the acquire, or the release. -/
inductive TSchritt : TZust → Faden → Option SperrOp → TZust → Prop where
  /-- `my = fetch_add(&L.next, 1)` -- only when the caller is not already
      inside an `L_nimm` (it is the first instruction of the call). -/
  | zieht (Z : TZust) (t : Faden) (L : Nat) (hz : Z.zieht t = none) :
      TSchritt Z t none (zieheT Z t L)
  /-- The spin load finds `now != my`: nothing changes. -/
  | dreht (Z : TZust) (t : Faden) (L m : Nat) (hz : Z.zieht t = some (L, m))
      (hne : Z.now L ≠ m) : TSchritt Z t none Z
  /-- The spin load finds `now == my`: the acquire completes. -/
  | tritt (Z : TZust) (t : Faden) (L m : Nat) (hz : Z.zieht t = some (L, m))
      (he : Z.now L = m) : TSchritt Z t (some (.nimm L)) (trittT Z t L)
  /-- The release store. The guard is the CALLER's position (it stands
      between its `L_nimm` and its `L_gib`), NOT a check the lock performs:
      see `gib_ohne_wache`. -/
  | gibt (Z : TZust) (t : Faden) (L : Nat) (hh : L ∈ Z.haelt t) :
      TSchritt Z t (some (.gib L)) (gibtT Z t L)

/-! ## 3. The invariant, and mutual exclusion -/

/-- **THE INVARIANT OF THE TICKET LOCK.** The counters never cross; every
    drawn ticket is distinct, and lies in `[now, next)`; and while a thread
    stands inside `L`, every drawn ticket of `L` is STRICTLY above `now` --
    which is what says that `now` is the holder's own ticket, without
    storing it anywhere. -/
structure TInv (Z : TZust) : Prop where
  wort : ∀ L, Z.now L ≤ Z.next L
  eindeutig : ∀ t u L m, Z.zieht t = some (L, m) → Z.zieht u = some (L, m) → t = u
  bereich : ∀ t L m, Z.zieht t = some (L, m) → Z.now L ≤ m ∧ m < Z.next L
  halter : ∀ t L, L ∈ Z.haelt t →
    Z.now L < Z.next L ∧ ∀ u m, Z.zieht u = some (L, m) → Z.now L < m
  exklusiv : ∀ t u L, L ∈ Z.haelt t → L ∈ Z.haelt u → t = u

/-- **MUTUAL EXCLUSION**: two threads never stand inside one lock. -/
theorem ticket_ausschluss {Z : TZust} (hI : TInv Z) {t u L : Faden}
    (ht : L ∈ Z.haelt t) (hu : L ∈ Z.haelt u) : t = u :=
  hI.exklusiv t u L ht hu

/-- **A thread whose ticket is served finds the lock EMPTY**: nobody stands
    inside it. This is the step at which mutual exclusion is earned. -/
theorem tritt_frei {Z : TZust} (hI : TInv Z) {t : Faden} {L m : Nat}
    (hz : Z.zieht t = some (L, m)) (he : Z.now L = m) (u : Faden) : L ∉ Z.haelt u := by
  intro hu
  have := (hI.halter u L hu).2 t m hz
  omega

/-- **The ticket lock is NOT re-entrant, and it does not pretend to be**: a
    thread that holds `L` and calls `L_nimm()` again draws a ticket strictly
    above `now`, so its spin never ends. -/
theorem ticket_nicht_wiedereintritt {Z : TZust} (hI : TInv Z) {t : Faden} {L m : Nat}
    (hh : L ∈ Z.haelt t) (hz : Z.zieht t = some (L, m)) : Z.now L < m :=
  (hI.halter t L hh).2 t m hz

/-! ### The three updates, entry by entry -/

theorem zieheT_next_eq (Z : TZust) (t : Faden) (L : Nat) :
    (zieheT Z t L).next L = Z.next L + 1 := aendere_eq _ _ _

theorem zieheT_next_ne (Z : TZust) (t : Faden) (L K : Nat) (h : K ≠ L) :
    (zieheT Z t L).next K = Z.next K := aendere_ne _ _ _ _ h

theorem zieheT_now (Z : TZust) (t : Faden) (L : Nat) : (zieheT Z t L).now = Z.now := rfl

theorem zieheT_haelt (Z : TZust) (t : Faden) (L : Nat) : (zieheT Z t L).haelt = Z.haelt := rfl

theorem zieheT_zieht_eq (Z : TZust) (t : Faden) (L : Nat) :
    (zieheT Z t L).zieht t = some (L, Z.next L) := aendere_eq _ _ _

theorem zieheT_zieht_ne (Z : TZust) (t u : Faden) (L : Nat) (h : u ≠ t) :
    (zieheT Z t L).zieht u = Z.zieht u := aendere_ne _ _ _ _ h

theorem trittT_next (Z : TZust) (t : Faden) (L : Nat) : (trittT Z t L).next = Z.next := rfl

theorem trittT_now (Z : TZust) (t : Faden) (L : Nat) : (trittT Z t L).now = Z.now := rfl

theorem trittT_zieht_eq (Z : TZust) (t : Faden) (L : Nat) : (trittT Z t L).zieht t = none :=
  aendere_eq _ _ _

theorem trittT_zieht_ne (Z : TZust) (t u : Faden) (L : Nat) (h : u ≠ t) :
    (trittT Z t L).zieht u = Z.zieht u := aendere_ne _ _ _ _ h

theorem trittT_haelt_eq (Z : TZust) (t : Faden) (L : Nat) :
    (trittT Z t L).haelt t = L :: Z.haelt t := aendere_eq _ _ _

theorem trittT_haelt_ne (Z : TZust) (t u : Faden) (L : Nat) (h : u ≠ t) :
    (trittT Z t L).haelt u = Z.haelt u := aendere_ne _ _ _ _ h

theorem gibtT_next (Z : TZust) (t : Faden) (L : Nat) : (gibtT Z t L).next = Z.next := rfl

theorem gibtT_zieht (Z : TZust) (t : Faden) (L : Nat) : (gibtT Z t L).zieht = Z.zieht := rfl

theorem gibtT_now_eq (Z : TZust) (t : Faden) (L : Nat) :
    (gibtT Z t L).now L = Z.now L + 1 := aendere_eq _ _ _

theorem gibtT_now_ne (Z : TZust) (t : Faden) (L K : Nat) (h : K ≠ L) :
    (gibtT Z t L).now K = Z.now K := aendere_ne _ _ _ _ h

theorem gibtT_haelt_eq (Z : TZust) (t : Faden) (L : Nat) :
    (gibtT Z t L).haelt t = (Z.haelt t).filter (fun L' => decide (L' ≠ L)) := aendere_eq _ _ _

theorem gibtT_haelt_ne (Z : TZust) (t u : Faden) (L : Nat) (h : u ≠ t) :
    (gibtT Z t L).haelt u = Z.haelt u := aendere_ne _ _ _ _ h

/-- The ticket a thread spins on after a draw: the drawer has the drawn one,
    everybody else keeps theirs. -/
theorem zieheT_zieht_inv {Z : TZust} {t u : Faden} {L K m : Nat}
    (h : (zieheT Z t L).zieht u = some (K, m)) :
    (u = t ∧ K = L ∧ m = Z.next L) ∨ (u ≠ t ∧ Z.zieht u = some (K, m)) := by
  by_cases e : u = t
  · subst e
    rw [zieheT_zieht_eq] at h
    have h' := Option.some.inj h
    exact Or.inl ⟨rfl, (congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
  · rw [zieheT_zieht_ne _ _ _ _ e] at h
    exact Or.inr ⟨e, h⟩

theorem trittT_zieht_inv {Z : TZust} {t u : Faden} {L K m : Nat}
    (h : (trittT Z t L).zieht u = some (K, m)) : u ≠ t ∧ Z.zieht u = some (K, m) := by
  by_cases e : u = t
  · subst e; rw [trittT_zieht_eq] at h; cases h
  · rw [trittT_zieht_ne _ _ _ _ e] at h; exact ⟨e, h⟩

theorem trittT_haelt_inv {Z : TZust} {t u : Faden} {L K : Nat}
    (h : K ∈ (trittT Z t L).haelt u) : (u = t ∧ K = L) ∨ K ∈ Z.haelt u := by
  by_cases e : u = t
  · subst e
    rw [trittT_haelt_eq] at h
    rcases List.mem_cons.mp h with rfl | h'
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr h'
  · rw [trittT_haelt_ne _ _ _ _ e] at h; exact Or.inr h

theorem gibtT_haelt_inv {Z : TZust} {t u : Faden} {L K : Nat}
    (h : K ∈ (gibtT Z t L).haelt u) : K ∈ Z.haelt u ∧ ¬ (u = t ∧ K = L) := by
  by_cases e : u = t
  · subst e
    rw [gibtT_haelt_eq] at h
    obtain ⟨h1, h2⟩ := mem_gibtT.mp h
    exact ⟨h1, fun hc => h2 hc.2⟩
  · rw [gibtT_haelt_ne _ _ _ _ e] at h
    exact ⟨h, fun hc => e hc.1⟩

/-- **FIFO: NOBODY OVERTAKES A WAITING THREAD.** While an earlier ticket for
    `L` is outstanding, a later one cannot be served -- the acquire of the
    thread holding the bigger ticket is not enabled, whatever the schedule
    does. This is the local form of `FifoSperre` (`Lebendigkeit.lean`), which
    the waiting bound assumes on machine-G runs; here it is a consequence of
    the two counters, since every outstanding ticket is at least `now`
    (`TInv.bereich`) and the acquire needs `now == my`. -/
theorem ticket_fifo {Z : TZust} (hI : TInv Z) {t u : Faden} {L m m' : Nat}
    (ht : Z.zieht t = some (L, m)) (hu : Z.zieht u = some (L, m')) (hlt : m < m') :
    ¬ ∃ Z', TSchritt Z u (some (.nimm L)) Z' := by
  rintro ⟨Z', hs⟩
  cases hs with
  | tritt =>
      rename_i m'' hz he
      rw [hu] at hz
      have em : m'' = m' := (congrArg Prod.snd (Option.some.inj hz)).symm
      rw [em] at he
      have := (hI.bereich t L m ht).1
      omega

/-- **The invariant survives every instruction.** -/
theorem tinv_schritt {Z Z' : TZust} {t : Faden} {o : Option SperrOp} (hI : TInv Z)
    (hs : TSchritt Z t o Z') : TInv Z' := by
  cases hs with
  | zieht L hz =>
      refine ⟨fun K => ?_, fun a b K m ha hb => ?_, fun a K m ha => ?_,
        fun a K hK => ⟨?_, fun u m hu => ?_⟩, ?_⟩
      · rw [zieheT_now]
        by_cases e : K = L
        · subst e; rw [zieheT_next_eq]; have := hI.wort K; omega
        · rw [zieheT_next_ne _ _ _ _ e]; exact hI.wort K
      · rcases zieheT_zieht_inv ha with ⟨rfl, rfl, rfl⟩ | ⟨-, ha'⟩
        · rcases zieheT_zieht_inv hb with ⟨rfl, -, -⟩ | ⟨-, hb'⟩
          · rfl
          · exact absurd (hI.bereich b K _ hb').2 (by omega)
        · rcases zieheT_zieht_inv hb with ⟨rfl, rfl, rfl⟩ | ⟨-, hb'⟩
          · exact absurd (hI.bereich a K _ ha').2 (by omega)
          · exact hI.eindeutig a b K m ha' hb'
      · rw [zieheT_now]
        rcases zieheT_zieht_inv ha with ⟨rfl, rfl, rfl⟩ | ⟨-, ha'⟩
        · rw [zieheT_next_eq]
          exact ⟨hI.wort K, by omega⟩
        · have hb := hI.bereich a K m ha'
          by_cases e : K = L
          · subst e; rw [zieheT_next_eq]; exact ⟨hb.1, by omega⟩
          · rw [zieheT_next_ne _ _ _ _ e]; exact hb
      · rw [zieheT_haelt] at hK
        rw [zieheT_now]
        have h1 := (hI.halter a K hK).1
        by_cases e : K = L
        · subst e; rw [zieheT_next_eq]; omega
        · rw [zieheT_next_ne _ _ _ _ e]; exact h1
      · rw [zieheT_haelt] at hK
        rw [zieheT_now]
        rcases zieheT_zieht_inv hu with ⟨rfl, rfl, rfl⟩ | ⟨-, hu'⟩
        · exact (hI.halter a K hK).1
        · exact (hI.halter a K hK).2 u m hu'
      · intro a b K ha hb
        rw [zieheT_haelt] at ha hb
        exact hI.exklusiv a b K ha hb
  | dreht L m hz hne => exact hI
  | tritt L m hz he =>
      have hfrei := tritt_frei hI hz he
      have hoben : ∀ u m', u ≠ t → Z.zieht u = some (L, m') → Z.now L < m' := by
        intro u m' hne hu
        have h1 := (hI.bereich u L m' hu).1
        have h2 : m' ≠ m := fun e => hne (hI.eindeutig u t L m' hu (e ▸ hz))
        omega
      refine ⟨fun K => hI.wort K, fun a b K m' ha hb => ?_, fun a K m' ha => ?_,
        fun a K hK => ?_, fun a b K ha hb => ?_⟩
      · exact hI.eindeutig a b K m' (trittT_zieht_inv ha).2 (trittT_zieht_inv hb).2
      · rw [trittT_now, trittT_next]
        exact hI.bereich a K m' (trittT_zieht_inv ha).2
      · rw [trittT_now, trittT_next]
        rcases trittT_haelt_inv hK with ⟨-, hKL⟩ | hK'
        · have h2 : Z.zieht t = some (K, m) := by rw [hKL]; exact hz
          have h3 : Z.now K = m := by rw [hKL]; exact he
          refine ⟨?_, fun u m' hu => ?_⟩
          · have := (hI.bereich t K m h2).2
            omega
          · have hu' := trittT_zieht_inv hu
            rw [hKL]
            rw [hKL] at hu'
            exact hoben u m' hu'.1 hu'.2
        · exact ⟨(hI.halter a K hK').1,
            fun u m' hu => (hI.halter a K hK').2 u m' (trittT_zieht_inv hu).2⟩
      · rcases trittT_haelt_inv ha with ⟨hat, hKL⟩ | ha'
        · rcases trittT_haelt_inv hb with ⟨hbt, -⟩ | hb'
          · rw [hat, hbt]
          · exact absurd (hKL ▸ hb') (hfrei b)
        · rcases trittT_haelt_inv hb with ⟨-, hKL⟩ | hb'
          · exact absurd (hKL ▸ ha') (hfrei a)
          · exact hI.exklusiv a b K ha' hb'
  | gibt L hh =>
      have hLt := hI.halter t L hh
      have hkein : ∀ u, L ∉ (gibtT Z t L).haelt u := by
        intro u hu
        obtain ⟨h1, h2⟩ := gibtT_haelt_inv hu
        exact h2 ⟨hI.exklusiv u t L h1 hh, rfl⟩
      refine ⟨fun K => ?_, fun a b K m ha hb => hI.eindeutig a b K m ha hb,
        fun a K m ha => ?_, fun a K hK => ?_,
        fun a b K ha hb => hI.exklusiv a b K (gibtT_haelt_inv ha).1 (gibtT_haelt_inv hb).1⟩
      · rw [gibtT_next]
        by_cases e : K = L
        · subst e; rw [gibtT_now_eq]; omega
        · rw [gibtT_now_ne _ _ _ _ e]; exact hI.wort K
      · rw [gibtT_next]
        rw [gibtT_zieht] at ha
        by_cases e : K = L
        · subst e
          rw [gibtT_now_eq]
          have := hLt.2 a m ha
          exact ⟨by omega, (hI.bereich a K m ha).2⟩
        · rw [gibtT_now_ne _ _ _ _ e]; exact hI.bereich a K m ha
      · have hKL : K ≠ L := fun e => hkein a (e ▸ hK)
        rw [gibtT_next, gibtT_now_ne _ _ _ _ hKL, gibtT_zieht]
        exact hI.halter a K (gibtT_haelt_inv hK).1

/-! ## 4. The abstraction, and the refinement of `sperrAbstrakt` -/

theorem halterSetze_eq (h : Halter) (L : Nat) (v : Option Faden) : halterSetze h L v L = v :=
  if_pos rfl

theorem halterSetze_ne (h : Halter) (L K : Nat) (v : Option Faden) (e : K ≠ L) :
    halterSetze h L v K = h K := if_neg e

/-- **The abstract holder table of a concrete state**: `h` says that `t`
    holds `L` exactly when `t` stands between its `L_nimm(L)` and its
    `L_gib(L)`. -/
def AbsT (Z : TZust) (h : Halter) : Prop :=
  ∀ (L : Nat) (t : Faden), h L = some t ↔ L ∈ Z.haelt t

/-- One concrete state has ONE abstract holder table. -/
theorem abs_eindeutig {Z : TZust} {h h' : Halter} (hA : AbsT Z h) (hA' : AbsT Z h') : h = h' := by
  funext L
  cases e : h L with
  | none =>
      cases e' : h' L with
      | none => rfl
      | some u =>
          have := (hA L u).mpr ((hA' L u).mp e')
          rw [e] at this
          cases this
  | some u => exact ((hA' L u).mpr ((hA L u).mp e)).symm

theorem abs_frei {Z : TZust} {h : Halter} (hA : AbsT Z h) {L : Nat}
    (hf : ∀ u, L ∉ Z.haelt u) : h L = none := by
  cases e : h L with
  | none => rfl
  | some u => exact absurd ((hA L u).mp e) (hf u)

/-- The abstract table after an acquire. -/
theorem abs_tritt {Z : TZust} {h : Halter} (hA : AbsT Z h) {t : Faden} {L : Nat}
    (hf : ∀ u, L ∉ Z.haelt u) : AbsT (trittT Z t L) (halterSetze h L (some t)) := by
  intro K u
  by_cases eK : K = L
  · subst eK
    rw [halterSetze_eq]
    constructor
    · intro hu
      have hut : u = t := (Option.some.inj hu).symm
      rw [hut, trittT_haelt_eq]
      exact List.mem_cons_self
    · intro hu
      by_cases eu : u = t
      · rw [eu]
      · rw [trittT_haelt_ne _ _ _ _ eu] at hu
        exact absurd hu (hf u)
  · rw [halterSetze_ne _ _ _ _ eK]
    by_cases eu : u = t
    · have hg : K ∈ (trittT Z t L).haelt u ↔ K ∈ Z.haelt u := by
        rw [eu, trittT_haelt_eq]
        constructor
        · intro h'
          rcases List.mem_cons.mp h' with e | h''
          · exact absurd e eK
          · exact h''
        · exact fun h' => List.mem_cons_of_mem _ h'
      rw [hg]
      exact hA K u
    · rw [trittT_haelt_ne _ _ _ _ eu]
      exact hA K u

/-- The abstract table after a release. -/
theorem abs_gibt {Z : TZust} {h : Halter} (hI : TInv Z) (hA : AbsT Z h) {t : Faden} {L : Nat}
    (hh : L ∈ Z.haelt t) : AbsT (gibtT Z t L) (halterSetze h L none) := by
  intro K u
  by_cases eK : K = L
  · subst eK
    rw [halterSetze_eq]
    constructor
    · intro hu; cases hu
    · intro hu
      exfalso
      by_cases eu : u = t
      · rw [eu, gibtT_haelt_eq] at hu
        exact (mem_gibtT.mp hu).2 rfl
      · rw [gibtT_haelt_ne _ _ _ _ eu] at hu
        exact eu (hI.exklusiv u t K hu hh)
  · rw [halterSetze_ne _ _ _ _ eK]
    by_cases eu : u = t
    · have hg : K ∈ (gibtT Z t L).haelt u ↔ K ∈ Z.haelt u := by
        rw [eu, gibtT_haelt_eq]
        exact ⟨fun h' => (mem_gibtT.mp h').1, fun h' => mem_gibtT.mpr ⟨h', eK⟩⟩
      rw [hg]
      exact hA K u
    · rw [gibtT_haelt_ne _ _ _ _ eu]
      exact hA K u

/-- **THE ABSTRACT RELATION THE TICKET LOCK INDUCES**: what the interleaved
    semantics of `CNebenlaeufig.lean` sees of one instruction of the lock --
    the acquire that completes, and the release -- read through the
    abstraction, from a state the invariant holds at. -/
def ticketLP : SperrSem := fun t op h h' =>
  ∃ Z Z' : TZust, TInv Z ∧ AbsT Z h ∧ AbsT Z' h' ∧ TSchritt Z t (some op) Z'

/-- **THE PREMISE, PROVED.** Every step of the runtime's ticket lock is a step
    of `sperrAbstrakt`: `L_nimm` completes only on a free lock and makes the
    caller its holder, `L_gib` fires only for the holder and frees it. This
    is the clause `LaufzeitC.sperre` of `CNebenlaeufig.lean`, for the lock the
    runtime has -- an assumption until here, a theorem from here. -/
theorem ticketLP_sperrAbstrakt : ∀ t op h h', ticketLP t op h h' → sperrAbstrakt t op h h' := by
  rintro t op h h' ⟨Z, Z', hI, hA, hA', hs⟩
  cases hs with
  | tritt L m hz he =>
      have hf := tritt_frei hI hz he
      exact ⟨abs_frei hA hf, abs_eindeutig hA' (abs_tritt hA hf)⟩
  | gibt L hh =>
      exact ⟨(hA L t).mpr hh, abs_eindeutig hA' (abs_gibt hI hA hh)⟩

/-! ## 5. The two findings -/

/-- A concrete state with two waiting threads and a free lock. -/
def zEins : TZust := ⟨fun _ => 1, fun _ => 0, fun u => if u = 7 then some (0, 0) else none,
  fun _ => []⟩

def zZwei : TZust := ⟨fun _ => 2, fun _ => 0,
  fun u => if u = 7 then some (0, 1) else if u = 8 then some (0, 0) else none, fun _ => []⟩

/-- **FINDING 1: the ticket lock reveals MORE than held or free.** Two
    concrete states with the SAME abstract holder table -- the lock is free
    in both -- and one thread `7` whose acquire completes in the one and
    CANNOT complete in the other: in `zZwei` thread `8` drew the earlier
    ticket. `sperrAbstrakt` admits the step in both (`sperrAbstrakt_nur_eigen`:
    the holder entry decides), the implementation does not.

    For the SAFETY statement of stage (b) this is harmless: the refinement
    runs from the implementation to the specification, and fewer runs are
    fewer runs. For the entry of `NICHTINTERFERENZ.md` §10 it is not: a
    waiting thread can measure its position in the queue, which is the
    ARRIVAL ORDER of the other threads, and that is not "held or free". -/
theorem ticket_mehr_als_frei :
    TInv zEins ∧ TInv zZwei ∧ AbsT zEins (fun _ => none) ∧ AbsT zZwei (fun _ => none) ∧
      (∃ Z', TSchritt zEins 7 (some (.nimm 0)) Z') ∧
      (¬ ∃ Z', TSchritt zZwei 7 (some (.nimm 0)) Z') ∧
      (∃ h', sperrAbstrakt 7 (.nimm 0) (fun _ => none) h') := by
  have hz1 : ∀ (a : Faden) (L m : Nat), zEins.zieht a = some (L, m) → a = 7 ∧ L = 0 ∧ m = 0 := by
    intro a L m ha
    have ha' : (if a = 7 then some ((0 : Nat), (0 : Nat)) else none) = some (L, m) := ha
    by_cases e : a = 7
    · rw [if_pos e] at ha'
      have := Option.some.inj ha'
      exact ⟨e, (congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩
    · rw [if_neg e] at ha'; cases ha'
  have hz2 : ∀ (a : Faden) (L m : Nat), zZwei.zieht a = some (L, m) →
      L = 0 ∧ ((a = 7 ∧ m = 1) ∨ (a = 8 ∧ m = 0)) := by
    intro a L m ha
    have ha' : (if a = 7 then some ((0 : Nat), (1 : Nat))
      else if a = 8 then some ((0 : Nat), (0 : Nat)) else none) = some (L, m) := ha
    by_cases e : a = 7
    · rw [if_pos e] at ha'
      have := Option.some.inj ha'
      exact ⟨(congrArg Prod.fst this).symm, Or.inl ⟨e, (congrArg Prod.snd this).symm⟩⟩
    · rw [if_neg e] at ha'
      by_cases e' : a = 8
      · rw [if_pos e'] at ha'
        have := Option.some.inj ha'
        exact ⟨(congrArg Prod.fst this).symm, Or.inr ⟨e', (congrArg Prod.snd this).symm⟩⟩
      · rw [if_neg e'] at ha'; cases ha'
  have hh1 : ∀ (a : Faden) (L : Nat), L ∉ zEins.haelt a := fun a L h => absurd h List.not_mem_nil
  have hh2 : ∀ (a : Faden) (L : Nat), L ∉ zZwei.haelt a := fun a L h => absurd h List.not_mem_nil
  refine ⟨⟨fun _ => Nat.zero_le 1, ?_, ?_, fun a L hL => absurd hL (hh1 a L),
      fun a b L hL => absurd hL (hh1 a L)⟩,
    ⟨fun _ => Nat.zero_le 2, ?_, ?_, fun a L hL => absurd hL (hh2 a L),
      fun a b L hL => absurd hL (hh2 a L)⟩,
    fun L t => ⟨(fun h => by cases h), fun h => absurd h (hh1 t L)⟩,
    fun L t => ⟨(fun h => by cases h), fun h => absurd h (hh2 t L)⟩,
    ⟨_, .tritt zEins 7 0 0 rfl rfl⟩, ?_, ⟨_, rfl, rfl⟩⟩
  · intro a b L m ha hb
    rw [(hz1 a L m ha).1, (hz1 b L m hb).1]
  · intro a L m ha
    obtain ⟨-, rfl, rfl⟩ := hz1 a L m ha
    exact ⟨Nat.le_refl 0, Nat.zero_lt_one⟩
  · intro a b L m ha hb
    have g1 := (hz2 a L m ha).2
    have g2 := (hz2 b L m hb).2
    rcases g1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases g2 with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
      first | rfl | omega
  · intro a L m ha
    obtain ⟨rfl, hm⟩ := hz2 a L m ha
    rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨Nat.zero_le 1, by decide⟩
    · exact ⟨Nat.le_refl 0, by decide⟩
  · rintro ⟨Z', hs⟩
    cases hs with
    | tritt =>
        rename_i m hz he
        obtain ⟨-, hm⟩ := hz2 7 0 m hz
        rcases hm with ⟨-, rfl⟩ | ⟨h8, -⟩
        · exact absurd he (by decide)
        · exact absurd h8 (by decide)

/-- A state in which thread `1` holds lock `0` and thread `2` waits. -/
def zDrin : TZust := ⟨fun _ => 2, fun _ => 0, fun u => if u = 2 then some (0, 1) else none,
  fun u => if u = 1 then [0] else []⟩

/-- The release the runtime actually performs: `now++`, WITHOUT a check. -/
def gibtRoh (Z : TZust) (L : Nat) : TZust :=
  { Z with now := aendere Z.now L (Z.now L + 1) }

/-- **FINDING 2: the release performs no check, and an unheld release breaks
    mutual exclusion.** `L_gib()` is `atomic_store(&L.now, now + 1)`; it
    succeeds for any caller. From `zDrin` -- thread `1` inside the lock,
    thread `2` waiting on ticket `1` -- one unguarded `now++` by a thread
    that holds nothing lets thread `2` in while thread `1` is still inside:
    two holders, and the invariant is gone.

    So the refinement of the `.gib` case is discharged only for callers that
    hold the lock, and THAT is a guarantee of the checker (a `L_gib()` is
    emitted only where the holder stands), not of the runtime. What the
    runtime would have to do to carry it alone: keep the holder's identity in
    the lock (`_Atomic unsigned besitzer`) and make the release a compare --
    which costs a word and a branch per release and is exactly the check the
    emitter's W6 rule ("what the checker decided, the machine does not check
    again") declines to emit. -/
theorem gib_ohne_wache :
    TInv zDrin ∧ (0 : Nat) ∈ zDrin.haelt 1 ∧
      ¬ TInv (gibtRoh zDrin 0) ∧
      (∃ Z', TSchritt (gibtRoh zDrin 0) 2 (some (.nimm 0)) Z' ∧
        (0 : Nat) ∈ Z'.haelt 1 ∧ (0 : Nat) ∈ Z'.haelt 2 ∧ (1 : Faden) ≠ 2) := by
  have hz : ∀ (a : Faden) (L m : Nat), zDrin.zieht a = some (L, m) → a = 2 ∧ L = 0 ∧ m = 1 := by
    intro a L m ha
    have ha' : (if a = 2 then some ((0 : Nat), (1 : Nat)) else none) = some (L, m) := ha
    by_cases e : a = 2
    · rw [if_pos e] at ha'
      have := Option.some.inj ha'
      exact ⟨e, (congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩
    · rw [if_neg e] at ha'; cases ha'
  have hh : ∀ (a : Faden) (L : Nat), L ∈ zDrin.haelt a → a = 1 ∧ L = 0 := by
    intro a L ha
    have ha' : L ∈ (if a = 1 then [(0 : Nat)] else []) := ha
    by_cases e : a = 1
    · rw [if_pos e] at ha'
      rcases List.mem_cons.mp ha' with rfl | h
      · exact ⟨e, rfl⟩
      · exact absurd h List.not_mem_nil
    · rw [if_neg e] at ha'; exact absurd ha' List.not_mem_nil
  have h10 : (0 : Nat) ∈ zDrin.haelt 1 := by
    show (0 : Nat) ∈ (if (1 : Faden) = 1 then [(0 : Nat)] else [])
    rw [if_pos rfl]
    exact List.mem_cons_self
  have hI : TInv zDrin := by
    refine ⟨fun _ => Nat.zero_le 2, ?_, ?_, ?_, ?_⟩
    · intro a b L m ha hb
      rw [(hz a L m ha).1, (hz b L m hb).1]
    · intro a L m ha
      obtain ⟨-, rfl, rfl⟩ := hz a L m ha
      exact ⟨by decide, by decide⟩
    · intro a L hL
      obtain ⟨rfl, rfl⟩ := hh a L hL
      refine ⟨by decide, fun u m hu => ?_⟩
      obtain ⟨-, -, rfl⟩ := hz u 0 m hu
      exact by decide
    · intro a b L ha hb
      rw [(hh a L ha).1, (hh b L hb).1]
  have hnow : (gibtRoh zDrin 0).now 0 = 1 := by
    show aendere zDrin.now 0 (zDrin.now 0 + 1) 0 = 1
    rw [aendere_eq]
    rfl
  have hzr : (gibtRoh zDrin 0).zieht 2 = some (0, 1) := by
    show (if (2 : Faden) = 2 then some ((0 : Nat), (1 : Nat)) else none) = some (0, 1)
    rw [if_pos rfl]
  refine ⟨hI, h10, ?_, ?_⟩
  · intro hI'
    have := (hI'.halter 1 0 h10).2 2 1 hzr
    omega
  · refine ⟨_, .tritt (gibtRoh zDrin 0) 2 0 1 hzr hnow, ?_, ?_, by decide⟩
    · show (0 : Nat) ∈ aendere (gibtRoh zDrin 0).haelt 2 (0 :: (gibtRoh zDrin 0).haelt 2) 1
      rw [aendere_ne _ _ _ _ (by decide : (1 : Faden) ≠ 2)]
      exact h10
    · show (0 : Nat) ∈ aendere (gibtRoh zDrin 0).haelt 2 (0 :: (gibtRoh zDrin 0).haelt 2) 2
      rw [aendere_eq]
      exact List.mem_cons_self

/-! ## 6. The C program with the lock implementation inlined -/

/-- A foreign call has no meaning inside a block: the block semantics of a
    unit gives foreign calls no relation (`keinXR`). -/
theorem ext_kein_block_gen (E : CEinheit) {n : Nat} {args : List CX} {dst : Option (Nat × CTy)}
    {st : CSt} {ρ : CLok} {o : COut} : ¬ E.laeuft (.ext n args dst) st ρ o := by
  intro h
  cases h with
  | ext _ hxr _ => exact hxr.elim

/-- The lock meaning that admits NO step: with it, the rule `sperre` of
    `SchrittC` cannot fire, and what is left are exactly the program's own
    steps. -/
def keinLP : SperrSem := fun _ _ _ _ => False

theorem keinLP_halter {E : CEinheit} {K K' : KonfC} {t : Faden} {ℓ : Etikett}
    (h : SchrittC E keinLP K t ℓ K') : K'.halter = K.halter := by
  cases h with
  | teile => rfl
  | ende => rfl
  | block => rfl
  | rueck => rfl
  | sperre _ _ _ _ _ _ _ hl => exact hl.elim

theorem keinLP_mono {E : CEinheit} {K K' : KonfC} {t : Faden} {ℓ : Etikett}
    (h : SchrittC E keinLP K t ℓ K') : SchrittC E sperrAbstrakt K t ℓ K' :=
  schrittC_mono (fun _ _ _ _ h => h.elim) h

/-- **A configuration of the C program WITH the lock implementation**: the C
    configuration of `CNebenlaeufig.lean` -- whose holder table is the
    ABSTRACT view, kept in step -- and the state of the runtime's locks. -/
structure KonfT where
  k : KonfC
  z : TZust

/-- **ONE STEP OF THE C PROGRAM WITH THE TICKET LOCK INLINED.** Everything
    that is not the lock is a step of the existing semantics (`rein`, with
    `keinLP`: the abstract lock rule cannot fire); a lock call is the four
    instructions of `L_nimm`/`L_gib`, one step each, at the head of the
    thread's continuation. A thread inside `L_nimm` takes no step of the
    program: its control is inside the runtime function. -/
inductive SchrittT (E : CEinheit) : KonfT → Faden → Etikett → KonfT → Prop where
  /-- The program's own step. -/
  | rein (T : KonfT) (t : Faden) (ℓ : Etikett) (K' : KonfC) (hz : T.z.zieht t = none)
      (h : SchrittC E keinLP T.k t ℓ K') : SchrittT E T t ℓ ⟨K', T.z⟩
  /-- `my = fetch_add(&L.next, 1)` at the head `L_nimm();`. -/
  | zieht (T : KonfT) (t : Faden) (n : Nat) (k : List CS) (ρ : CLok) (L : Nat)
      (h : T.k.faeden t = .an (.ext n [] none :: k) ρ) (ho : E.sperre n = some (.nimm L))
      (hz : T.z.zieht t = none) : SchrittT E T t .still ⟨T.k, zieheT T.z t L⟩
  /-- A spin load that finds `now != my`. -/
  | dreht (T : KonfT) (t : Faden) (L m : Nat) (hz : T.z.zieht t = some (L, m))
      (hne : T.z.now L ≠ m) : SchrittT E T t .still T
  /-- The spin load that finds `now == my`: `L_nimm()` returns, and the
      continuation moves past the call. -/
  | tritt (T : KonfT) (t : Faden) (n : Nat) (k : List CS) (ρ : CLok) (L m : Nat)
      (h : T.k.faeden t = .an (.ext n [] none :: k) ρ) (ho : E.sperre n = some (.nimm L))
      (hz : T.z.zieht t = some (L, m)) (he : T.z.now L = m) :
      SchrittT E T t (.sperre (.nimm L))
        ⟨⟨T.k.st, fadenSetze T.k.faeden t (.an k ρ), halterSetze T.k.halter L (some t)⟩,
          trittT T.z t L⟩
  /-- The release store at the head `L_gib();`. -/
  | gibt (T : KonfT) (t : Faden) (n : Nat) (k : List CS) (ρ : CLok) (L : Nat)
      (h : T.k.faeden t = .an (.ext n [] none :: k) ρ) (ho : E.sperre n = some (.gib L))
      (hh : L ∈ T.z.haelt t) :
      SchrittT E T t (.sperre (.gib L))
        ⟨⟨T.k.st, fadenSetze T.k.faeden t (.an k ρ), halterSetze T.k.halter L none⟩,
          gibtT T.z t L⟩

/-- **THE FRAME OF THE LOCK PRIMITIVE**: a step that is a call of the lock
    leaves the program's memory alone, and changes nothing but its own lock's
    holder entry and counters -- the two words and the caller's `my` are
    runtime objects, not program objects (`sperrAbstrakt_rahmen` for the
    implementation). -/
theorem ticket_frame {E : CEinheit} {T T' : KonfT} {t : Faden} {op : SperrOp}
    (h : SchrittT E T t (.sperre op) T') :
    T'.k.st = T.k.st ∧ (∀ L, L ≠ op.nr → T'.k.halter L = T.k.halter L) ∧
      (∀ L, L ≠ op.nr → T'.z.next L = T.z.next L ∧ T'.z.now L = T.z.now L) := by
  cases h with
  | rein =>
      rename_i hst
      cases hst with
      | sperre => rename_i hl; exact hl.elim
  | tritt n k ρ L m h ho hz he =>
      exact ⟨rfl, fun K hK => if_neg hK, fun K hK => ⟨rfl, rfl⟩⟩
  | gibt n k ρ L h ho hh =>
      exact ⟨rfl, fun K hK => if_neg hK, fun K hK => ⟨rfl, aendere_ne _ _ _ _ hK⟩⟩

/-- Configurations of the inlined program reachable from `T0`. -/
inductive ErreichbarT (E : CEinheit) (T0 : KonfT) : KonfT → Prop where
  | start : ErreichbarT E T0 T0
  | schritt {T T' : KonfT} {t : Faden} {ℓ : Etikett} (h : ErreichbarT E T0 T)
      (hs : SchrittT E T t ℓ T') : ErreichbarT E T0 T'

/-- A run of `n` steps of the inlined program, by index. -/
def LaufT (E : CEinheit) (T0 : KonfT) (ks : Nat → KonfT) (ts : Nat → Faden)
    (ls : Nat → Etikett) (n : Nat) : Prop :=
  ks 0 = T0 ∧ ∀ i, i < n → SchrittT E (ks i) (ts i) (ls i) (ks (i + 1))

theorem laufT_erreichbar {E : CEinheit} {T0 : KonfT} {ks : Nat → KonfT} {ts : Nat → Faden}
    {ls : Nat → Etikett} {n : Nat} (hl : LaufT E T0 ks ts ls n) :
    ∀ i, i ≤ n → ErreichbarT E T0 (ks i)
  | 0, _ => by rw [hl.1]; exact .start
  | i + 1, hi => .schritt (laufT_erreichbar hl i (by omega)) (hl.2 i (by omega))

/-- A run extended by one step at its end. -/
theorem laufT_snoc {E : CEinheit} {T0 : KonfT} {ks : Nat → KonfT} {ts : Nat → Faden}
    {ls : Nat → Etikett} {n : Nat} (hl : LaufT E T0 ks ts ls n) {t : Faden} {ℓ : Etikett}
    {T' : KonfT} (hs : SchrittT E (ks n) t ℓ T') :
    LaufT E T0 (fun i => if i ≤ n then ks i else T') (fun i => if i < n then ts i else t)
      (fun i => if i < n then ls i else ℓ) (n + 1) := by
  refine ⟨by simp only [Nat.zero_le, if_true]; exact hl.1, fun i hi => ?_⟩
  by_cases hin : i < n
  · simp only [if_pos (Nat.le_of_lt hin), if_pos hin, if_pos (show i + 1 ≤ n by omega)]
    exact hl.2 i hin
  · have e : i = n := by omega
    subst e
    simp only [Nat.le_refl, if_true, Nat.lt_irrefl, if_false, show ¬ (i + 1 ≤ i) by omega]
    exact hs

/-- Every instruction of the lock keeps the invariant. -/
theorem schrittT_inv {E : CEinheit} {T T' : KonfT} {t : Faden} {ℓ : Etikett} (hI : TInv T.z)
    (h : SchrittT E T t ℓ T') : TInv T'.z := by
  cases h with
  | rein => exact hI
  | zieht n k ρ L _ _ hz => exact tinv_schritt hI (.zieht T.z t L hz)
  | dreht => exact hI
  | tritt n k ρ L m _ _ hz he => exact tinv_schritt hI (.tritt T.z t L m hz he)
  | gibt n k ρ L _ _ hh => exact tinv_schritt hI (.gibt T.z t L hh)

/-- **THE PROJECTION**: an instruction of the lock that does not complete a
    call is a STUTTER (the C configuration does not move), and everything
    else is a step of the abstract semantics with the specified lock. -/
theorem schrittT_proj {E : CEinheit} {T T' : KonfT} {t : Faden} {ℓ : Etikett} (hI : TInv T.z)
    (hA : AbsT T.z T.k.halter) (h : SchrittT E T t ℓ T') :
    (T'.k = T.k ∧ ℓ = .still) ∨ SchrittC E sperrAbstrakt T.k t ℓ T'.k := by
  cases h with
  | rein => rename_i hst; exact Or.inr (keinLP_mono hst)
  | zieht => exact Or.inl ⟨rfl, rfl⟩
  | dreht => exact Or.inl ⟨rfl, rfl⟩
  | tritt n k ρ L m h ho hz he =>
      refine Or.inr (SchrittC.sperre T.k t n k ρ (.nimm L) _ h ho ?_)
      exact ⟨abs_frei hA (tritt_frei hI hz he), rfl⟩
  | gibt n k ρ L h ho hh =>
      refine Or.inr (SchrittC.sperre T.k t n k ρ (.gib L) _ h ho ?_)
      exact ⟨(hA L t).mpr hh, rfl⟩

/-- The abstraction stays in step with the concrete lock state. -/
theorem schrittT_abs {E : CEinheit} {T T' : KonfT} {t : Faden} {ℓ : Etikett} (hI : TInv T.z)
    (hA : AbsT T.z T.k.halter) (h : SchrittT E T t ℓ T') : AbsT T'.z T'.k.halter := by
  cases h with
  | rein =>
      rename_i hst
      rw [keinLP_halter hst]
      exact hA
  | zieht n k ρ L _ _ hz => exact hA
  | dreht => exact hA
  | tritt n k ρ L m h ho hz he => exact abs_tritt hA (tritt_frei hI hz he)
  | gibt n k ρ L h ho hh => exact abs_gibt hI hA hh

/-- **A THREAD WHOSE TICKET IS NOT SERVED CAN ONLY SPIN.** It is inside
    `L_nimm`, so it takes no step of the program; its ticket is not `now`, so
    the acquire does not complete; it holds nothing, so it cannot release.
    Every step it can take leaves the C configuration where it was. This is
    what "blocked on the lock" means for a SPINLOCK -- the thread is not
    stuck, it is busy, and the difference is invisible to `SchrittC`. -/
theorem spinnt_nur {E : CEinheit} {T : KonfT} {t : Faden} {L m : Nat}
    (hz : T.z.zieht t = some (L, m)) (hne : T.z.now L ≠ m)
    (hfrei : ∀ K, K ∉ T.z.haelt t) (ℓ : Etikett) (T' : KonfT) (hs : SchrittT E T t ℓ T') :
    T'.k = T.k ∧ ℓ = .still := by
  cases hs with
  | rein => rename_i hzn hst; rw [hz] at hzn; cases hzn
  | zieht => rename_i hc ho hzn; rw [hz] at hzn; cases hzn
  | dreht => exact ⟨rfl, rfl⟩
  | tritt =>
      rename_i L' m' hc ho hz' he
      rw [hz] at hz'
      have hp := Option.some.inj hz'
      have eL : L' = L := (congrArg Prod.fst hp).symm
      have em : m' = m := (congrArg Prod.snd hp).symm
      rw [eL, em] at he
      exact absurd he hne
  | gibt => rename_i hc ho hh; exact absurd hh (hfrei _)

/-- **EVERY CONFIGURATION THE INLINED PROGRAM REACHES, THE ABSTRACT SEMANTICS
    REACHES TOO** -- and the invariant and the abstraction hold there. The
    ticket lock adds no run to the program; it removes some (a thread whose
    ticket is not served waits where the abstract semantics would let it
    in). -/
theorem erreichbarT_erreichbarC {E : CEinheit} {T0 T : KonfT} (hI0 : TInv T0.z)
    (hA0 : AbsT T0.z T0.k.halter) (h : ErreichbarT E T0 T) :
    ErreichbarC E sperrAbstrakt T0.k T.k ∧ TInv T.z ∧ AbsT T.z T.k.halter := by
  induction h with
  | start => exact ⟨.start, hI0, hA0⟩
  | schritt hT hs ih =>
      obtain ⟨hE, hI, hA⟩ := ih
      refine ⟨?_, schrittT_inv hI hs, schrittT_abs hI hA hs⟩
      rcases schrittT_proj hI hA hs with ⟨he, -⟩ | hc
      · rw [he]; exact hE
      · exact .schritt hE hc

/-- **MUTUAL EXCLUSION ON EVERY REACHABLE CONFIGURATION** of the C program
    with the runtime's ticket lock inlined. -/
theorem erreichbarT_exklusiv {E : CEinheit} {T0 T : KonfT} (hI0 : TInv T0.z)
    (hA0 : AbsT T0.z T0.k.halter) (h : ErreichbarT E T0 T) {t u : Faden} {L : Nat}
    (ht : L ∈ T.z.haelt t) (hu : L ∈ T.z.haelt u) : t = u :=
  ticket_ausschluss (erreichbarT_erreichbarC hI0 hA0 h).2.1 ht hu

/-- **The start of the runtime's locks**: both counters at zero, no ticket
    drawn, no lock held. -/
def zStart : TZust := ⟨fun _ => 0, fun _ => 0, fun _ => none, fun _ => []⟩

theorem zStart_inv : TInv zStart where
  wort := fun _ => Nat.le_refl 0
  eindeutig := fun _ _ _ _ h => by cases h
  bereich := fun _ _ _ h => by cases h
  halter := fun _ _ h => absurd h List.not_mem_nil
  exklusiv := fun _ _ _ h => absurd h List.not_mem_nil

theorem zStart_abs {h : Halter} (hf : ∀ L, h L = none) : AbsT zStart h := by
  intro L t
  rw [hf L]
  exact ⟨(fun e => by cases e), fun e => absurd e List.not_mem_nil⟩

/-- The start configuration of the inlined program, for a root assignment
    `w` of the runtime. -/
def startT (E : CEinheit) (w : Faden → Option Nat) (st0 : CSt) : KonfT :=
  ⟨startC E w st0, zStart⟩

theorem startT_inv (E : CEinheit) (w : Faden → Option Nat) (st0 : CSt) :
    TInv (startT E w st0).z := zStart_inv

theorem startT_abs (E : CEinheit) (w : Faden → Option Nat) (st0 : CSt) :
    AbsT (startT E w st0).z (startT E w st0).k.halter := zStart_abs (fun _ => rfl)

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.tinv_schritt
#print axioms Gabbro.Grammatik.ticket_ausschluss
#print axioms Gabbro.Grammatik.ticket_fifo
#print axioms Gabbro.Grammatik.spinnt_nur
#print axioms Gabbro.Grammatik.tritt_frei
#print axioms Gabbro.Grammatik.ticket_nicht_wiedereintritt
#print axioms Gabbro.Grammatik.abs_eindeutig
#print axioms Gabbro.Grammatik.ticketLP_sperrAbstrakt
#print axioms Gabbro.Grammatik.ticket_frame
#print axioms Gabbro.Grammatik.ticket_mehr_als_frei
#print axioms Gabbro.Grammatik.gib_ohne_wache
#print axioms Gabbro.Grammatik.schrittT_proj
#print axioms Gabbro.Grammatik.erreichbarT_erreichbarC
#print axioms Gabbro.Grammatik.erreichbarT_exklusiv
