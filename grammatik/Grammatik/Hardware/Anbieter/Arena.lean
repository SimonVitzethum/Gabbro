import Grammatik.Hardware.Anbieter.Region
import Grammatik.Bausteine.Schablonen.SchablonenArena
import Grammatik.Bausteine.Arena.ArenaDyn

/-
  File:      Grammatik/Hardware/Anbieter/Arena.lean
  Subject:   L1 -- ARENAS AND THREAD STACKS ACQUIRE THEIR MEMORY THROUGH THE PROVIDER (`Region.lean`).
             PLAN-HARDWARE.md section 16.2.

  `arena A capacity lo .. hi max M of T from P` (proposed surface): the arena's storage is ONE
  reservation of the pool `P` (`hole`, answered fresh), grown page by page with `fuell`. The
  arithmetic of the ranges is the existing, proved template arithmetic (`ArenaLaufzeit`:
  `spanne`, `commitStart`, `commitEnde`, `arena_commit_bereich`), the committed prefix is the existing
  `DynArena` (`dynGrow`, ceiling `M`). What this file adds is the statement about RESIDENT MEMORY
  that the Linux-profile compiler had as a property of `mmap`/`mprotect` (guardian stage 2b) and
  that is now a consequence of the pool's contract:

    * `ArenaGut`           -- the arena's reservation is live; every committed slot byte is resident;
                              resident memory inside the reservation reaches no further than the
                              PAGE-ROUNDED committed prefix (the "no RAM before use" property);
    * `arena_start`        -- right after the reserve the invariant holds with an empty prefix
                              (uses `hole_neu_aus`: a fresh range holds no resident byte);
    * `arena_grow_geht`    -- `dynGrow A n = some B` is realised by ONE `fuell` of exactly the
                              template's range, that step is legal under the contract, and the
                              invariant holds for `B`;
    * `slot_resident`      -- every slot below the committed prefix is readable and writable;
    * `region_exklusiv`    -- the arena's bytes lie in no other live reservation (freshness);
    * `gib_nichts_resident`-- giving the whole reservation back leaves nothing resident.

  Thread stacks (`StapelGut`): a stack is a reservation whose lowest `gd` bytes (the GUARD) are never
  committed; the stack grows by `fuell` above the guard. An overflow into the guard is therefore an
  access to a non-resident address (a hardware stop, never a silent write), and the guard belongs to
  no other reservation (`stapel_wache_exklusiv`). Frames larger than the guard can skip it: that is the
  NOT CLAIMED stack depth of the goal statement, named in the design.

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Grammatik.Anbieter

open ArenaLaufzeit (spanne commitStart commitEnde aufrunden abrunden)
open ArenaDyn (DynArena dynGrow)

/-! ## 1. A different reservation is a different range -/

/-- Two distinct members of a pairwise disjoint list are disjoint. -/
theorem paar_aus {l : List Strecke} (hp : l.Pairwise Strecke.getrennt) {r r' : Strecke}
    (hr : r ∈ l) (hr' : r' ∈ l) (hne : r ≠ r') : Strecke.getrennt r r' := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hr
  | cons x xs ih =>
      rw [List.pairwise_cons] at hp
      obtain ⟨hx, hxs⟩ := hp
      simp only [List.mem_cons] at hr hr'
      rcases hr with rfl | hr <;> rcases hr' with rfl | hr'
      · exact absurd rfl hne
      · exact hx _ hr'
      · exact Strecke.getrennt_symm (hx _ hr)
      · exact ih hxs hr hr'

/-- Two distinct live reservations share no address. -/
theorem region_exklusiv {s : Zust} (hg : Gut s) {r r' : Strecke} (hr : r ∈ s.lebend)
    (hr' : r' ∈ s.lebend) (hne : r ≠ r') (a : Nat) (ha : r.drin a) : ¬ r'.drin a := by
  have := paar_aus hg.getrennt hr hr' hne
  unfold Strecke.getrennt at this
  unfold Strecke.drin at *
  omega

/-! ## 2. The arena through the provider -/

/-- The reservation of an arena of ceiling `M`, `elem`-byte slots, page `g`, at base `b`. -/
def arenaStrecke (elem g b M : Nat) : Strecke := ⟨b, b + spanne elem M g⟩

/-- **The arena invariant** over the provider state. -/
structure ArenaGut (elem g b : Nat) (A : DynArena) (s : Zust) : Prop where
  lebt : arenaStrecke elem g b A.M ∈ s.lebend
  voll : ∀ a, b ≤ a → a < b + A.c * elem → s.ram a = true
  huelle : ∀ a, b ≤ a → a < b + spanne elem A.M g → s.ram a = true →
    a < b + aufrunden (A.c * elem) g

theorem dynGrow_felder {A B : DynArena} {n : Nat} (h : dynGrow A n = some B) :
    B.M = A.M ∧ B.c = A.c + n ∧ A.c + n ≤ A.M := by
  unfold dynGrow at h
  split at h
  · rename_i hle
    cases h
    exact ⟨rfl, rfl, hle⟩
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- **The start.** The reserve answers the arena's span; the invariant holds with an empty
    prefix: the fresh range holds nothing resident. -/
theorem arena_start {g elem b : Nat} {s s' : Zust} (A : DynArena) (hc : A.c = 0) (hg : Gut s)
    (h : PStep g s (.hole (spanne elem A.M g) b) s') : ArenaGut elem g b A s' := by
  have hp := hole_neu_aus hg h
  refine ⟨?_, ?_, ?_⟩
  · cases h
    unfold arenaStrecke
    exact List.mem_cons_self ..
  · intro a h1 h2
    rw [hc] at h2
    omega
  · intro a h1 h2 h3
    have := hp a h1 h2
    rw [this] at h3
    exact absurd h3 (by simp only [Bool.false_eq_true, not_false_eq_true])

/-- **A grow is one commit of the template's range.** `dynGrow A n = some B` (the ceiling is kept)
    is realised by a `fuell` of `[b + commitStart, b + commitEnde)`: legal under the contract,
    and the invariant holds for `B`. -/
theorem arena_grow_geht {g elem b : Nat} {A B : DynArena} {s : Zust} (hg0 : 0 < g)
    (hb : b % g = 0) (hA : ArenaGut elem g b A s) (n : Nat) (hB : dynGrow A n = some B) :
    ∃ s', PStep g s (.fuell (b + commitStart elem A.c g) (b + commitEnde elem A.c n g)) s' ∧
      ArenaGut elem g b B s' := by
  obtain ⟨hM, hBc, hn⟩ := dynGrow_felder hB
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := ArenaLaufzeit.arena_commit_bereich elem A.M A.c n g hg0 hn
  have hal : (b + commitStart elem A.c g) % g = 0 ∧ (b + commitEnde elem A.c n g) % g = 0 := by
    constructor
    · rw [Nat.add_mod, hb, e5]; simp only [Nat.add_zero, Nat.zero_mod]
    · rw [Nat.add_mod, hb, e6]; simp only [Nat.add_zero, Nat.zero_mod]
  have hlive : arenaStrecke elem g b A.M ∈ s.lebend := hA.lebt
  have hstep := PStep.fuell (g := g) (s := s) (r := arenaStrecke elem g b A.M)
    (lo := b + commitStart elem A.c g) (hi := b + commitEnde elem A.c n g) hlive
    (by unfold arenaStrecke; simp only; omega) hal
  refine ⟨_, hstep, ?_, ?_, ?_⟩
  · show arenaStrecke elem g b B.M ∈ s.lebend
    rw [hM]
    exact hlive
  · intro a h1 h2
    rw [hBc] at h2
    show (s.ram a || (decide (b + commitStart elem A.c g ≤ a) &&
      decide (a < b + commitEnde elem A.c n g))) = true
    by_cases hlt : a < b + A.c * elem
    · simp only [hA.voll a h1 hlt, Bool.true_or]
    · have h3 : b + commitStart elem A.c g ≤ a := by omega
      have h4 : a < b + commitEnde elem A.c n g := by
        have : (A.c + n) * elem ≤ commitEnde elem A.c n g := e2
        omega
      simp only [h3, decide_true, h4, Bool.and_self, Bool.or_true]
  · intro a h1 h2 h3
    rw [hM] at h2
    rw [hBc]
    have h3' : (s.ram a || (decide (b + commitStart elem A.c g ≤ a) &&
      decide (a < b + commitEnde elem A.c n g))) = true := h3
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h3'
    rcases h3' with h3' | ⟨-, h4⟩
    · have := hA.huelle a h1 h2 h3'
      have hm := ArenaLaufzeit.aufrunden_mono (A.c * elem) ((A.c + n) * elem) g
        (Nat.mul_le_mul_right _ (by omega))
      omega
    · unfold commitEnde at h4
      exact h4

/-- Every slot below the committed prefix is resident, byte for byte. -/
theorem slot_resident {g elem b : Nat} {A : DynArena} {s : Zust} (hA : ArenaGut elem g b A s)
    (i : Nat) (hi : i < A.c) (a : Nat) (h1 : b + i * elem ≤ a) (h2 : a < b + (i + 1) * elem) :
    s.ram a = true := by
  have hm : (i + 1) * elem ≤ A.c * elem := Nat.mul_le_mul_right _ hi
  exact hA.voll a (by omega) (by omega)

/-- Every slot below the committed prefix lies inside the arena's reservation (ceiling `M`). -/
theorem slot_in_region {g elem : Nat} (A : DynArena) (hg0 : 0 < g) (i : Nat) (hi : i < A.c) :
    (i + 1) * elem ≤ spanne elem A.M g := by
  have h1 : (i + 1) * elem ≤ A.M * elem := Nat.mul_le_mul_right _ (by have := A.hceil; omega)
  have h2 := ArenaLaufzeit.le_aufrunden (A.M * elem) g hg0
  unfold spanne
  omega

/-- **The arena's bytes belong to this arena alone**: no other live reservation contains them. -/
theorem arena_exklusiv {g elem b : Nat} {A : DynArena} {s : Zust} (hg : Gut s)
    (hA : ArenaGut elem g b A s) {r' : Strecke} (hr' : r' ∈ s.lebend)
    (hne : arenaStrecke elem g b A.M ≠ r') (a : Nat) (h1 : b ≤ a)
    (h2 : a < b + spanne elem A.M g) : ¬ r'.drin a :=
  region_exklusiv hg hA.lebt hr' hne a (by unfold arenaStrecke Strecke.drin; simp only; omega)

/-- Giving a reservation back leaves none of its addresses resident. -/
theorem gib_nichts_resident {g : Nat} {s s' : Zust} {r : Strecke} (h : PStep g s (.gib r) s')
    (a : Nat) (ha : r.drin a) : s'.ram a = false := by
  cases h
  unfold Strecke.drin at ha
  simp only [ha.1, decide_true, ha.2, Bool.and_self, Bool.not_true, Bool.and_false]

/-- **The planted defect: a grow past the ceiling.** One slot beyond `M = 8` of 512-byte slots on
    4096-byte pages asks for a commit past the reservation; the contract refuses it (the caller's
    `dynGrow` is `none` there, `dynGrow_ueber_M`, so the template never issues it). -/
theorem grow_ueber_decke_verweigert (s' : Zust) :
    ¬ PStep 4096 ⟨[arenaStrecke 512 4096 4096 8], fun _ => false⟩
      (.fuell (4096 + commitStart 512 8 4096) (4096 + commitEnde 512 8 1 4096)) s' := by
  intro h
  cases h with
  | fuell hr hin hal =>
      simp only [List.mem_singleton] at hr
      subst hr
      have e : commitEnde 512 8 1 4096 = 8192 := by decide
      have e2 : spanne 512 8 4096 = 4096 := by decide
      unfold arenaStrecke at hin
      rw [e, e2] at hin
      simp only at hin
      omega

/-! ## 3. The thread stack through the provider -/

/-- A stack: a live reservation `[b, b+n)` whose lowest `gd` bytes (the guard) are not resident. -/
structure StapelGut (b n gd : Nat) (s : Zust) : Prop where
  lebt : (⟨b, b + n⟩ : Strecke) ∈ s.lebend
  wache : ∀ a, b ≤ a → a < b + gd → s.ram a = false

/-- Right after the reserve the stack stands with its guard clean. -/
theorem stapel_start {g b n gd : Nat} {s s' : Zust} (hg : Gut s) (hgn : gd ≤ n)
    (h : PStep g s (.hole n b) s') : StapelGut b n gd s' := by
  have hp := hole_neu_aus hg h
  refine ⟨?_, ?_⟩
  · cases h
    exact List.mem_cons_self ..
  · intro a h1 h2
    exact hp a h1 (by omega)

/-- **The stack grows above the guard**: a commit that starts at or above `b + gd` keeps the guard
    clean. -/
theorem stapel_waechst {g b n gd lo hi : Nat} {s s' : Zust} (hS : StapelGut b n gd s)
    (hlo : b + gd ≤ lo) (h : PStep g s (.fuell lo hi) s') : StapelGut b n gd s' := by
  cases h with
  | fuell hr hin hal =>
      refine ⟨hS.lebt, ?_⟩
      intro a h1 h2
      show (s.ram a || (decide (lo ≤ a) && decide (a < hi))) = false
      have h3 : ¬ lo ≤ a := by omega
      simp only [hS.wache a h1 h2, h3, decide_false, Bool.false_and, Bool.or_self]

/-- **An overflow into the guard is a stop, not a write**: the guard is not a legal access. -/
theorem stapel_wache_kein_zugriff {b n gd : Nat} {s : Zust} (hS : StapelGut b n gd s)
    (a : Nat) (h1 : b ≤ a) (h2 : a < b + gd) : ¬ Zugriff s a := by
  intro hz
  have := hS.wache a h1 h2
  unfold Zugriff at hz
  rw [this] at hz
  exact absurd hz (by simp only [Bool.false_eq_true, not_false_eq_true])

/-- The guard (inside the stack's reservation) belongs to no other live reservation. -/
theorem stapel_wache_exklusiv {b n gd : Nat} {s : Zust} (hg : Gut s) (hS : StapelGut b n gd s)
    (hgn : gd ≤ n) {r' : Strecke} (hr' : r' ∈ s.lebend) (hne : (⟨b, b + n⟩ : Strecke) ≠ r')
    (a : Nat) (h1 : b ≤ a) (h2 : a < b + gd) : ¬ r'.drin a :=
  region_exklusiv hg hS.lebt hr' hne a (by unfold Strecke.drin; simp only; omega)

/-- **The planted defect: a commit that starts inside the guard** makes the guard resident, and
    the next overflow then writes silently. -/
theorem fuell_in_wache_bricht :
    ((⟨[⟨64, 64 + 128⟩], fun _ => false⟩ : Zust).ram 64 = false) ∧
    (∃ s', PStep 16 ⟨[⟨64, 64 + 128⟩], fun _ => false⟩ (.fuell 64 80) s' ∧ s'.ram 64 = true) := by
  refine ⟨rfl, _, PStep.fuell (r := ⟨64, 64 + 128⟩) (by simp only [Nat.reduceAdd, List.mem_cons, List.not_mem_nil, or_false]) (by decide) (by decide), rfl⟩

/-! ## 4. Witness: an arena of six 8-byte slots on 16-byte pages -/

/-- Ceiling 6, floor 0, nothing committed. -/
def arenaA0 : DynArena := ⟨6, 0, 0, by decide, by decide, by decide⟩

/-- **Witness for `arena_start`, `arena_grow_geht`, `slot_resident` and the page-rounded bound**,
    all premises jointly: reserve 48 bytes at 32, grow by 2 slots, then by 1. After the second
    grow slot 2 is resident, and the address 70 (past the page-rounded prefix of 3 slots = 24
    bytes -> 32) is not. The two commit ranges are the template's: `[32,48)` and `[48,64)`. -/
theorem arena_zeuge :
    ∃ (s1 s2 s3 : Zust) (A2 A3 : DynArena),
      PStep 16 Zust.leer (.hole (spanne 8 6 16) 32) s1 ∧
      dynGrow arenaA0 2 = some A2 ∧
      PStep 16 s1 (.fuell (32 + commitStart 8 0 16) (32 + commitEnde 8 0 2 16)) s2 ∧
      dynGrow A2 1 = some A3 ∧
      PStep 16 s2 (.fuell (32 + commitStart 8 A2.c 16) (32 + commitEnde 8 A2.c 1 16)) s3 ∧
      ArenaGut 8 16 32 A3 s3 ∧ A3.c = 3 ∧ s3.ram (32 + 2 * 8) = true ∧ s3.ram 70 = false := by
  have hs1 : PStep 16 Zust.leer (.hole (spanne 8 6 16) 32)
      { lebend := [⟨32, 32 + spanne 8 6 16⟩], ram := Zust.leer.ram } :=
    PStep.hole (s := Zust.leer) (by decide) (by decide) (by decide) (by simp only [Zust.leer, List.not_mem_nil, false_implies, implies_true])
  have hA0 : ArenaGut 8 16 32 arenaA0
      { lebend := [⟨32, 32 + spanne 8 6 16⟩], ram := Zust.leer.ram } :=
    arena_start arenaA0 rfl gut_leer hs1
  have hsome2 : (dynGrow arenaA0 2).isSome = true := by decide
  obtain ⟨A2, hA2⟩ := Option.isSome_iff_exists.mp hsome2
  obtain ⟨s2, hst2, hG2⟩ := arena_grow_geht (by decide) (by decide) hA0 2 hA2
  have hc2 : A2.c = 2 := (dynGrow_felder hA2).2.1
  have hsome3 : (dynGrow A2 1).isSome = true := by
    have h := (dynGrow_felder hA2)
    unfold dynGrow
    have : A2.c + 1 ≤ A2.M := by
      have := (dynGrow_felder hA2).1
      rw [hc2, this]; decide
    simp only [this, ↓reduceDIte, Option.isSome_some]
  obtain ⟨A3, hA3⟩ := Option.isSome_iff_exists.mp hsome3
  obtain ⟨s3, hst3, hG3⟩ := arena_grow_geht (by decide) (by decide) hG2 1 hA3
  have hc3 : A3.c = 3 := by
    have := (dynGrow_felder hA3).2.1
    omega
  refine ⟨_, s2, s3, A2, A3, hs1, ?_, ?_, hA3, hst3, hG3, hc3, ?_, ?_⟩
  · exact hA2
  · exact hst2
  · have := slot_resident hG3 2 (by omega) (32 + 2 * 8) (by omega) (by omega)
    exact this
  · have hh := hG3.huelle 70 (by omega) (by
      have := (dynGrow_felder hA3).1
      have := (dynGrow_felder hA2).1
      show 70 < 32 + spanne 8 A3.M 16
      rw [‹A3.M = A2.M›, ‹A2.M = arenaA0.M›]
      decide)
    cases hr : s3.ram 70 with
    | false => rfl
    | true =>
        have := hh hr
        rw [hc3] at this
        revert this
        decide

end Gabbro.Grammatik.Anbieter
