/-
  File:      Grammatik/Hardware/Anbieter/Region.lean
  Subject:   L1 -- THE REGION PROVIDER: the three roles `get` (reserve), `fill` (commit), `drop`
             (release) a program's pool is bound to, as a state machine with its contract.
             PLAN-HARDWARE.md section 16 (design), LLVM-BACKEND.md section 11 (audit item A1-A4).

  Simon's rule (2026-10-18): the compiler contains no system call; the memory of an arena or a thread
  stack comes from gates the USER's source declares. This file is the MODEL of what such a gate trio
  promises, so that the arena and the stack can be proved against it (`Arena.lean`). It is a LAYER:
  machine G, `Deklaration` and the goal statement are untouched (the gates are ordinary `Ax`es; the
  contract below is a NAMED HARDWARE ASSUMPTION about their joint answers, `AnbieterAnnahme`).

  State: the live reservations (address ranges, pairwise disjoint) and, per address, whether it holds
  RESIDENT memory (RAM). Events, one per role call, with the contract as the premise of each step:
    * `hole n b`   -- reserve: the answer is the range `[b, b+n)`, FRESH (disjoint from every live
                      reservation) and page aligned; it costs no resident memory;
    * `fuell lo hi`-- commit: `[lo, hi)` inside one live reservation, page aligned, becomes resident;
    * `zurueck lo hi` -- release of pages: the range inside a live reservation stops being resident,
                      the reservation stays;
    * `gib r`      -- release of a whole reservation: it ends, its pages stop being resident, and a
                      later `hole` may hand the same addresses out again.

  What is proved (every theorem has a witness below or in `Arena.lean`):
    * `gut_nach`           -- the invariant `Gut` (reservations pairwise disjoint, every resident
                              address lies in a live reservation) survives every step;
    * `hole_ram_gleich`, `hole_neu_null` -- NO RAM BEFORE USE: a reserve changes nothing resident, and
                              the new range holds no resident byte (the latter needs freshness and
                              the invariant -- that is why freshness is part of the contract);
    * `ram_gefuellt`       -- NO RAM WITHOUT A COMMIT: on every run from nothing, a resident address
                              was committed by some `fuell` of the run;
    * `lauf_gut`, `lebend_getrennt` -- two live reservations never share an address on any run;
    * planted defects: an overlapping answer, a commit outside any reservation and a reserve that
      makes pages resident are each refused or visible (`ueberlapp_verweigert`, `fuell_draussen_verweigert`,
      `hole_mit_ram_sichtbar`).
  NOT proved: that the kernel keeps the contract -- that is the pool's named assumption (user logic).

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Grammatik.Anbieter

/-- A half-open address range `[von, bis)`. -/
structure Strecke where
  von : Nat
  bis : Nat
  deriving DecidableEq, Repr

/-- The address lies in the range. -/
def Strecke.drin (r : Strecke) (a : Nat) : Prop := r.von ≤ a ∧ a < r.bis

/-- Two ranges share no address. -/
def Strecke.getrennt (r s : Strecke) : Prop := r.bis ≤ s.von ∨ s.bis ≤ r.von

theorem Strecke.getrennt_symm {r s : Strecke} (h : r.getrennt s) : s.getrennt r := by
  unfold Strecke.getrennt at *
  omega

/-- The provider's state: live reservations and the resident addresses. -/
structure Zust where
  lebend : List Strecke
  ram : Nat → Bool

/-- Nothing reserved, nothing resident. -/
def Zust.leer : Zust := ⟨[], fun _ => false⟩

/-- The events of the three roles (the answers are part of the event). -/
inductive Ereig where
  | hole (n b : Nat)
  | fuell (lo hi : Nat)
  | zurueck (lo hi : Nat)
  | gib (r : Strecke)
  deriving DecidableEq, Repr

/-- **The invariant**: live reservations are non-empty and pairwise disjoint; a resident address
    lies in a live reservation. -/
structure Gut (s : Zust) : Prop where
  heil : ∀ r ∈ s.lebend, r.von < r.bis
  getrennt : s.lebend.Pairwise Strecke.getrennt
  ramIn : ∀ a, s.ram a = true → ∃ r ∈ s.lebend, r.drin a

/-- **The contract of the three roles**, one step per call; `g` is the page (commit granule). The
    premises of each constructor ARE the contract the pool's assumption names. -/
inductive PStep (g : Nat) : Zust → Ereig → Zust → Prop where
  /-- reserve: a fresh, page-aligned, non-empty range; no resident memory is touched. -/
  | hole {s : Zust} {n b : Nat} (hn : 0 < n) (hnb : n % g = 0) (hb : b % g = 0)
      (hfrisch : ∀ r ∈ s.lebend, Strecke.getrennt ⟨b, b + n⟩ r) :
      PStep g s (.hole n b) { s with lebend := ⟨b, b + n⟩ :: s.lebend }
  /-- commit: a page-aligned range inside one live reservation becomes resident. -/
  | fuell {s : Zust} {r : Strecke} {lo hi : Nat} (hr : r ∈ s.lebend)
      (hin : r.von ≤ lo ∧ lo ≤ hi ∧ hi ≤ r.bis) (hal : lo % g = 0 ∧ hi % g = 0) :
      PStep g s (.fuell lo hi)
        { s with ram := fun a => s.ram a || (decide (lo ≤ a) && decide (a < hi)) }
  /-- release of pages: a range inside one live reservation stops being resident. -/
  | zurueck {s : Zust} {r : Strecke} {lo hi : Nat} (hr : r ∈ s.lebend)
      (hin : r.von ≤ lo ∧ lo ≤ hi ∧ hi ≤ r.bis) (hal : lo % g = 0 ∧ hi % g = 0) :
      PStep g s (.zurueck lo hi)
        { s with ram := fun a => s.ram a && !(decide (lo ≤ a) && decide (a < hi)) }
  /-- release of a whole reservation: it ends, nothing of it stays resident. -/
  | gib {s : Zust} {r : Strecke} (hr : r ∈ s.lebend) :
      PStep g s (.gib r)
        { lebend := s.lebend.erase r,
          ram := fun a => s.ram a && !(decide (r.von ≤ a) && decide (a < r.bis)) }

/-- A run: a list of events, each a step. -/
inductive Lauf (g : Nat) : Zust → List Ereig → Zust → Prop where
  | nil (s : Zust) : Lauf g s [] s
  | cons {s s' s'' : Zust} {e : Ereig} {es : List Ereig} :
      PStep g s e s' → Lauf g s' es s'' → Lauf g s (e :: es) s''

/-! ## 1. The invariant -/

theorem gut_leer : Gut Zust.leer :=
  ⟨by simp [Zust.leer], by simp [Zust.leer], by simp [Zust.leer]⟩

theorem gut_nach {g : Nat} {s s' : Zust} {e : Ereig} (hg : Gut s) (h : PStep g s e s') :
    Gut s' := by
  cases h with
  | hole hn hnb hb hfrisch =>
      refine ⟨?_, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · dsimp only
          omega
        · exact hg.heil r hr
      · simp only [List.pairwise_cons]
        exact ⟨hfrisch, hg.getrennt⟩
      · intro a ha
        obtain ⟨r, hr, hd⟩ := hg.ramIn a ha
        exact ⟨r, List.mem_cons_of_mem _ hr, hd⟩
  | fuell hr hin hal =>
      refine ⟨hg.heil, hg.getrennt, ?_⟩
      intro a ha
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
      rcases ha with ha | ⟨h1, h2⟩
      · exact hg.ramIn a ha
      · exact ⟨_, hr, by unfold Strecke.drin; omega⟩
  | zurueck hr hin hal =>
      refine ⟨hg.heil, hg.getrennt, ?_⟩
      intro a ha
      simp only [Bool.and_eq_true] at ha
      exact hg.ramIn a ha.1
  | @gib r0 hr =>
      refine ⟨?_, ?_, ?_⟩
      · intro r' hr'
        exact hg.heil r' (List.mem_of_mem_erase hr')
      · exact hg.getrennt.sublist (List.erase_sublist)
      · intro a ha
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
          decide_eq_false_iff_not] at ha
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨r', hr', hd⟩ := hg.ramIn a ha1
        have hne : r' ≠ r0 := by
          intro heq
          subst heq
          unfold Strecke.drin at hd
          rcases ha2 with h | h <;> omega
        exact ⟨r', (List.mem_erase_of_ne hne).2 hr', hd⟩

theorem lauf_gut {g : Nat} {s s' : Zust} {es : List Ereig} (hg : Gut s) (h : Lauf g s es s') :
    Gut s' := by
  induction h with
  | nil => exact hg
  | cons hs _ ih => exact ih (gut_nach hg hs)

/-- On every run from nothing, two live reservations never share an address. -/
theorem lebend_getrennt {g : Nat} {s : Zust} {es : List Ereig} (h : Lauf g Zust.leer es s) :
    s.lebend.Pairwise Strecke.getrennt :=
  (lauf_gut gut_leer h).getrennt

/-! ## 2. No RAM before use -/

/-- **A reserve changes nothing resident.** -/
theorem hole_ram_gleich {g : Nat} {s s' : Zust} {n b : Nat} (h : PStep g s (.hole n b) s') :
    ∀ a, s'.ram a = s.ram a := by
  cases h
  intro a
  rfl

/-- The number of resident bytes in `[b, b+n)`. -/
def ramZahl (s : Zust) (b n : Nat) : Nat := (List.range n).countP (fun i => s.ram (b + i))

/-- **The new reservation holds no resident byte, address by address.** From the invariant and
    freshness: a resident address lies in a live reservation, and the new range is disjoint from
    all of them. -/
theorem hole_neu_aus {g : Nat} {s s' : Zust} {n b : Nat} (hg : Gut s)
    (h : PStep g s (.hole n b) s') : ∀ a, b ≤ a → a < b + n → s'.ram a = false := by
  cases h with
  | hole hn hnb hb hfrisch =>
      intro a h1 h2
      cases hres : s.ram a with
      | false => rfl
      | true =>
          obtain ⟨r, hrm, hd⟩ := hg.ramIn a hres
          have hf := hfrisch r hrm
          unfold Strecke.getrennt at hf
          unfold Strecke.drin at hd
          simp only at hf
          omega

/-- The count form: the new reservation holds no resident byte. -/
theorem hole_neu_null {g : Nat} {s s' : Zust} {n b : Nat} (hg : Gut s)
    (h : PStep g s (.hole n b) s') : ramZahl s' b n = 0 := by
  have hp := hole_neu_aus hg h
  unfold ramZahl
  rw [List.countP_eq_zero]
  intro i hi
  simp only [List.mem_range] at hi
  have := hp (b + i) (by omega) (by omega)
  simp [this]

/-- **No RAM without a commit.** On every run from a state `s0`, an address that is resident at
    the end was resident at `s0` or lies in the range of a `fuell` of the run. -/
theorem ram_gefuellt {g : Nat} {s0 s : Zust} {es : List Ereig} (h : Lauf g s0 es s) :
    ∀ a, s.ram a = true → s0.ram a = true ∨
      ∃ lo hi, Ereig.fuell lo hi ∈ es ∧ lo ≤ a ∧ a < hi := by
  induction h with
  | nil => intro a ha; exact Or.inl ha
  | @cons s1 s2 s3 e es' hs _ ih =>
      intro a ha
      rcases ih a ha with h2 | ⟨lo, hi, hm, h1, h2⟩
      · cases hs with
        | hole => exact Or.inl h2
        | fuell hr hin hal =>
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h2
            rcases h2 with h2 | ⟨h1, h3⟩
            · exact Or.inl h2
            · exact Or.inr ⟨_, _, List.mem_cons_self .., h1, h3⟩
        | zurueck hr hin hal =>
            simp only [Bool.and_eq_true] at h2
            exact Or.inl h2.1
        | gib hr =>
            simp only [Bool.and_eq_true] at h2
            exact Or.inl h2.1
      · exact Or.inr ⟨lo, hi, List.mem_cons_of_mem _ hm, h1, h2⟩

/-- From nothing: every resident address was committed by the run. -/
theorem ram_nur_gefuellt {g : Nat} {s : Zust} {es : List Ereig} (h : Lauf g Zust.leer es s)
    (a : Nat) (ha : s.ram a = true) : ∃ lo hi, Ereig.fuell lo hi ∈ es ∧ lo ≤ a ∧ a < hi := by
  rcases ram_gefuellt h a ha with h0 | h1
  · simp [Zust.leer] at h0
  · exact h1

/-- A legal access: a resident address (which the invariant puts inside a live reservation). -/
def Zugriff (s : Zust) (a : Nat) : Prop := s.ram a = true

/-- An address no `fuell` of the run covered is never a legal access. -/
theorem kein_zugriff_ohne_fuell {g : Nat} {s : Zust} {es : List Ereig}
    (h : Lauf g Zust.leer es s) (a : Nat)
    (hn : ∀ lo hi, Ereig.fuell lo hi ∈ es → ¬ (lo ≤ a ∧ a < hi)) : ¬ Zugriff s a := by
  intro hz
  obtain ⟨lo, hi, hm, h1, h2⟩ := ram_nur_gefuellt h a hz
  exact hn lo hi hm ⟨h1, h2⟩

/-! ## 3. Planted defects and a witness -/

/-- The defect "the answer overlaps a live reservation" is refused by the contract. -/
theorem ueberlapp_verweigert (g : Nat) (s' : Zust) :
    ¬ PStep g ⟨[⟨0, 100⟩], fun _ => false⟩ (.hole 100 50) s' := by
  intro h
  cases h with
  | hole hn hnb hb hfrisch =>
      have := hfrisch ⟨0, 100⟩ (by simp)
      unfold Strecke.getrennt at this
      simp only at this
      omega

/-- The defect "commit outside every reservation" is refused. -/
theorem fuell_draussen_verweigert (g : Nat) (s' : Zust) :
    ¬ PStep g ⟨[⟨0, 100⟩], fun _ => false⟩ (.fuell 90 120) s' := by
  intro h
  cases h with
  | fuell hr hin hal =>
      simp only [List.mem_singleton] at hr
      subst hr
      simp only at hin
      omega

/-- The defect "a reserve that makes its pages resident": unchecked, it is visible as resident
    bytes right after the call (the contract's `hole_neu_null` says there are none). -/
def holeMitRam (s : Zust) (n b : Nat) : Zust :=
  { lebend := ⟨b, b + n⟩ :: s.lebend,
    ram := fun a => s.ram a || (decide (b ≤ a) && decide (a < b + n)) }

theorem hole_mit_ram_sichtbar : ramZahl (holeMitRam Zust.leer 16 32) 32 16 = 16 := by decide

/-- A run with all four roles (page 16): reserve 64, commit one page, give it back, end. -/
def zeugeLauf : List Ereig :=
  [.hole 64 32, .fuell 48 64, .zurueck 48 64, .gib ⟨32, 96⟩]

theorem zeuge_lauf_geht : ∃ s, Lauf 16 Zust.leer zeugeLauf s ∧ s.lebend = [] :=
  ⟨_, Lauf.cons
    (PStep.hole (s := Zust.leer) (n := 64) (b := 32) (by decide) (by decide) (by decide)
      (by simp [Zust.leer]))
    (Lauf.cons (PStep.fuell (r := ⟨32, 96⟩) (lo := 48) (hi := 64) (by simp) (by decide) (by decide))
    (Lauf.cons (PStep.zurueck (r := ⟨32, 96⟩) (lo := 48) (hi := 64) (by simp) (by decide) (by decide))
    (Lauf.cons (PStep.gib (r := ⟨32, 96⟩) (by simp)) (Lauf.nil _)))), rfl⟩

/-- The witness of `hole_neu_null`: the fresh range of the first reserve holds nothing. -/
theorem hole_neu_null_zeuge :
    ∃ s', PStep 16 Zust.leer (.hole 64 32) s' ∧ ramZahl s' 32 64 = 0 := by
  have h1 : PStep 16 Zust.leer (.hole 64 32)
      { lebend := [⟨32, 32 + 64⟩], ram := Zust.leer.ram } :=
    PStep.hole (s := Zust.leer) (by decide) (by decide) (by decide) (by simp [Zust.leer])
  exact ⟨_, h1, hole_neu_null gut_leer h1⟩

end Gabbro.Grammatik.Anbieter
