module

public import Grammatik.Speichermodell.Maschine.Sicht.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Speichermodell
open Befehl LOrt Ordnung

theorem sbInv_start : SBInv (LZustand.start LOrt) where
  xOben _ _ _ h := by simp only [LZustand.start, Nat.le_zero_eq, Nat.succ_ne_self] at h
  yOben _ _ _ h := by simp only [LZustand.start, Nat.le_zero_eq, Nat.succ_ne_self] at h
  r0 h := by simp only [LZustand.start, Nat.le_zero_eq, reduceCtorEq] at h

/-- The newest message after an appending write is the written one. -/
theorem oben_neu {hist : List (Nachricht LOrt Int)} {n m : Nachricht LOrt Int}
    (hoben : ∀ m' ∈ hist, m'.ts < n.ts) (hm : m ∈ n :: hist)
    (hmax : ∀ m' ∈ n :: hist, m'.ts ≤ m.ts) : m = n := by
  rcases List.mem_cons.mp hm with h | h
  · exact h
  · have h1 := hoben m h
    have h2 := hmax n List.mem_cons_self
    omega

theorem sbInv_schritt {Z Z' : LZustand LOrt} (hI : SBInv Z) (hs : LSchrittSC sbRA Z Z') :
    SBInv Z' := by
  cases hs with
  | schreib t xo w o ts hb hf hoben =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨_, hc⟩
        · obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m hm hmax _
            simp only [LZustand.nachSchreib, aufO_gleich] at hm hmax
            rw [oben_neu (n := nachricht .freigabe (Z.sicht 0) .x ts 1) hoben hm hmax]
            rfl
          · intro m hm hmax h
            simp only [LZustand.nachSchreib, aufO_anders _ _ (show LOrt.y ≠ LOrt.x by decide),
              aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at hm hmax h
            exact hI.yOben m hm hmax h
          · intro h
            simp only [LZustand.nachSchreib, hpc, Nat.zero_add, aufN, ↓reduceIte, Nat.reduceLeDiff] at h
        · cases hc
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨_, hc⟩
        · obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m hm hmax h
            simp only [LZustand.nachSchreib, aufO_anders _ _ (show LOrt.x ≠ LOrt.y by decide),
              aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)] at hm hmax h
            exact hI.xOben m hm hmax h
          · intro m hm hmax _
            simp only [LZustand.nachSchreib, aufO_gleich] at hm hmax
            rw [oben_neu (n := nachricht .freigabe (Z.sicht 1) .y ts 1) hoben hm hmax]
            rfl
          · intro _ _ h
            simp only [LZustand.nachSchreib, hpc, Nat.zero_add, aufN, ↓reduceIte, Nat.reduceLeDiff] at h
        · cases hc
  | lies t xo r o m hb hl hoben =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨hpc, hc⟩
        · cases hc
        · -- thread 0 reads the newest `y`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m' hm hmax h
            simp only [LZustand.nachLies] at hm hmax h
            exact hI.xOben m' hm hmax (by simp only [aufN, ↓reduceIte, Nat.le_add_left] at h; omega)
          · intro m' hm hmax h
            simp only [LZustand.nachLies, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)] at hm hmax h
            exact hI.yOben m' hm hmax h
          · intro _ h0 h1
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)]
              at h0 h1
            have hy := hI.yOben m hl.1 hoben (by omega)
            rw [hy] at h0
            exact absurd h0 (by decide)
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨hpc, hc⟩
        · cases hc
        · -- thread 1 reads the newest `x`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨?_, ?_, ?_⟩
          · intro m' hm hmax h
            simp only [LZustand.nachLies, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)] at hm hmax h
            exact hI.xOben m' hm hmax h
          · intro m' hm hmax h
            simp only [LZustand.nachLies] at hm hmax h
            exact hI.yOben m' hm hmax (by simp only [aufN, ↓reduceIte, Nat.le_add_left] at h; omega)
          · intro h2 _ _
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
              at h2 ⊢
            exact hI.xOben m hl.1 hoben (by omega)

theorem sbInv_erreichbar {Z : LZustand LOrt} (h : LErreichbar (LSchrittSC sbRA) Z) : SBInv Z := by
  induction h with
  | start => exact sbInv_start
  | schritt _ hs ih => exact sbInv_schritt ih hs

/-- **SB on the SC machine: both reads 0 is NOT reachable.** Together with `sb_erlaubt` this
    shows that the weak machine has behaviours the SC machine does not. -/
theorem sb_sc_verboten {Z : LZustand LOrt} (h : LErreichbar (LSchrittSC sbRA) Z)
    (h0 : Z.pc 0 = 2) (h1 : Z.pc 1 = 2) : ¬ (Z.reg 0 0 = 0 ∧ Z.reg 1 0 = 0) := by
  rintro ⟨r0, r1⟩
  have := (sbInv_erreichbar h).r0 (by omega) r0 (by omega)
  rw [r1] at this
  exact absurd this (by decide)

/-- Every SC run is a weak run. -/
theorem lErreichbar_sc_schwach {prog : Nat → List (Befehl LOrt)} {Z : LZustand LOrt}
    (h : LErreichbar (LSchrittSC prog) Z) : LErreichbar (LSchritt prog) Z := by
  induction h with
  | start => exact .start
  | schritt _ hs ih => exact .schritt ih (lSchrittSC_schwach hs)

/-! ## 7. Coherence read-read: FORBIDDEN on the weak machine -/

/-- `CoRR`. Thread 0: `x := 1`; `x := 2` (relaxed). Thread 1: `r0 := x`; `r1 := x` (relaxed). -/
def coRR : Nat → List (Befehl LOrt) :=
  zwei [schreib .x 1 .entspannt, schreib .x 2 .entspannt] [lies .x 0 .entspannt, lies .x 1 .entspannt]

/-- The invariant of `coRR`. -/
structure CoInv (Z : LZustand LOrt) : Prop where
  ordnung : ∀ m ∈ Z.hist .x, m.wert = 1 → ∀ m' ∈ Z.hist .x, m'.wert = 2 → m.ts < m'.ts
  t0 : ∀ m ∈ Z.hist .x, m.wert = 1 → m.ts ≤ Z.sicht 0 .x
  zwei0 : ∀ m ∈ Z.hist .x, m.wert = 2 → 2 ≤ Z.pc 0
  eins0 : ∀ m ∈ Z.hist .x, m.wert = 1 → 1 ≤ Z.pc 0
  gesehen : 1 ≤ Z.pc 1 → Z.reg 1 0 = 2 → ∃ m ∈ Z.hist .x, m.wert = 2
  t1 : 1 ≤ Z.pc 1 → Z.reg 1 0 = 2 → ∀ m ∈ Z.hist .x, m.wert = 1 → m.ts < Z.sicht 1 .x
  r1 : 2 ≤ Z.pc 1 → Z.reg 1 0 = 2 → Z.reg 1 1 ≠ 1

theorem coInv_start : CoInv (LZustand.start LOrt) where
  ordnung m hm h := by simp only [LZustand.start, List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; simp only [Int.reduceEq] at h
  t0 m hm h := by simp only [LZustand.start, List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; simp only [Int.reduceEq] at h
  zwei0 m hm h := by simp only [LZustand.start, List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; simp only [Int.reduceEq] at h
  eins0 m hm h := by simp only [LZustand.start, List.mem_cons, List.not_mem_nil, or_false] at hm; subst hm; simp only [Int.reduceEq] at h
  gesehen h := by simp only [LZustand.start, Nat.le_zero_eq, Nat.succ_ne_self] at h
  t1 h := by simp only [LZustand.start, Nat.le_zero_eq, Nat.succ_ne_self] at h
  r1 h := by simp only [LZustand.start, Nat.le_zero_eq, reduceCtorEq] at h

theorem coInv_schritt {Z Z' : LZustand LOrt} (hI : CoInv Z) (hs : LSchritt coRR Z Z') :
    CoInv Z' := by
  cases hs with
  | schreib t xo w o ts hb hf =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨hpc, hc⟩
        · -- `x := 1`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          have kein2 : ∀ m ∈ Z.hist .x, m.wert ≠ 2 := fun m hm h => by
            have := hI.zwei0 m hm h; omega
          have kein1 : ∀ m ∈ Z.hist .x, m.wert ≠ 1 := fun m hm h => by
            have := hI.eins0 m hm h; omega
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [LZustand.nachSchreib, aufO_gleich, aufN_gleich,
              aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)]
          · intro m hm h1 m' hm' h2
            rcases List.mem_cons.mp hm' with rfl | hm'
            · simp only [nachricht, Int.reduceEq] at h2
            · exact absurd h2 (kein2 m' hm')
          · intro m hm h1
            rcases List.mem_cons.mp hm with rfl | hm
            · simp only [nachricht, Sicht.setze_selbst, Std.le_refl]
            · exact absurd h1 (kein1 m hm)
          · intro m hm h2
            rcases List.mem_cons.mp hm with rfl | hm
            · simp only [nachricht, Int.reduceEq] at h2
            · exact absurd h2 (kein2 m hm)
          · intro _ _ _; simp only [Nat.le_add_left]
          · intro h h'
            obtain ⟨m, hm, h2⟩ := hI.gesehen h h'
            exact absurd h2 (kein2 m hm)
          · intro h h'
            obtain ⟨m, hm, h2⟩ := hI.gesehen h h'
            exact absurd h2 (kein2 m hm)
          · exact hI.r1
        · -- `x := 2`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_schreib_inj hc
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [LZustand.nachSchreib, aufO_gleich, aufN_gleich,
              aufN_anders _ _ (show (1 : Nat) ≠ 0 by decide)]
          · intro m hm h1 m' hm' h2
            rcases List.mem_cons.mp hm with rfl | hm
            · simp only [nachricht, Int.reduceEq] at h1
            · rcases List.mem_cons.mp hm' with rfl | hm'
              · have := hI.t0 m hm h1
                have := hf.1
                simp only [nachricht]
                omega
              · exact hI.ordnung m hm h1 m' hm' h2
          · intro m hm h1
            rcases List.mem_cons.mp hm with rfl | hm
            · simp only [nachricht, Int.reduceEq] at h1
            · have := hI.t0 m hm h1
              have := hf.1
              rw [Sicht.setze_selbst]
              omega
          · intro _ _ _; simp only [hpc, Nat.reduceAdd, Std.le_refl]
          · intro _ _ _; simp only [hpc, Nat.reduceAdd, Nat.reduceLeDiff]
          · intro h h'
            obtain ⟨m, hm, h2⟩ := hI.gesehen h h'
            exact ⟨m, List.mem_cons_of_mem _ hm, h2⟩
          · intro h h' m hm h1
            rcases List.mem_cons.mp hm with rfl | hm
            · simp only [nachricht, Int.reduceEq] at h1
            · exact hI.t1 h h' m hm h1
          · exact hI.r1
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨_, hc⟩ <;> cases hc
  | lies t xo r o m hb hl =>
      rcases zwei_fall hb with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
      · rcases zwei_befehle hb with ⟨_, hc⟩ | ⟨_, hc⟩ <;> cases hc
      · rcases zwei_befehle hb with ⟨hpc, hc⟩ | ⟨hpc, hc⟩
        · -- `r0 := x`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          refine ⟨hI.ordnung, hI.t0, hI.zwei0, hI.eins0, ?_, ?_, ?_⟩ <;>
            simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
          · intro _ h'
            try simp [aufN] at h'
            exact ⟨m, hl.1, h'⟩
          · intro _ h' m1 hm1 h1
            try simp [aufN] at h'
            have h2 := hI.ordnung m1 hm1 h1 m hl.1 h'
            exact Nat.lt_of_lt_of_le h2 (Nat.le_trans (beitrag_selbst _ _ _)
              (Sicht.verein_rechts _ _ LOrt.x))
          · intro h; simp only [hpc, Nat.zero_add, Nat.reduceLeDiff] at h
        · -- `r1 := x`
          obtain ⟨rfl, rfl, rfl⟩ := befehl_lies_inj hc
          simp only [LZustand.nachLies, aufN_gleich, aufN_anders _ _ (show (0 : Nat) ≠ 1 by decide)]
          have hpc1 : 1 ≤ Z.pc 1 := by omega
          refine ⟨hI.ordnung, hI.t0, hI.zwei0, hI.eins0, ?_, ?_, ?_⟩
          · intro _ h'
            simp only [aufN, ↓reduceIte, Nat.zero_ne_one] at h'
            exact hI.gesehen hpc1 h'
          · intro _ h' m1 hm1 h1
            simp only [aufN, ↓reduceIte, Nat.zero_ne_one] at h'
            exact Nat.lt_of_lt_of_le (hI.t1 hpc1 h' m1 hm1 h1) (Sicht.verein_links _ _ LOrt.x)
          · intro _ h' h1
            simp only [aufN, ↓reduceIte, Nat.zero_ne_one] at h' h1
            have := hI.t1 hpc1 h' m hl.1 h1
            have := hl.2
            omega

theorem coInv_erreichbar {Z : LZustand LOrt} (h : LErreichbar (LSchritt coRR) Z) : CoInv Z := by
  induction h with
  | start => exact coInv_start
  | schritt _ hs ih => exact coInv_schritt ih hs

/-- **CoRR: FORBIDDEN.** A thread that read the second write (`2`) never reads the first (`1`)
    afterwards -- per-location coherence, from the view alone. -/
theorem corr_verboten {Z : LZustand LOrt} (h : LErreichbar (LSchritt coRR) Z) (hpc : Z.pc 1 = 2)
    (h0 : Z.reg 1 0 = 2) : Z.reg 1 1 ≠ 1 :=
  (coInv_erreichbar h).r1 (by omega) h0

end Gabbro.Grammatik.Speichermodell
