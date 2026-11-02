/-
   File:      Grammatik/GabbroV/GvVerkettung.lean
   Subject:   Agent 04 follow-up: the person's linked-structure arguments
              (TODO 0f; `01-tabelle`, `55-kindkette`, `F01`, `kapraum`;
              `programmlogik/PLAN.md` 5.1).

   Per unit, the person owes a `reaches`-invariant across a relink (PLAN
   5.1); the GvTreeParent decision (NO: `deklaration_schliesst_eltern_nicht`,
   `deklaration_schliesst_benutzt_nicht`) shows the declaration does not
   give it. Lemma (a) below is the walk bound every `traverse` domain
   needs; lemma (b) is pop-preserves-acyclicity for free lists.
-/
module
public import Grammatik.GabbroV.GvTreeParent
@[expose] public section


namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik.GabbroV

/-- The chain over one `option index` field, with fuel: `k` reaches `ziel`
    in at most `fuel` steps. Nat-index mirror of `Semantik.kette`
    (`Semantik.lean:203-209`); total because the fuel is finite, and the
    fuel the surface uses is the slot count (`eval` `.reaches`,
    `Semantik.lean:261-262`). At fuel zero an `if` stands where `kette`
    writes `decide`: Bool-equal, and the successor case is identical.
    Nothing here is an interpreter: a `Bool` predicate over data. -/
def ketteNext (nxt : Nat → Option Nat) : Nat → Nat → Nat → Bool
  | 0, k, ziel => if k = ziel then true else false
  | fuel + 1, k, ziel =>
      if k = ziel then true
      else
        match nxt k with
        | none => false
        | some m => ketteNext nxt fuel m ziel

/-- Zero steps reach the start itself. -/
theorem ketteNext_refl (nxt : Nat → Option Nat) (fuel h : Nat) :
    ketteNext nxt fuel h h = true := by
  cases fuel with
  | zero => simp only [ketteNext, ↓reduceIte]
  | succ fuel => simp only [ketteNext, ↓reduceIte]

/-- One unfolding step, away from the target. -/
theorem ketteNext_schritt (nxt : Nat → Option Nat) (fuel a d : Nat)
    (heq : a ≠ d) :
    ketteNext nxt (fuel + 1) a d =
      match nxt a with
      | none => false
      | some m => ketteNext nxt fuel m d := by
  simp only [ketteNext, if_neg heq]

/-- More fuel reaches at least as far. -/
theorem ketteNext_mono (nxt : Nat → Option Nat) (fuel extra a d : Nat)
    (h : ketteNext nxt fuel a d = true) :
    ketteNext nxt (fuel + extra) a d = true := by
  induction fuel generalizing a extra with
  | zero =>
      by_cases heq : a = d
      · subst heq
        have h0 : 0 + extra = extra := by omega
        rw [h0]
        exact ketteNext_refl nxt extra a
      · exfalso
        simp only [ketteNext, if_neg heq, Bool.false_eq_true] at h
  | succ fuel ih =>
      cases extra with
      | zero =>
          have h0 : fuel + 1 + 0 = fuel + 1 := by omega
          rw [h0]
          exact h
      | succ extra =>
          have hS : ketteNext nxt (fuel + 1) a d = true := h
          by_cases heq : a = d
          · subst heq
            exact ketteNext_refl nxt _ _
          · have hfuel : fuel + 1 + (extra + 1) = (fuel + (extra + 1)) + 1 := by
              omega
            rw [ketteNext_schritt nxt _ _ _ heq] at hS
            rw [hfuel, ketteNext_schritt nxt _ _ _ heq]
            cases hm : nxt a with
            | none => simp only [hm, Bool.false_eq_true] at hS
            | some m =>
                have hrest : ketteNext nxt fuel m d = true := by
                  rw [hm] at hS
                  exact hS
                have hgo := ih (extra + 1) m hrest
                exact hgo

/-! ## The drawer principle: n+1 values below n repeat one -/

/-- Drawer principle (`Schubfach`): n+1 values below n repeat one. -/
theorem schubladenSatz (f : Nat → Nat) (n : Nat)
    (h : ∀ k, k < n + 1 → f k < n) :
    ∃ i j, i < j ∧ j < n + 1 ∧ f i = f j := by
  induction n generalizing f with
  | zero =>
      have h0 := h 0 (by omega)
      omega
  | succ n ih =>
      by_cases hex : ∃ i, i < n + 1 ∧ f i = f (n + 1)
      · obtain ⟨i, hi, heq⟩ := hex
        exact ⟨i, n + 1, hi, by omega, heq⟩
      · by_cases hvn : f (n + 1) = n
        · have hklein : ∀ k, k < n + 1 → f k < n := by
            intro k hk
            have hfk := h k (by omega)
            have hne : f k ≠ f (n + 1) := by
              intro hcontra
              exact hex ⟨k, hk, hcontra⟩
            omega
          obtain ⟨i, j, hij, hjn, heq⟩ := ih f hklein
          exact ⟨i, j, hij, by omega, heq⟩
        · have hB : ∀ i, i < n + 1 → f i ≠ f (n + 1) := by
            intro i hi hcontra
            exact hex ⟨i, hi, hcontra⟩
          have hlast : f (n + 1) < n := by
            have htop := h (n + 1) (by omega)
            omega
          have hg : ∀ k, k < n + 1 →
              (if f k = n then f (n + 1) else f k) < n := by
            intro k hk
            have hfk := h k (by omega)
            by_cases hkn : f k = n
            · rw [if_pos hkn]
              exact hlast
            · rw [if_neg hkn]
              omega
          obtain ⟨i, j, hij, hjn, heq⟩ :=
            ih (fun k => if f k = n then f (n + 1) else f k) hg
          by_cases hfin : f i = n
          · by_cases hfin2 : f j = n
            · exact ⟨i, j, hij, by omega, by omega⟩
            · have heq' : f (n + 1) = f j := by
                simpa [hfin, hfin2] using heq
              exact False.elim (hB j (by omega) (by omega))
          · by_cases hfin2 : f j = n
            · have heq' : f i = f (n + 1) := by
                simpa [hfin, hfin2] using heq
              exact False.elim (hB i (by omega) (by omega))
            · have heq' : f i = f j := by
                simpa [hfin, hfin2] using heq
              exact ⟨i, j, hij, by omega, heq'⟩

/-! ## The walk bound: n steps in n slots end or repeat -/

/-- Forward walk: `k` steps from `s` along `nxt`, `none` past the end.
    `ketteNext` searches backwards for a target; this one walks forwards
    and counts visits. -/
def geh (nxt : Nat → Option Nat) : Nat → Nat → Option Nat
  | 0, s => some s
  | fuel + 1, s =>
      match nxt s with
      | none => none
      | some m => geh nxt fuel m

/-- Position value with stop sentinel `n` (outside every slot `< n`). -/
def wert (nxt : Nat → Option Nat) (n s : Nat) : Nat → Nat
  | k =>
    match geh nxt k s with
    | some m => m
    | none => n

/-- One unfolding step of the walk. -/
theorem geh_schritt (nxt : Nat → Option Nat) (fuel s : Nat) :
    geh nxt (fuel + 1) s =
      match nxt s with
      | none => none
      | some m => geh nxt fuel m := by
  simp only [geh]

/-- In-range edges keep a started walk in range. -/
theorem geh_bereich (nxt : Nat → Option Nat) (n s : Nat) (hs : s < n)
    (hrand : ∀ j, j < n → ∀ m, nxt j = some m → m < n)
    (k : Nat) (m : Nat) (hm : geh nxt k s = some m) : m < n := by
  induction k generalizing s with
  | zero =>
      have hsm : s = m := by simpa [geh] using hm
      omega
  | succ k ih =>
      cases hsm : nxt s with
      | none =>
          have hstop : geh nxt (k + 1) s = none := by
            rw [geh_schritt, hsm]
          rw [hstop] at hm
          simp only [reduceCtorEq] at hm
      | some t =>
          have hrest : geh nxt k t = some m := by
            have h2 := hm
            rw [geh_schritt, hsm] at h2
            exact h2
          exact ih t (hrand s hs t hsm) hrest

/-- Traversal bound: `n + 1` positions in a table of `n` slots either stop
    (`none`) or repeat a slot below `n`. This is the `descend_to_leaf`
    half of `kapraum.gab:10-14` and the domain bound of every
    `traverse ... by consuming` in `01`/`F01`/`kapraum`. -/
theorem kette_schranke (nxt : Nat → Option Nat) (n s : Nat) (hs : s < n)
    (hrand : ∀ j, j < n → ∀ m, nxt j = some m → m < n) :
    (∃ k, k ≤ n ∧ geh nxt k s = none) ∨
      (∃ i j, i < j ∧ j ≤ n ∧
        wert nxt n s i = wert nxt n s j ∧ wert nxt n s i < n) := by
  by_cases hstop : ∃ k, k ≤ n ∧ geh nxt k s = none
  · exact Or.inl hstop
  · apply Or.inr
    have hall : ∀ k, k < n + 1 → wert nxt n s k < n := by
      intro k hk
      have hne : geh nxt k s ≠ none := by
        intro hcontra
        exact hstop ⟨k, by omega, hcontra⟩
      cases hgm : geh nxt k s with
      | none => exact absurd hgm hne
      | some m =>
          have hmlt : m < n := geh_bereich nxt n s hs hrand k m hgm
          have hwm : wert nxt n s k = m := by simp only [wert, hgm]
          omega
    obtain ⟨i, j, hij, hjn, heq⟩ := schubladenSatz (wert nxt n s) n hall
    have hilt : wert nxt n s i < n := hall i (by omega)
    exact ⟨i, j, hij, by omega, heq, hilt⟩

/-! ## Pop keeps acyclicity: removing edges cannot create cycles -/

end Gabbro.Grammatik.GabbroV
