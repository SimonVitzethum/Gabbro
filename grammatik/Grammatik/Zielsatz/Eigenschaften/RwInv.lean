/-
  File:      Grammatik/Zielsatz/Eigenschaften/RwInv.lean
  Subject:   THE READER/WRITER LOCK, STEP FOUR: THE LOCK INVARIANT `S.inv` is VISIBLE TO READERS and
             RE-ESTABLISHED BY WRITERS ONLY.

  Machine G's `SperrInvG`: every FREE lock has its invariant at the live memory, given that every
  release re-establishes it. The layer's version: every lock whose holders (if any) are all READERS
  has its invariant (`SperrInvRw`). A reader's acquisition starts from such a lock, a reader's
  release leaves one, and neither moves a carrier the lock guards (`LeserLos`), so neither owes
  anything. The only owed step is a WRITER's release, exactly G's `hfrei` hypothesis.

  * `sperrInvRw_schritt` -- one layer step keeps `SperrInvRw`, given (i) the readers' discipline of the
    step (a reader's step changes no carrier its lock guards) and (ii) the release obligation of a
    WRITER only (`hwr`): a lock the acting thread holds without being a reader of it, and releases in
    the step, has its invariant at the new memory.
  * `sperrInvRw_lauf` -- along a layer run.
  * `leser_sieht_inv` -- THE VISIBILITY: a thread that holds `L` as a reader sees `S.inv L` at the live
    memory, at every machine of the run (the holders are readers: exclusion).
  * `schreiber_erst_frei` -- a thread that holds `L` and is not a reader holds it alone, so the
    invariant may be broken only inside a section no other thread is in.
-/
import Grammatik.Zielsatz.Eigenschaften.RwOrdnung

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat} {lese : Lese D}
  {S : SperrInv D}

/-- **The lock invariant of a shared lock**: every lock all of whose holders are readers (a free lock
    among them) has its invariant at the live memory. -/
def SperrInvRw (lese : Lese D) (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ L : D.Lock, (∀ t : Faden, L ∈ offen (M.faeden t).spur → lese t L) → S.inv L M.speicher = true

theorem sperrInvRw_start (P : Programm D) (S : SperrInv D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hsp : ∀ L, S.inv L sp = true) :
    SperrInvRw lese S (RufStartG P sp init) :=
  fun L _ => hsp L

/-- **A layer step keeps the lock invariant of every shared lock.**
    `hdisc`: a reader's step changes no carrier its lock guards (`LeserLos`, at this step).
    `hwr`: the obligation of a WRITER's release -- a lock the acting thread holds without being a
    reader of it and no longer holds after the step has its invariant at the new memory. -/
theorem sperrInvRw_schritt (hO : GutO O) (hS : SperrInvOk S) {M M' : RufMaschineG D} {u : Faden}
    (hs : RwSchritt P O passes lese M u M') (hSR : SperrInvRw lese S M)
    (hdisc : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock), Bewacht c L → lese u L →
      TraegerGleich M'.speicher M.speicher c)
    (hwr : ∀ L, L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → ¬ lese u L →
      S.inv L M'.speicher = true) : SperrInvRw lese S M' := by
  intro L hL
  by_cases hA : ∀ t, L ∈ offen (M.faeden t).spur → lese t L
  · -- only readers held `L` before: the carriers it guards are untouched
    rw [← hSR L hA]
    refine hS.2 L _ _ fun c hc => ?_
    by_cases hu : L ∈ offen (M.faeden u).spur
    · exact hdisc c L (hS.1 L c hc) (hA u hu)
    · exact rwSchritt_traeger hO hs c ⟨L, hS.1 L c hc, hu⟩
  · -- a writer `t` held `L`: it can only be the acting thread, and it released
    obtain ⟨t, ht, htl⟩ : ∃ t, L ∈ offen (M.faeden t).spur ∧ ¬ lese t L :=
      Classical.byContradiction fun hn => hA fun t ht =>
        Classical.byContradiction fun htl => hn ⟨t, ht, htl⟩
    by_cases htu : t = u
    · subst htu
      refine hwr L ht ?_ htl
      intro hafter
      exact htl (hL t hafter)
    · exfalso
      apply htl
      apply hL t
      rw [rwSchritt_fremd hs t htu]
      exact ht

theorem sperrInvRw_lauf (hO : GutO O) (hS : SperrInvOk S) {M0 : RufMaschineG D}
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : RwLauf P O passes lese M0 ms fs n) (h0 : SperrInvRw lese S M0)
    (hd : ∀ k, k < n → ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock), Bewacht c L → lese (fs k) L →
      TraegerGleich (ms (k + 1)).speicher (ms k).speicher c)
    (hwr : ∀ k, k < n → ∀ L, L ∈ offen ((ms k).faeden (fs k)).spur →
      L ∉ offen ((ms (k + 1)).faeden (fs k)).spur → ¬ lese (fs k) L →
      S.inv L (ms (k + 1)).speicher = true) :
    ∀ k, k ≤ n → SperrInvRw lese S (ms k)
  | 0, _ => by rw [hl.1]; exact h0
  | k + 1, hk =>
      sperrInvRw_schritt hO hS (hl.2 k (by omega)) (sperrInvRw_lauf hO hS hl h0 hd hwr k (by omega))
        (hd k (by omega)) (hwr k (by omega))

/-- **THE VISIBILITY.** A thread that holds `L` as a reader sees the invariant of `L` at the live
    memory: every holder of `L` is a reader (exclusion), so `SperrInvRw` applies. -/
theorem leser_sieht_inv {M : RufMaschineG D} (hx : RwExkl lese M) (hSR : SperrInvRw lese S M)
    {t : Faden} {L : D.Lock} (ht : L ∈ offen (M.faeden t).spur) (hl : lese t L) :
    S.inv L M.speicher = true := by
  refine hSR L fun u hu => ?_
  by_cases htu : t = u
  · subst htu
    exact hl
  · exact (hx t u L htu ht hu).2

/-- A thread that holds `L` without being a reader of it holds it alone: no other thread can observe
    a state inside its section. -/
theorem schreiber_erst_frei {M : RufMaschineG D} (hx : RwExkl lese M) {t : Faden} {L : D.Lock}
    (ht : L ∈ offen (M.faeden t).spur) (hw : ¬ lese t L) :
    ∀ u, u ≠ t → L ∉ offen (M.faeden u).spur :=
  rw_schreiber_allein hx ht hw

end Gabbro.Grammatik.Zielsatz

#print axioms Gabbro.Grammatik.Zielsatz.sperrInvRw_lauf
#print axioms Gabbro.Grammatik.Zielsatz.leser_sieht_inv
