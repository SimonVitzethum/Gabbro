/-
  File:      Grammatik/Zielsatz/Akzeptiert.lean
  Subject:   PLAN-ZIELSATZ.md step 3 -- what the CHECKER decides, as ONE Bool
             (`Akzeptiert`), proved to be a `Pruefer` of `Spec.lean`
             (`akzeptiert_pruefer`): the Bool decides EXACTLY
             `AkzeptiertSpec` (`akzeptiert_iff`), given complete member
             lists. The start the goal speaks about is Spec's
             `StartZulaessig`, with a Bool for finite start tables
             (`startB`).

  `Akzeptiert P S fs ls cs ws` is the conjunction of every premise of the
  flagship theorems that is a decidable fact about the PROGRAM:

  | component      | Bool                   | field of `AkzeptiertSpec` (Spec.lean)                  | used by |
  |----------------|------------------------|--------------------------------------------------------|---------|
  | `frag`         | `programmImFragmentG`  | the same Bool                                          | `hFrag` of `ziel_ort_mehrfaden_ende` |
  | `abg`          | `abgAlleB`             | `∀ w, AbgK P fs (reachB P fs w)`                       | `hAbg` (with `K t := reachB P fs (init t).1`) |
  | `fuss`         | `fussWB`               | `∀ f, FussS P S (lokW P fs ws) f`                      | `hFuss` (with `StartZulaessig`) |
  | `stufen`       | `stufenB`              | `StufenM P`                                            | `hSt` of `keine_verklemmungG` |
  | `sperrOrte`    | `sperrOrteB`           | `∀ L c, c ∈ S.orte L → Bewacht c L`                    | first half of `hS : SperrInvOk S` |
  | `wurzeln`      | `wurzelnB`             | `∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0`           | `hLeer` / `hex`; no reasons at a start (`StartOhneGrund`) |
  | `renn`         | `rennB`                | every unguarded, non-atomic, non-payload carrier is `SchreibGetrennt` | `rennfrei_ungeschuetzt` (the checker's `H013`) |

  **Member lists.** `fs` (functions), `ls` (locks), `cs` (carriers:
  tables and globals). `D.Fn`, `D.Lock`, `D.Tab`, `D.Glob` carry no
  enumeration; `SperrInvOk`'s first half and the deadlock theorem quantify
  over every lock, and the race component over every carrier (a write-write
  race on a carrier that no footprint reads is visible to no footprint list,
  only to a list of ALL carriers). In `GabbroZiel` all three are
  `Aufzaehlung`s -- complete by their type.

  `ws : List D.Fn` -- the program's DECLARED THREAD STARTS (the checker's
  `concurrent { … }` members and `entry`/`boot` dispatch roots,
  `crates/gabbro-check/src/startexklusiv.rs`). `Programm D` has no field for
  the starts, so the list is an argument; the call graphs are COMPUTED from
  it (`reachB`), never supplied.

  **Changes of 2026-09-14 (review findings):**
  * `renn` is NEW: a write-write race on an unguarded carrier that no
    footprint reads passed the old Bool (thread-locality was judged on
    footprints, which list reads, not writes). `rennfreiBis_of`
    proves Spec's `RennfreiBis` for EVERY carrier from the Bool's Prop and an
    admissible start (`rennfrei_alle`, RennfreiOrte.lean). Probe:
    `ak3_zwei_schreiber_ohne_lesen` (AkzeptiertZeuge.lean) -- refused now,
    accepted by the old conjunction.
  * `wurzeln` includes "no reasons" (`D.gruende w = 0`).
  * `zeit` (`rufTief` for every function) is DROPPED: it refused every
    recursive or indirect program, and Spec does not need it -- the time
    leg `ZeitAb` is conditional on `rufTief` per frame.
  * `StartZulaessig`/`Ruhig`/`SperrInvLokal` are Spec's (one definition).
    `Ruhig` now demands that an idle start writes NOTHING (before: no
    footprint carrier) -- two idle threads writing one unguarded carrier
    would race.

  **What could NOT be made decidable, and why:**
  * member-list completeness (`hvoll`, `hls`, `hcs`): the exporter's
    `inductive`s are finite, and the proof is `cases` per declaration.
  * `SperrInvLokal S` and `AxEnsLokal Q`: `S.inv L` and `Q a` are
    Bool-valued FUNCTIONS on memory, not syntax. User well-formedness.
  * `StartGut`, `∀ L, S.inv L sp`, the start assignment: they RESTRICT the
    quantified start (`StartZulaessig`); decidable for a finite start table
    (`startB`).
  * NOT in `Akzeptiert`, although decidable per instance:
    `kostenPasst P passes decl fs` (the DECLARED costs; `decl` is not part
    of `Programm D`, and the check depends on `passes`).
-/
import Grammatik.Zielsatz.Spec
import Grammatik.RennfreiOrte

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section Akzeptiert

variable [DecidableEq D.Fn]

/-! ## 1. Thread-locality over the declared starts -/

/-- **`c` is thread-local among the declared starts** (reads against
    writes): for every two DIFFERENT declared starts, no function the first
    reaches has `c` in its footprint while a function the second reaches may
    write it. Decides Spec's `Getrennt`. -/
def getrenntW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w1 => ws.all fun w2 => decide (w1 = w2) ||
    (fs.all fun f => !(reachB P fs w1 f) || !(istIn (fussOrteG P f) c)) ||
    (fs.all fun g => !(reachB P fs w2 g) || !(TraegerSchreibt g c))

theorem getrenntW_iff {P : Programm D} {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {c : D.Tab ⊕ D.Glob} : getrenntW P fs ws c = true ↔ Getrennt P fs ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne f g hf hc hg
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with (h1 | h1) | h1
    · exact absurd h1 hne
    · have h2 := (List.all_eq_true.mp h1) f (hvoll f)
      rw [hf, istIn_iff.mpr hc] at h2
      simp at h2
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [hg] at h2
      simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2
    · simp [hne]
    by_cases hfr : (fs.all fun f => !(reachB P fs w1 f) || !(istIn (fussOrteG P f) c)) = true
    · simp [hfr]
    · have hex : ∃ f, reachB P fs w1 f = true ∧ c ∈ fussOrteG P f := by
        refine Classical.byContradiction fun hn => hfr (List.all_eq_true.mpr fun f _ => ?_)
        cases hr : reachB P fs w1 f
        · rfl
        · cases hi : istIn (fussOrteG P f) c
          · rfl
          · exact absurd ⟨f, hr, istIn_iff.mp hi⟩ hn
      obtain ⟨f, hf, hc⟩ := hex
      have hw : (fs.all fun g => !(reachB P fs w2 g) || !(TraegerSchreibt g c)) = true :=
        List.all_eq_true.mpr fun g _ => by
          cases hg : reachB P fs w2 g
          · rfl
          · simp [h w1 hw1 w2 hw2 hne f g hf hc hg]
      simp [hw]

/-- The decided thread-locality IS Spec's `lokW` (given the member list). -/
theorem getrenntW_eq_lokW {P : Programm D} {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) :
    getrenntW P fs ws = lokW P fs ws := by
  funext c
  unfold lokW
  cases h : getrenntW P fs ws c
  · symm
    apply @decide_eq_false _ (Classical.propDecidable _)
    intro hg
    rw [(getrenntW_iff hvoll).mpr hg] at h
    cases h
  · symm
    exact @decide_eq_true _ (Classical.propDecidable _) ((getrenntW_iff hvoll).mp h)

/-- **`c` is write-separated among the declared starts**: for every two
    DIFFERENT declared starts, if a function the first reaches may write
    `c`, no function the second reaches may write it or have it in its
    footprint. Decides Spec's `SchreibGetrennt`. -/
def schreibGetrenntW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w1 => ws.all fun w2 => decide (w1 = w2) ||
    (fs.all fun g => !(reachB P fs w1 g) || !(TraegerSchreibt g c)) ||
    (fs.all fun h => !(reachB P fs w2 h) ||
      (!(TraegerSchreibt h c) && !(istIn (fussOrteG P h) c)))

theorem schreibGetrenntW_iff {P : Programm D} {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {c : D.Tab ⊕ D.Glob} : schreibGetrenntW P fs ws c = true ↔ SchreibGetrennt P fs ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne g hg hgw k hk
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with (h1 | h1) | h1
    · exact absurd h1 hne
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [hg, hgw] at h2
      simp at h2
    · have h2 := (List.all_eq_true.mp h1) k (hvoll k)
      rw [hk] at h2
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h2
      exact ⟨h2.1, fun hc => by rw [istIn_iff.mpr hc] at h2; cases h2.2⟩
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2
    · simp [hne]
    by_cases hfr : (fs.all fun g => !(reachB P fs w1 g) || !(TraegerSchreibt g c)) = true
    · simp [hfr]
    · have hex : ∃ g, reachB P fs w1 g = true ∧ TraegerSchreibt g c = true := by
        refine Classical.byContradiction fun hn => hfr (List.all_eq_true.mpr fun g _ => ?_)
        cases hr : reachB P fs w1 g
        · rfl
        · cases hi : TraegerSchreibt g c
          · rfl
          · exact absurd ⟨g, hr, hi⟩ hn
      obtain ⟨g, hg, hgw⟩ := hex
      have hw : (fs.all fun k => !(reachB P fs w2 k) ||
          (!(TraegerSchreibt k c) && !(istIn (fussOrteG P k) c))) = true :=
        List.all_eq_true.mpr fun k _ => by
          cases hk : reachB P fs w2 k
          · rfl
          · obtain ⟨h1, h2⟩ := h w1 hw1 w2 hw2 hne g hg hgw k hk
            have h3 : istIn (fussOrteG P k) c = false := by
              cases hi : istIn (fussOrteG P k) c
              · rfl
              · exact absurd (istIn_iff.mp hi) h2
            simp [h1, h3]
      simp [hw]

/-! ## 2. The exemptions of the race component -/

/-- An `atomic` global (`AtomarAusgenommen`), decided. -/
def atomarB : D.Tab ⊕ D.Glob → Bool
  | .inl _ => false
  | .inr g => D.atomar g

/-- A publish payload (`PaarungAusgenommen`), decided over the carrier list. -/
def paarungB (cs : List (D.Tab ⊕ D.Glob)) : D.Tab ⊕ D.Glob → Bool
  | .inl _ => false
  | .inr p => cs.any fun a => match a with
    | .inl _ => false
    | .inr a => decide (p ∈ D.nutzlast a) && D.atomar a

/-- The carrier needs no write separation: it has a guard lock, or it is
    `atomic`, or a publish payload. -/
def ausgenommenB (cs : List (D.Tab ⊕ D.Glob)) (c : D.Tab ⊕ D.Glob) : Bool :=
  !(waechterVon c).isEmpty || atomarB c || paarungB cs c

theorem ausgenommenB_false {cs : List (D.Tab ⊕ D.Glob)} (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {c : D.Tab ⊕ D.Glob} :
    ausgenommenB cs c = false ↔
      (∀ L, ¬ Bewacht c L) ∧ ¬ AtomarAusgenommen c ∧ ¬ PaarungAusgenommen c := by
  unfold ausgenommenB
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff]
  constructor
  · rintro ⟨⟨hw, ha⟩, hp⟩
    refine ⟨fun L hL => ?_, ?_, ?_⟩
    · have := waechterVon_mem.mpr hL
      rw [hw] at this
      exact absurd this List.not_mem_nil
    · rintro ⟨g, rfl, hg⟩
      simp [atomarB, hg] at ha
    · rintro ⟨a, p, rfl, hp', ha'⟩
      simp only [paarungB, List.any_eq_false] at hp
      have := hp (.inr a) (hcs _)
      simp [hp', ha'] at this
  · rintro ⟨hB, hA, hP⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · cases hw : waechterVon c with
      | nil => rfl
      | cons L _ => exact absurd (waechterVon_mem.mp (by rw [hw]; exact List.mem_cons_self)) (hB L)
    · cases c with
      | inl t => rfl
      | inr g =>
          cases hg : D.atomar g
          · simp [atomarB, hg]
          · exact absurd ⟨g, rfl, hg⟩ hA
    · cases c with
      | inl t => rfl
      | inr p =>
          simp only [paarungB, List.any_eq_false]
          intro a _
          cases a with
          | inl _ => simp
          | inr a =>
              cases hpa : decide (p ∈ D.nutzlast a)
              · simp [hpa]
              · cases ha : D.atomar a
                · simp [ha]
                · exact absurd ⟨a, p, rfl, of_decide_eq_true hpa, ha⟩ hP

/-- **The race component**: every carrier that needs it is write-separated
    among the declared starts. -/
def rennB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    Bool :=
  cs.all fun c => ausgenommenB cs c || schreibGetrenntW P fs ws c

theorem rennB_iff {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    rennB P fs cs ws = true ↔ ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c →
      ¬ PaarungAusgenommen c → SchreibGetrennt P fs ws c := by
  constructor
  · intro h c hB hA hP
    have h1 := (List.all_eq_true.mp h) c (hcs c)
    rw [(ausgenommenB_false hcs).mpr ⟨hB, hA, hP⟩, Bool.false_or] at h1
    exact (schreibGetrenntW_iff hvoll).mp h1
  · intro h
    refine List.all_eq_true.mpr fun c _ => ?_
    cases ha : ausgenommenB cs c
    · obtain ⟨hB, hA, hP⟩ := (ausgenommenB_false hcs).mp ha
      rw [Bool.false_or]
      exact (schreibGetrenntW_iff hvoll).mpr (h c hB hA hP)
    · rfl

/-! ## 3. The components -/

/-- Every computed call graph is closed -- for EVERY function as a root, so
    no start assignment is needed. -/
def abgAlleB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun w => abgB P fs (reachB P fs w)

/-- **The footprint check over the declared starts**: `fussMehrB` with
    thread-locality judged over `ws` (`getrenntW`) instead of over threads
    below a bound. -/
def fussWB (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || getrenntW P fs ws c || (waechterVon c).any fun L => istIn (S.orte L) c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || getrenntW P fs ws c)

/-- The lock floors on every body (`StufenM`). -/
def stufenB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => mE (bodenM f) (P.rumpf f)

/-- Every protected carrier is guarded by its lock (first half of
    `SperrInvOk`). -/
def sperrOrteB (S : SperrInv D) (ls : List D.Lock) : Bool :=
  ls.all fun L => (S.orte L).all fun c => decide (L ∈ waechterVon c)

/-- No declared start holds a lock by signature (`N240`, strong form) or has
    reasons (a start's reason has no caller to go to). -/
def wurzelnB (ws : List D.Fn) : Bool :=
  ws.all fun w => (D.haelt w).isEmpty && decide (D.gruende w = 0)

/-- **`Akzeptiert` -- what the checker decides, as ONE Bool.** -/
def Akzeptiert (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && rennB P fs cs ws

/-! ## 4. Each component decides its field of `AkzeptiertSpec` -/

section Komponenten

variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
  {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

theorem abgAlleB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    abgAlleB P fs = true ↔ ∀ w, AbgK P fs (reachB P fs w) := by
  constructor
  · intro h w
    exact abgB_ok hvoll ((List.all_eq_true.mp h) w (hvoll w))
  · intro h
    refine List.all_eq_true.mpr fun w _ => List.all_eq_true.mpr fun f _ => ?_
    cases hf : reachB P fs w f
    · rfl
    · simp [h w f hf]

theorem fussWB_iff' (hvoll : ∀ g : D.Fn, g ∈ fs) :
    fussWB P S fs ws = true ↔ ∀ f, FussS P S (getrenntW P fs ws) f := by
  constructor
  · intro h f
    have h1 := (List.all_eq_true.mp h) f (hvoll f)
    simp only [Bool.and_eq_true] at h1
    refine ⟨fun c hc => ?_, fun c hc => (List.all_eq_true.mp h1.2) c hc⟩
    have h2 := (List.all_eq_true.mp h1.1) c hc
    simp only [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact Or.inl (by simp only [Bool.or_eq_true]; exact h2)
    · obtain ⟨L, hL, hc'⟩ := List.any_eq_true.mp h2
      exact Or.inr ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hc'⟩
  · intro h
    refine List.all_eq_true.mpr fun f _ => ?_
    simp only [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr fun c hc => ?_, List.all_eq_true.mpr fun c hc => (h f).2 c hc⟩
    rcases (h f).1 c hc with h2 | ⟨L, hL, hc'⟩
    · simp only [Bool.or_eq_true] at h2 ⊢
      exact Or.inl h2
    · simp only [Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨L, waechterVon_mem.mpr hL, istIn_iff.mpr hc'⟩)

theorem fussWB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    fussWB P S fs ws = true ↔ ∀ f, FussS P S (lokW P fs ws) f := by
  rw [← getrenntW_eq_lokW hvoll]
  exact fussWB_iff' hvoll

omit [DecidableEq D.Fn] in
theorem stufenB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) : stufenB P fs = true ↔ StufenM P :=
  ⟨fun h f => (List.all_eq_true.mp h) f (hvoll f), fun h => List.all_eq_true.mpr fun f _ => h f⟩

omit [DecidableEq D.Fn] in
theorem sperrOrteB_iff (hls : ∀ L : D.Lock, L ∈ ls) :
    sperrOrteB S ls = true ↔ ∀ L c, c ∈ S.orte L → Bewacht c L := by
  constructor
  · intro h L c hc
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) L (hls L))) c hc
    exact waechterVon_mem.mp (of_decide_eq_true h1)
  · intro h
    exact List.all_eq_true.mpr fun L _ => List.all_eq_true.mpr fun c hc =>
      decide_eq_true (waechterVon_mem.mpr (h L c hc))

omit [DecidableEq D.Fn] in
theorem wurzelnB_iff : wurzelnB (D := D) ws = true ↔ ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0 := by
  unfold wurzelnB
  rw [List.all_eq_true]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq]

/-- **`Akzeptiert` decides exactly `AkzeptiertSpec`** (given complete member
    lists). -/
theorem akzeptiert_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    Akzeptiert P S fs ls cs ws = true ↔ AkzeptiertSpec P S fs ws := by
  unfold Akzeptiert
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    exact ⟨h1, (abgAlleB_iff hvoll).mp h2, (fussWB_iff hvoll).mp h3, (stufenB_iff hvoll).mp h4,
      (sperrOrteB_iff hls).mp h5, wurzelnB_iff.mp h6, (rennB_iff hvoll hcs).mp h7⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨h.frag, (abgAlleB_iff hvoll).mpr h.abg⟩, (fussWB_iff hvoll).mpr h.fuss⟩,
      (stufenB_iff hvoll).mpr h.stufen⟩, (sperrOrteB_iff hls).mpr h.sperrOrte⟩,
      wurzelnB_iff.mpr h.wurzeln⟩, (rennB_iff hvoll hcs).mpr h.renn⟩

theorem akzeptiertSpec_of (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (h : Akzeptiert P S fs ls cs ws = true) :
    AkzeptiertSpec P S fs ws :=
  (akzeptiert_iff hvoll hls hcs).mp h

end Komponenten

end Akzeptiert

/-- **The concrete checker is a `Pruefer`**: its Bool is `Akzeptiert`, and
    its soundness obligation against `AkzeptiertSpec` is `akzeptiert_iff`. -/
def akzeptiert_pruefer : Pruefer where
  akzeptiert := fun P S fs ls cs ws => Akzeptiert P S fs ls cs ws
  korrekt := fun _ _ fs ls cs _ h => akzeptiertSpec_of fs.2 ls.2 cs.2 h

section Start

variable [DecidableEq D.Fn]

/-! ## 5. The start -/

/-- **An idle start, decided**: holds no lock by signature, has no reasons,
    and every function it reaches has an empty footprint and writes no
    carrier of the list `cs`. -/
def ruheB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && decide (D.gruende w = 0) && fs.all fun f => !(reachB P fs w f) ||
    ((fussOrteG P f).isEmpty && cs.all fun c => !(TraegerSchreibt f c))

theorem ruheB_iff {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) {w : D.Fn} :
    ruheB P fs cs w = true ↔ Ruhig P fs w := by
  unfold ruheB Ruhig
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun f hf => ?_⟩
    have h4 := (List.all_eq_true.mp h3) f (hvoll f)
    rw [hf] at h4
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at h4
    refine ⟨h4.1, fun c => ?_⟩
    have h5 := (List.all_eq_true.mp h4.2) c (hcs c)
    simpa using h5
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, List.all_eq_true.mpr fun f _ => ?_⟩
    cases hf : reachB P fs w f
    · rfl
    · obtain ⟨h4, h5⟩ := h3 f hf
      simp [h4, h5]

/-- The call graph of thread `t`, computed from its start function. -/
def kVon (P : Programm D) (fs : List D.Fn) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) : D.Fn → Bool :=
  reachB P fs (init t).1

variable {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ws : List D.Fn}
  {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}

/-- The declared-start test gives thread-locality for the computed graphs
    of every admissible start. -/
theorem getrenntK_of (hZ : StartZulaessig P S fs ws sp init)
    {c : D.Tab ⊕ D.Glob} (hc : Getrennt P fs ws c) : GetrenntK P (kVon P fs init) c := by
  intro t u htu f hf hcf g hg
  by_cases hrt : Ruhig P fs (init t).1
  · rw [(hrt.2.2 f hf).1] at hcf
    exact absurd hcf List.not_mem_nil
  by_cases hru : Ruhig P fs (init u).1
  · exact (hru.2.2 g hg).2 c
  have hwt := (hZ.wurzel t).resolve_right hrt
  have hwu := (hZ.wurzel u).resolve_right hru
  have hne : (init t).1 ≠ (init u).1 := fun he => hrt (hZ.einmal t u htu he)
  exact hc _ hwt _ hwu hne f g hf hcf hg

/-- The declared-start write separation gives write separation over the
    computed graphs of every admissible start: an idle thread writes
    nothing and reads nothing, and two busy threads run different declared
    starts. -/
theorem schreibGetrenntK_of (hZ : StartZulaessig P S fs ws sp init)
    {c : D.Tab ⊕ D.Glob} (hc : SchreibGetrennt P fs ws c) :
    SchreibGetrenntK P (kVon P fs init) c := by
  intro t u htu g hg hgw h hh
  by_cases hrt : Ruhig P fs (init t).1
  · rw [(hrt.2.2 g hg).2 c] at hgw
    cases hgw
  by_cases hru : Ruhig P fs (init u).1
  · obtain ⟨h1, h2⟩ := hru.2.2 h hh
    exact ⟨h2 c, by rw [h1]; exact List.not_mem_nil⟩
  have hwt := (hZ.wurzel t).resolve_right hrt
  have hwu := (hZ.wurzel u).resolve_right hru
  have hne : (init t).1 ≠ (init u).1 := fun he => hrt (hZ.einmal t u htu he)
  exact hc _ hwt _ hwu hne g hg hgw h hh

/-- No thread starts holding a lock by signature, and none starts with
    reasons. -/
theorem wurzel_of (hA : AkzeptiertSpec P S fs ws) (hZ : StartZulaessig P S fs ws sp init)
    (t : Faden) : D.haelt (init t).1 = [] ∧ D.gruende (init t).1 = 0 := by
  rcases hZ.wurzel t with h | h
  · exact hA.wurzeln _ h
  · exact ⟨h.1, h.2.1⟩

/-- **`Akzeptiert_ok` -- the checker's facts and an admitted start give every
    decidable premise of the flagships**, with the call graphs computed
    from the program (`kVon`). -/
theorem Akzeptiert_ok (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec P S fs ws)
    (hZ : StartZulaessig P S fs ws sp init) :
    programmImFragmentG P fs = true ∧
    (∀ t, AbgK P fs (kVon P fs init t)) ∧
    (∀ t, kVon P fs init t (init t).1 = true) ∧
    (∀ f, FussS P S (lokK P (kVon P fs init)) f) ∧
    (∀ L c, c ∈ S.orte L → Bewacht c L) ∧
    StartGut P sp init ∧ (∀ L, S.inv L sp = true) ∧ StartExklusiv init ∧
    StufenM P ∧ (∀ t, D.haelt (init t).1 = []) ∧
    (∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → ¬ PaarungAusgenommen c →
      SchreibGetrenntK P (kVon P fs init) c) := by
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => (wurzel_of hA hZ t).1
  refine ⟨hA.frag, fun t => hA.abg _, fun t => reachB_wurzel P fs _, fun f => ?_, hA.sperrOrte,
    hZ.req, hZ.sperren, startExklusiv_ohne_haelt init hLeer, hA.stufen, hLeer,
    fun c hB hAt hP => schreibGetrenntK_of hZ (hA.renn c hB hAt hP)⟩
  refine fussS_mono (fun c _ hc => lokK_of (getrenntK_of hZ ?_)) (hA.fuss f)
  unfold lokW at hc
  exact @of_decide_eq_true _ (Classical.propDecidable _) hc

/-- **Race freedom for EVERY carrier (Spec's `RennfreiBis`) from the
    checker's facts and an admissible start.** Guarded carriers:
    `rennfrei_g_voll`; unguarded carriers that are neither atomic nor a
    publish payload: write separation (`renn`) over the computed call
    graphs, `rennfrei_ungeschuetzt`. -/
theorem rennfreiBis_of (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec P S fs ws)
    (hZ : StartZulaessig P S fs ws sp init) {O : Orakel D} (hO : GutO O) (passes : Nat)
    (M : RufMaschineG D) : RennfreiBis P O passes (RufStartG P sp init) M := by
  obtain ⟨-, hAbg, hW, -, -, -, -, hex, -, -, hsep⟩ := Akzeptiert_ok hvoll hA hZ
  intro ms ts n hl _ i j c hij hjn hfg hzi hzj hw hAt hP
  exact rennfrei_alle hO hvoll sp init hex (kVon P fs init) hAbg hW hsep ms ts n hl i j c hij hjn
    hfg hzi hzj hw hAt hP

end Start

/-! ## 6. `SperrInvOk`: the decided half and the user's half -/

theorem sperrInvOk_iff (S : SperrInv D) :
    SperrInvOk S ↔ (∀ L c, c ∈ S.orte L → Bewacht c L) ∧ SperrInvLokal S :=
  Iff.rfl

/-! ## 7. Finite start tables: `StartZulaessig` decided -/

/-- **A finite start table**: thread `i` below `aktiv.length` runs
    `aktiv[i]`, every later thread runs `ruhe` (G starts every thread of
    `Faden = Nat`). -/
structure StartTafel (D : Deklaration) where
  aktiv : List (Σ f : D.Fn, Env D (D.params f))
  ruhe : Σ f : D.Fn, Env D (D.params f)

/-- The start assignment of a table. -/
def StartTafel.init (st : StartTafel D) : Faden → Σ f : D.Fn, Env D (D.params f) :=
  fun t => st.aktiv.getD t st.ruhe

theorem StartTafel.init_mem (st : StartTafel D) (t : Faden) :
    st.init t = st.ruhe ∨ st.init t ∈ st.aktiv := by
  unfold StartTafel.init
  rw [List.getD_eq_getElem?_getD]
  cases h : st.aktiv[t]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_of_getElem? h)

theorem StartTafel.init_ab (st : StartTafel D) {t : Faden} (ht : st.aktiv.length ≤ t) :
    st.init t = st.ruhe := by
  unfold StartTafel.init
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht]
  rfl

section Tafel

variable [DecidableEq D.Fn]

/-- **`StartZulaessig` for a start table, as a Bool.** -/
def startB (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (st : StartTafel D) (sp : Speicher D) : Bool :=
  ruheB P fs cs st.ruhe.1 &&
  (List.range st.aktiv.length).all (fun i =>
    (decide ((st.init i).1 ∈ ws) || ruheB P fs cs (st.init i).1) &&
    (List.range st.aktiv.length).all fun j =>
      decide (i = j) || !(decide ((st.init i).1 = (st.init j).1)) || ruheB P fs cs (st.init i).1) &&
  (st.ruhe :: st.aktiv).all (fun a =>
    wahr? (eval (sp.welt []) (P.requires a.1) (sp.welt []) a.2)) &&
  ls.all fun L => S.inv L sp

theorem startB_ok {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} {st : StartTafel D} {sp : Speicher D}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (h : startB P S fs ls cs ws st sp = true) : StartZulaessig P S fs ws sp st.init := by
  unfold startB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hR : ∀ w, ruheB P fs cs w = true → Ruhig P fs w := fun w hw => (ruheB_iff hvoll hcs).mp hw
  have hi : ∀ i, i < st.aktiv.length →
      ((st.init i).1 ∈ ws ∨ ruheB P fs cs (st.init i).1 = true) ∧
      ∀ j, j < st.aktiv.length → i ≠ j → (st.init i).1 = (st.init j).1 →
        ruheB P fs cs (st.init i).1 = true := by
    intro i hi
    have e := (List.all_eq_true.mp h2) i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at e
    refine ⟨e.1, fun j hj hij he => ?_⟩
    have e2 := (List.all_eq_true.mp e.2) j (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      at e2
    rcases e2 with (e2 | e2) | e2
    · exact absurd e2 hij
    · exact absurd he e2
    · exact e2
  refine ⟨fun t => ?_, fun t u htu he => ?_, fun t => ?_,
    fun L => (List.all_eq_true.mp h4) L (hls L)⟩
  · by_cases ht : t < st.aktiv.length
    · exact (hi t ht).1.imp id (hR _)
    · rw [st.init_ab (Nat.le_of_not_lt ht)]
      exact Or.inr (hR _ h1)
  · apply hR
    by_cases ht : t < st.aktiv.length
    · by_cases hu : u < st.aktiv.length
      · exact (hi t ht).2 u hu htu he
      · rw [he, st.init_ab (Nat.le_of_not_lt hu)]
        exact h1
    · rw [st.init_ab (Nat.le_of_not_lt ht)]
      exact h1
  · show wahr? (eval (sp.welt []) (P.requires (st.init t).1) (sp.welt []) (st.init t).2) = true
    rcases st.init_mem t with e | e
    · rw [e]
      exact (List.all_eq_true.mp h3) _ List.mem_cons_self
    · exact (List.all_eq_true.mp h3) _ (List.mem_cons_of_mem _ e)

end Tafel

#print axioms Gabbro.Grammatik.getrenntW_iff
#print axioms Gabbro.Grammatik.schreibGetrenntW_iff
#print axioms Gabbro.Grammatik.rennB_iff
#print axioms Gabbro.Grammatik.akzeptiert_iff
#print axioms Gabbro.Grammatik.akzeptiert_pruefer
#print axioms Gabbro.Grammatik.ruheB_iff
#print axioms Gabbro.Grammatik.getrenntK_of
#print axioms Gabbro.Grammatik.schreibGetrenntK_of
#print axioms Gabbro.Grammatik.Akzeptiert_ok
#print axioms Gabbro.Grammatik.rennfreiBis_of
#print axioms Gabbro.Grammatik.startB_ok

end Gabbro.Grammatik
