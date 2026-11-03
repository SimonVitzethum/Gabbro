module

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Kern.Syntax.Satz.T3
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte
public import Grammatik.Logik.Vertraege.EinpassenVoll
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil3
public import Grammatik.Zielsatz.Kern.Akzeptiert.Bibliothek

@[expose] public section



namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

section Akzeptiert

variable [DecidableEq D.Fn]

/-! ## 0. "Declared at least twice", decided (fix lane F10) -/

/-- "Declared at least twice" is "filtering for it leaves two or more". -/
theorem mehrfach_filter {α : Type} [DecidableEq α] {ws : List α} {w : α} :
    Mehrfach ws w ↔ 1 < (ws.filter (fun v => decide (v = w))).length := by
  constructor
  · intro h
    have h1 := (h.filter (fun v => decide (v = w))).length_le
    have h2 : ([w, w].filter (fun v => decide (v = w))).length = 2 := by simp only [decide_true, List.filter_cons_of_pos, List.filter_nil, List.length_cons, List.length_nil,
  Nat.zero_add, Nat.reduceAdd]
    omega
  · induction ws with
    | nil => intro h; simp only [List.filter_nil, List.length_nil, Nat.not_lt_zero] at h
    | cons a l ih =>
        intro h
        by_cases he : a = w
        · subst he
          simp only [List.filter_cons, decide_true, if_true, List.length_cons] at h
          have hpos : 0 < (l.filter (fun v => decide (v = a))).length := by omega
          obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
          have hxl := (List.mem_filter.mp hx)
          have hxa : x = a := of_decide_eq_true hxl.2
          subst hxa
          exact List.Sublist.cons_cons x (List.singleton_sublist.mpr hxl.1)
        · have h' : 1 < (l.filter (fun v => decide (v = w))).length := by
            simpa [List.filter_cons, he] using h
          exact List.Sublist.cons a (ih h')

/-- `w` is declared at least twice in `ws`, decided. -/
def mehrfachB (ws : List D.Fn) (w : D.Fn) : Bool :=
  decide (1 < (ws.filter (fun v => decide (v = w))).length)

theorem mehrfachB_iff {ws : List D.Fn} {w : D.Fn} : mehrfachB ws w = true ↔ Mehrfach ws w := by
  unfold mehrfachB
  rw [decide_eq_true_iff, mehrfach_filter]

/-- On a repetition-free list nothing is declared twice. -/
theorem nicht_mehrfach_of_nodup {α : Type} {ws : List α} (hnd : ws.Nodup) (w : α) :
    ¬ Mehrfach ws w := fun h => by
  have := List.Nodup.sublist h hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_true_eq_false, not_false_eq_true,
  List.nodup_nil, and_self, and_true] at this

/-! ## 1. Thread-locality over the declared starts -/

/-- **`c` is thread-local among the declared starts** (reads against
    writes): for every two DIFFERENT declared start occurrences, no function
    the first reaches has `c` in its footprint while a function the second
    reaches may write it; a routine declared twice is paired with itself
    (fix lane F10). Decides Spec's `Getrennt`. -/
def getrenntW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  ws.all fun w1 => ws.all fun w2 => (decide (w1 = w2) && !(mehrfachB ws w1)) ||
    (fs.all fun f => !(reachB P fs w1 f) || !(istIn (fussOrteG P f) c)) ||
    (fs.all fun g => !(reachB P fs w2 g) || !(TraegerSchreibt g c))

theorem getrenntW_iff {P : Programm D} {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {c : D.Tab ⊕ D.Glob} : getrenntW P fs ws c = true ↔ Getrennt P fs ws c := by
  constructor
  · intro h w1 hw1 w2 hw2 hne f g hf hc hg
    have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) w1 hw1)) w2 hw2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    rcases h1 with (h1 | h1) | h1
    · rcases hne with hne | hne
      · exact absurd h1.1 hne
      · rw [mehrfachB_iff.mpr hne] at h1
        cases h1.2
    · have h2 := (List.all_eq_true.mp h1) f (hvoll f)
      rw [hf, istIn_iff.mpr hc] at h2
      simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true] at h2
    · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
      rw [hg] at h2
      simpa using h2
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2 ∧ mehrfachB ws w1 = false
    · obtain ⟨rfl, hm⟩ := hne
      simp only [decide_true, hm, Bool.not_false, Bool.and_self, Bool.true_or]
    have hne' : w1 ≠ w2 ∨ Mehrfach ws w1 := by
      by_cases he : w1 = w2
      · refine Or.inr (mehrfachB_iff.mp ?_)
        cases hm : mehrfachB ws w1
        · exact absurd ⟨he, hm⟩ hne
        · rfl
      · exact Or.inl he
    by_cases hfr : (fs.all fun f => !(reachB P fs w1 f) || !(istIn (fussOrteG P f) c)) = true
    · simp only [hfr, Bool.or_true, Bool.true_or]
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
          · simp only [Bool.not_true, h w1 hw1 w2 hw2 hne' f g hf hc hg, Bool.not_false, Bool.or_true]
      simp only [hw, Bool.or_true]

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
      simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true] at h2
    · have h2 := (List.all_eq_true.mp h1) k (hvoll k)
      rw [hk] at h2
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h2
      exact ⟨h2.1, fun hc => by rw [istIn_iff.mpr hc] at h2; cases h2.2⟩
  · intro h
    refine List.all_eq_true.mpr fun w1 hw1 => List.all_eq_true.mpr fun w2 hw2 => ?_
    by_cases hne : w1 = w2
    · simp only [hne, decide_true, Bool.true_or]
    by_cases hfr : (fs.all fun g => !(reachB P fs w1 g) || !(TraegerSchreibt g c)) = true
    · simp only [hfr, Bool.or_true, Bool.true_or]
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
            simp only [Bool.not_true, h1, Bool.not_false, h3, Bool.and_self, Bool.or_true]
      simp only [hw, Bool.or_true]

/-! ## 2. The exemptions of the race component -/

/-- An `atomic` global (`AtomarAusgenommen`), decided. -/
def atomarB : D.Tab ⊕ D.Glob → Bool
  | .inl _ => false
  | .inr g => D.atomar g

/-- The carrier needs no write separation: it has a guard lock, or it is
    `atomic`. A publish payload is NOT exempt (since 2026-09-15, verdict P3:
    two starts writing one unguarded payload is a C11 race on a non-atomic
    object; `H013` has no payload exemption either). -/
def ausgenommenB (c : D.Tab ⊕ D.Glob) : Bool :=
  !(waechterVon c).isEmpty || atomarB c

theorem ausgenommenB_false {c : D.Tab ⊕ D.Glob} :
    ausgenommenB c = false ↔ (∀ L, ¬ Bewacht c L) ∧ ¬ AtomarAusgenommen c := by
  unfold ausgenommenB
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff]
  constructor
  · rintro ⟨hw, ha⟩
    refine ⟨fun L hL => ?_, ?_⟩
    · have := waechterVon_mem.mpr hL
      rw [hw] at this
      exact absurd this List.not_mem_nil
    · rintro ⟨g, rfl, hg⟩
      simp only [atomarB, hg, Bool.true_eq_false] at ha
  · rintro ⟨hB, hA⟩
    refine ⟨?_, ?_⟩
    · cases hw : waechterVon c with
      | nil => rfl
      | cons L _ => exact absurd (waechterVon_mem.mp (by rw [hw]; exact List.mem_cons_self)) (hB L)
    · cases c with
      | inl t => rfl
      | inr g =>
          cases hg : D.atomar g
          · simp only [atomarB, hg]
          · exact absurd ⟨g, rfl, hg⟩ hA

/-- **The race component**: every carrier that needs it is write-separated
    among the declared starts. -/
def rennB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    Bool :=
  cs.all fun c => ausgenommenB c || schreibGetrenntW P fs ws c

theorem rennB_iff {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    rennB P fs cs ws = true ↔ ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c →
      SchreibGetrennt P fs ws c := by
  constructor
  · intro h c hB hA
    have h1 := (List.all_eq_true.mp h) c (hcs c)
    rw [ausgenommenB_false.mpr ⟨hB, hA⟩, Bool.false_or] at h1
    exact (schreibGetrenntW_iff hvoll).mp h1
  · intro h
    refine List.all_eq_true.mpr fun c _ => ?_
    cases ha : ausgenommenB c
    · obtain ⟨hB, hA⟩ := ausgenommenB_false.mp ha
      rw [Bool.false_or]
      exact (schreibGetrenntW_iff hvoll).mpr (h c hB hA)
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

/-- **The scope discipline on every body (C11)**: every `retScoped`/
    `retWhyScoped` releases only locks outside the residual and at or
    above the floor (`ScopesOkProg`). The Satz carries it as a premise
    (`rufAt_gut`, `exec_gut`); the checker decides it here. -/
def scopesOkProgB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).scopesOk (D.signatur f).haelt (D.signatur f).boden

/-- Every protected carrier is guarded by its lock (first half of
    `SperrInvOk`). -/
def sperrOrteB (S : SperrInv D) (ls : List D.Lock) : Bool :=
  ls.all fun L => (S.orte L).all fun c => decide (L ∈ waechterVon c)

/-- No declared start holds a lock by signature (`N240`, strong form) or has
    reasons (a start's reason has no caller to go to). -/
def wurzelnB (ws : List D.Fn) : Bool :=
  ws.all fun w => (D.haelt w).isEmpty && decide (D.gruende w = 0)

/-- The declared starts are pairwise distinct -- the `einzeln` component from
    2026-09-15 until fix lane F10 (2026-09-22), which replaced it by
    `einzelnPoolB`. Kept for the "never weakened" statements of PoolSym.lean
    (`akzeptiert_nodup_gleich`). -/
def einzelnB (ws : List D.Fn) : Bool :=
  decide ws.Nodup

/-- **Pool-safe, decided**: no signature lock, no reasons, and every
    function the graph reaches writes only carriers of the list `cs`
    that are guarded or atomic. Decides `PoolSicherW` given complete
    member lists (lane 245; moved here by fix lane F10). -/
def poolSicherWB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && decide (D.gruende w = 0) && fs.all fun f =>
    !(reachB P fs w f) ||
      (cs.all fun c => !(TraegerSchreibt f c) ||
        (!(waechterVon c).isEmpty || atomarB c))

/-- **The start component since fix lane F10** (`EinzelnPool`): every
    routine declared at least twice is pool-safe. Replaces `einzelnB`: the
    runtime runs each declared occurrence on its own thread, and a routine
    on two threads is admitted when no instance can write a carrier the
    other could race on (the race leg), while the footprint leg pairs the
    two occurrences in `getrenntW`. The Rust checker's `N304`. -/
def einzelnPoolB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) : Bool :=
  ws.all fun w => !(mehrfachB ws w) || poolSicherWB P fs cs w

/-- **An answer site, decided** (`StelleOk`, AntwortOrte.lean; round-6 finding W1): an axiom
    whose declared result is `never`, or a site whose declared answer type has a value over
    the function list `fs` (`antwortB`, EinpassenVoll.lean). -/
def stelleB (fs : List D.Fn) : D.Ax ⊕ D.Reg → Bool
  | .inl a => decide (D.aerg a = some .never) || antwortB fs (D.aerg a)
  | .inr r => antwortB fs (some (D.rtyp r))

/-- **The answer component** (2026-09-15, W1): no body calls an axiom or reads a register at
    a declared answer type without a value, except an axiom `-> never`. -/
def antwortenB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).ants.all (stelleB fs)

/-- **`H102` over a member list** (Opus agent H, 2026-09-26; before, fix lane F11, over the
    feature set `maskM`): every function of the call graph of `w` takes only locks declared
    `masks irqs`. The Rust checker decides the same over the handler's effect hull
    (`kontexte.rs`, `H102`). -/
def maskenDisziplinB (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Bool :=
  fs.all fun f => !(reachB P fs w f) || mE (NurMaskiert D) (P.rumpf f)

/-- **The handler component** (Opus agent H, 2026-09-26, OFFEN O19): every function the program
    declares entered by hardware (`P.unterbricht`, `entry … via idt`) meets the discipline. On a
    program with no handler it is `true` (`maskenB_ohne`). -/
def maskenB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun w => !(P.unterbricht w) || maskenDisziplinB P fs w

/-- **`Akzeptiert` -- what the checker decides, as ONE Bool.** The last conjunct is the C02
    library binding: generated programs are ordinary, so it holds by construction
    (`libraryB_immer`); the content is source-level (`Uebersetzung.lean`). -/
def Akzeptiert [DecidableEq D.Ax] (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn)
    (aks : List (Kernzelle.AccumulatorDecl D) := []) (checks : List (CheckDecl D) := [])
    (aqs : List D.Ax := []) : Bool :=
  programmImFragmentG P fs && abgAlleB P fs && fussWB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && einzelnPoolB P fs cs ws && rennB P fs cs ws &&
    antwortenB P fs && maskenB P fs && schnittstellenB P fs && resetB cs && libraryB P fs && Kernzelle.accumulatorB P fs (tabsOf cs) (globsOf cs) aqs aks && checkB P (tabsOf cs) (globsOf cs) fs checks && scopesOkProgB P fs

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
    · simp only [Bool.not_true, h w f hf, Bool.or_true]

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
theorem scopesOkProgB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    scopesOkProgB P fs = true ↔ ScopesOkProg P :=
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

omit [DecidableEq D.Fn] in
theorem stelleB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) (x : D.Ax ⊕ D.Reg) :
    stelleB fs x = true ↔ StelleOk D x := by
  cases x with
  | inl a =>
      simp only [stelleB, StelleOk, Bool.or_eq_true, decide_eq_true_eq]
      rw [antwortB_iff hvoll]
  | inr r =>
      show antwortB fs (some (D.rtyp r)) = true ↔ ¬ AntwortLeer D (some (D.rtyp r))
      exact antwortB_iff hvoll _

omit [DecidableEq D.Fn] in
/-- **The answer component decides its field** (`AkzeptiertSpec.antworten`). -/
theorem antwortenB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    antwortenB P fs = true ↔ ∀ f, ∀ x ∈ (P.rumpf f).ants, StelleOk D x := by
  unfold antwortenB
  constructor
  · intro h f x hx
    exact (stelleB_iff hvoll x).mp (List.all_eq_true.mp ((List.all_eq_true.mp h) f (hvoll f)) x hx)
  · intro h
    exact List.all_eq_true.mpr fun f _ => List.all_eq_true.mpr fun x hx =>
      (stelleB_iff hvoll x).mpr (h f x hx)

end Komponenten
end Akzeptiert
end Gabbro.Grammatik
