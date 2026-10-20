/-
  File:      Grammatik/Gen/Abdeckung/ZellenUnmoeglich.lean
  Subject:   THE CELLS NO PROGRAM HAS, and the bad cells that never come alone (steps 2 and 3 of making M and N complete,
             `Adaequanz/Vollstaendig.lean`). A cell that no program has needs no test; a good cell that no VALID program
             has needs no valid test; a bad cell that always comes with another bad cell needs no single-fault test of its
             own, as long as the other one has one. Each of these is a theorem over EVERY program, not a measurement.
-/
import Grammatik.Gen.Abdeckung.ZellenSatz

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-- A cell of `alleZellen` is a cell of one component. -/
theorem mem_alleZellen {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} {z : Zelle} :
    z ∈ alleZellen P S fs ls cs ws ↔ ∃ c : Fin 10, z ∈ zellen P S fs ls cs ws c := by
  simp [alleZellen, List.mem_flatMap]

/-- Every cell of component `c` carries `c`. -/
theorem zellen_komp {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} {c : Fin 10} {z : Zelle} (h : z ∈ zellen P S fs ls cs ws c) :
    z.komp = c.val := by
  rcases c with ⟨n, hn⟩
  match n, hn with
  | 0, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | 1, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, _, _, rfl⟩ := h; rfl
  | 2, _ =>
    simp only [zellen, getrenntZellen, geteiltZelle, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with ⟨_, _, _, _, (rfl | ⟨_, _, _, _, rfl⟩) | rfl⟩ | ⟨_, _, _, _, rfl | ⟨_, _, _, _, rfl⟩⟩ <;> rfl
  | 3, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | 4, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | 5, _ => simp only [zellen, List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | 6, _ =>
    simp only [zellen, List.mem_append, List.mem_flatMap, List.mem_map] at h
    rcases h with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;> rfl
  | 7, _ =>
    simp only [zellen, schreibGetrenntZellen, List.mem_flatMap, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false, List.mem_map] at h
    rcases h with ⟨_, _, rfl | ⟨_, _, _, _, rfl⟩⟩ <;> rfl
  | 8, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | 9, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, _, _, rfl⟩ := h; rfl
  | n + 10, hn => exact absurd hn (by omega)

/-- A cell of component `k` lies in the cells of `k`. -/
theorem mem_alleZellen_k {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} {z : Zelle} (k : Fin 10) (hk : z.komp = k.val)
    (h : z ∈ alleZellen P S fs ls cs ws) : z ∈ zellen P S fs ls cs ws k := by
  obtain ⟨c, hc⟩ := mem_alleZellen.1 h
  have := zellen_komp hc
  have hck : c = k := Fin.ext (by omega)
  exact hck ▸ hc

/-! ## Cells that no program has -/

/-- **`0.0 0..`**: the fragment without its indirect-call test is always true. -/
theorem zelle_0_ohne_gOk (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (b c : Bool) :
    (⟨0, 0, true, [false, b, c]⟩ : Zelle) ∉ alleZellen P S fs ls cs ws := by
  intro h
  have h0 := mem_alleZellen_k (0 : Fin 10) rfl h
  simp only [zellen, List.mem_flatMap, List.mem_map, Zelle.mk.injEq, List.cons.injEq] at h0
  obtain ⟨f, _, g, _, -, -, -, hf, -⟩ := h0
  rw [gOk_ohne_test] at hf
  cases hf

/-- **`7.1 110`**: with `w1 = w2`, the writer the first start reaches is reached by the second. -/
theorem zelle_7_1_110 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    (⟨7, 1, false, [true, true, false]⟩ : Zelle) ∉ alleZellen P S fs ls cs ws := by
  intro h
  have h0 := mem_alleZellen_k (7 : Fin 10) rfl h
  simp only [zellen] at h0
  obtain ⟨c, _, h1⟩ := List.mem_flatMap.1 h0
  rcases List.mem_append.1 h1 with h2 | h2
  · simp at h2
  · simp only [schreibGetrenntZellen, List.mem_flatMap, List.mem_map] at h2
    obtain ⟨w1, _, w2, _, h3⟩ := h2
    simp only [Zelle.mk.injEq, List.cons.injEq, true_and, and_true] at h3
    obtain ⟨he, hb, hc⟩ := h3
    have hw : w1 = w2 := of_decide_eq_true he
    subst hw
    obtain ⟨g, hg, hgg⟩ := List.any_eq_true.1 hb
    have : (fs.any fun h => reachB P fs w1 h && (TraegerSchreibt h c || istIn (fussOrteG P h) c)) = true := by
      apply List.any_eq_true.2
      refine ⟨g, hg, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hgg ⊢
      exact ⟨hgg.1, Or.inl hgg.2⟩
    rw [this] at hc
    cases hc

/-- **`8.0 .11`**: a foreign body that never returns has an answer type without a value. -/
theorem zelle_8_never (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (a : Bool) :
    (⟨8, 0, true, [a, true, true]⟩ : Zelle) ∉ alleZellen P S fs ls cs ws := by
  intro h
  have h0 := mem_alleZellen_k (8 : Fin 10) rfl h
  simp only [zellen, List.mem_flatMap, List.mem_map, Zelle.mk.injEq, List.cons.injEq] at h0
  obtain ⟨f, _, x, _, -, -, -, -, hb, hc, -⟩ := h0
  cases x with
  | inr r => simp at hb
  | inl a =>
    simp only at hb hc
    have hn : D.aerg a = some Ty.never := of_decide_eq_true hb
    rw [hn] at hc
    simp [antwortB, antwortTyB] at hc

/-! ## The pool cells of a start that holds a lock or has reasons come with a bad root cell -/

/-- **`6.0 x1x`, `6.0 xx1`**: the start `w` that holds a lock or has reasons is also a bad cell of component 5 with
    the same two atoms. -/
theorem zelle_6_0_braucht_5 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (m hh gg : Bool) (hbad : (hh || gg) = true)
    (h : (⟨6, 0, true, [m, hh, gg]⟩ : Zelle) ∈ alleZellen P S fs ls cs ws) :
    (⟨5, 0, true, [hh, gg]⟩ : Zelle) ∈ alleZellen P S fs ls cs ws ∧ (⟨5, 0, true, [hh, gg]⟩ : Zelle).schlecht = true := by
  have h0 := mem_alleZellen_k (6 : Fin 10) rfl h
  simp only [zellen, List.mem_append, List.mem_flatMap, List.mem_map, Zelle.mk.injEq, List.cons.injEq] at h0
  rcases h0 with ⟨w, hw, -, -, -, -, h1, h2, -⟩ | ⟨_, _, _, _, _, _, -, h3, -⟩
  · refine ⟨mem_alleZellen.2 ⟨5, ?_⟩, ?_⟩
    · simp only [zellen, List.mem_map]
      exact ⟨w, hw, by rw [h1, h2]⟩
    · cases hh <;> cases gg <;> simp_all [Zelle.schlecht, Zelle.kern, Zelle.kern?]
  · cases h3

/-- Hence a valid program has none of these good cells (`6.0 010`, `6.0 001`, `6.0 011`). -/
theorem zelle_6_0_nicht_gueltig (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (hv : AkzeptiertX P S fs ls cs ws = true) (m hh gg : Bool)
    (hbad : (hh || gg) = true) : (⟨6, 0, true, [m, hh, gg]⟩ : Zelle) ∉ alleZellen P S fs ls cs ws := by
  intro h
  obtain ⟨h5, hs⟩ := zelle_6_0_braucht_5 P S fs ls cs ws m hh gg hbad h
  have := (akzeptiertX_zellen P S fs ls cs ws hvoll hls hcs).1 hv _ h5
  rw [hs] at this
  cases this

/-! ## The call graph of a start is closed (`1.0 110` has no program) -/

section Huelle

variable (P : Programm D) (fs : List D.Fn) (w : D.Fn)

theorem erreich_mono (n : Nat) (g : D.Fn) (h : erreichB P fs w n g = true) : erreichB P fs w (n + 1) g = true := by
  simp [erreichB, erreichSchritt, h]

theorem filter_laenge_le {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    cases hp : p a <;> cases hq : q a <;> simp [List.filter_cons, hp, hq] <;> try omega
    exact absurd (h a List.mem_cons_self hp) (by simp [hq])

theorem filter_laenge_lt {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = true → q x = true)
    (x : α) (hx : x ∈ l) (hq : q x = true) (hp : p x = false) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    have hle := filter_laenge_le t p q fun y hy => h y (List.mem_cons_of_mem a hy)
    rcases List.mem_cons.1 hx with rfl | hxt
    · simp [List.filter_cons, hp, hq]; omega
    · have ih' := ih (fun y hy => h y (List.mem_cons_of_mem a hy)) hxt
      cases hpa : p a <;> cases hqa : q a <;> simp [List.filter_cons, hpa, hqa] <;> try omega
      exact absurd (h a List.mem_cons_self hpa) (by simp [hqa])

/-- A round that changes nothing changes nothing afterwards. -/
theorem erreich_fix (n : Nat) (hfix : erreichB P fs w (n + 1) = erreichB P fs w n) :
    ∀ k, erreichB P fs w (n + k) = erreichB P fs w n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show erreichSchritt P fs (erreichB P fs w (n + k)) = _
    rw [ih]
    exact hfix

/-- **The call graph after `|fs|` rounds is a fixed point**, over a complete function list. -/
theorem reach_fix (hvoll : ∀ g : D.Fn, g ∈ fs) :
    erreichB P fs w (fs.length + 1) = erreichB P fs w fs.length := by
  classical
  -- the count of reached functions after `n` rounds
  let cnt := fun n => (fs.filter (erreichB P fs w n)).length
  have hcnt0 : 1 ≤ cnt 0 := by
    have : 0 < (fs.filter (erreichB P fs w 0)).length :=
      List.length_pos_iff.2 (List.ne_nil_of_mem (List.mem_filter.2 ⟨hvoll w, by simp [erreichB]⟩))
    exact this
  have hle : ∀ n, cnt n ≤ fs.length := fun n => List.length_filter_le _ _
  -- if a round changes something, the count grows
  have hstep : ∀ n, erreichB P fs w (n + 1) ≠ erreichB P fs w n → cnt n + 1 ≤ cnt (n + 1) := by
    intro n hne
    have : ∃ g, erreichB P fs w (n + 1) g ≠ erreichB P fs w n g :=
      Classical.byContradiction fun hc => hne (funext fun g => Classical.byContradiction fun hg => hc ⟨g, hg⟩)
    obtain ⟨g, hg⟩ := this
    have hg1 : erreichB P fs w (n + 1) g = true ∧ erreichB P fs w n g = false := by
      cases h1 : erreichB P fs w (n + 1) g <;> cases h0 : erreichB P fs w n g <;> simp_all
      exact absurd (erreich_mono P fs w n g h0) (by simp [h1])
    exact filter_laenge_lt fs _ _ (fun x _ hx => erreich_mono P fs w n x hx) g (hvoll g) hg1.1 hg1.2
  -- if no round below `|fs|` were a fixed point, the count would exceed `|fs|`
  have hexists : ∃ n, n < fs.length + 1 ∧ erreichB P fs w (n + 1) = erreichB P fs w n := by
    refine Classical.byContradiction fun hc' => ?_
    have hc : ∀ n, n < fs.length + 1 → erreichB P fs w (n + 1) ≠ erreichB P fs w n :=
      fun n hn hf => hc' ⟨n, hn, hf⟩
    have hgrow : ∀ n, n ≤ fs.length + 1 → cnt 0 + n ≤ cnt n := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
        have := hstep n (hc n (by omega))
        have := ih (by omega)
        omega
    have := hgrow (fs.length + 1) (Nat.le_refl _)
    have := hle (fs.length + 1)
    omega
  obtain ⟨n, hn, hfix⟩ := hexists
  have h1 := erreich_fix P fs w n hfix (fs.length + 1 - n)
  have h2 := erreich_fix P fs w n hfix (fs.length - n)
  rw [show n + (fs.length + 1 - n) = fs.length + 1 by omega] at h1
  by_cases hnl : n ≤ fs.length
  · rw [show n + (fs.length - n) = fs.length by omega] at h2
    rw [h1, h2]
  · -- n = fs.length + 0 is impossible here since n < fs.length + 1 means n ≤ fs.length
    omega

/-- **The call graph of a start is closed**: a function that a reached function calls is reached. -/
theorem reach_abg (hvoll : ∀ g : D.Fn, g ∈ fs) (f g : D.Fn) (hf : reachB P fs w f = true)
    (hfg : ruftB P f g = true) : reachB P fs w g = true := by
  have : erreichB P fs w (fs.length + 1) g = true := by
    simp only [erreichB, erreichSchritt, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨f, hvoll f, hf, hfg⟩
  rw [reach_fix P fs w hvoll] at this
  exact this

end Huelle

/-- **`1.0 110`** has no program. -/
theorem zelle_1_0_110 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) :
    (⟨1, 0, true, [true, true, false]⟩ : Zelle) ∉ alleZellen P S fs ls cs ws := by
  intro h
  have h0 := mem_alleZellen_k (1 : Fin 10) rfl h
  simp only [zellen, List.mem_flatMap, List.mem_map, Zelle.mk.injEq, List.cons.injEq, true_and, and_true] at h0
  obtain ⟨w, _, f, _, g, _, h1, h2, h3⟩ := h0
  rw [reach_abg P fs w hvoll f g h1 h2] at h3
  cases h3

end Gabbro.Grammatik.Gen
