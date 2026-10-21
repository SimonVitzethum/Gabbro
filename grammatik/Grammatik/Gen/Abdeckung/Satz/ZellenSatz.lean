/-
  File:      Grammatik/Gen/Abdeckung/Satz/ZellenSatz.lean
  Subject:   THE CELLS ARE THE CHECKER, as theorems (step 1 of making M and N complete in the sense of Theorem 4):
             for every program, the verdict recomputed from the cells of a component (`urteilAusZellen`) IS the
             component of the Lean model's Bool (`komp`). Until now this was only evaluated on generated programs
             (`zellenStimmen`); here it is proved for all of them, one component at a time.

  Hypotheses: the member lists are complete (`hvoll`: every function, `hls`: every lock, `hcs`: every carrier), as in
  `akzeptiert_iff`. All ten components are proved here (`urteil_0` .. `urteil_9`), and `akzeptiertX_zellen` puts them together; the
  feature-set tools are in `MerkmalUnd`, `MerkmalZerlegt` and `MerkmalGOk`.
-/
import Grammatik.Gen.Abdeckung.Satz.MerkmalGOk

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-- A cell of a verdict kind is bad exactly when its test fails. -/
theorem schlecht_urteil {k a : Nat} {v : List Bool} :
    (Zelle.mk k a true v).schlecht = !(Zelle.mk k a true v).kern := by
  simp [Zelle.schlecht]

/-- **Component 5 (roots)**: the cells decide it. -/
theorem urteil_5 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 5 = komp P S fs ls cs ws 5 := by
  simp only [urteilAusZellen, zellen, komp, wurzelnB, List.all_map, Function.comp_def, Zelle.schlecht,
    Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]

/-- **Component 4 (lock sites)**: the cells decide it, over a complete list of carriers. -/
theorem urteil_4 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    urteilAusZellen P S fs ls cs ws 4 = komp P S fs ls cs ws 4 := by
  simp only [urteilAusZellen, zellen, komp, sperrOrteB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h L hL c hc
    rcases h L hL c (hcs c) with h1 | h1
    · rw [istIn_iff.mpr hc] at h1; cases h1
    · exact h1
  · intro h L hL c _
    cases hi : istIn (S.orte L) c
    · exact Or.inl rfl
    · exact Or.inr (h L hL c (istIn_iff.mp hi))

/-! ## Components 1, 3, 9 -/

/-- **Component 3 (lock ranks)**. -/
theorem urteil_3 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hls : ∀ L : D.Lock, L ∈ ls) :
    urteilAusZellen P S fs ls cs ws 3 = komp P S fs ls cs ws 3 := by
  simp only [urteilAusZellen, zellen, komp, stufenB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext f
  rw [show bodenM f = (⟨fun _ => true, fun _ => true, (bodenM f).sperre⟩ : Merkmal D) from rfl,
    sperrMerkmal_zerlegt ls hls]
  apply congrArg (List.all ls); funext L
  rw [nimmtB_eq]
  generalize mE (ohneSperre L) (P.rumpf f) = x
  generalize (bodenM f).sperre L = y
  cases x <;> cases y <;> rfl

/-- **Component 9 (masks)**. -/
theorem urteil_9 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hls : ∀ L : D.Lock, L ∈ ls) :
    urteilAusZellen P S fs ls cs ws 9 = komp P S fs ls cs ws 9 := by
  simp only [urteilAusZellen, zellen, komp, maskenB, maskenDisziplinB, List.all_flatMap, List.all_map,
    Function.comp_def, Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext w
  cases P.unterbricht w
  · simp
  · simp only [Bool.not_true, Bool.false_or, Bool.true_and]
    apply congrArg (List.all fs); funext f
    cases reachB P fs w f
    · simp
    · simp only [Bool.not_true, Bool.false_or, Bool.true_and]
      rw [show NurMaskiert D = (⟨fun _ => true, fun _ => true, D.maskiert⟩ : Merkmal D) from rfl,
        sperrMerkmal_zerlegt ls hls]
      apply congrArg (List.all ls); funext L
      rw [nimmtB_eq]
      generalize mE (ohneSperre L) (P.rumpf f) = x
      generalize D.maskiert L = y
      cases x <;> cases y <;> rfl

/-- **Component 1 (closedness)**. -/
theorem urteil_1 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) :
    urteilAusZellen P S fs ls cs ws 1 = komp P S fs ls cs ws 1 := by
  simp only [urteilAusZellen, zellen, komp, abgAlleB, abgB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext w
  apply congrArg (List.all fs); funext f
  cases reachB P fs w f
  · simp
  · simp only [Bool.not_true, Bool.false_or, Bool.true_and]
    rw [rufM_zerlegt fs hvoll]
    apply congrArg (List.all fs); funext g
    rw [ruftB_eq]
    generalize mE (ohneRuf g) (P.rumpf f) = x
    generalize reachB P fs w g = y
    cases x <;> cases y <;> rfl

/-! ## Components 2, 6, 7, 8 -/

theorem all_wahr {α : Type} (l : List α) : (l.all fun _ => true) = true := by
  induction l <;> simp_all

theorem all_und {α : Type} (l : List α) (p q : α → Bool) :
    (l.all p && l.all q) = l.all fun x => p x && q x := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, ← ih]
    cases p a <;> cases q a <;> simp

theorem all_oder {α : Type} (l : List α) (b : Bool) (p : α → Bool) :
    (l.all fun x => b || p x) = (b || l.all p) := by
  cases b <;> simp [all_wahr]

/-- **Component 8 (answers)**, over the complete lists of foreign bodies and registers. -/
theorem urteil_8 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 8 = komp P S fs ls cs ws 8 := by
  simp only [urteilAusZellen, zellen, komp, antwortenB, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not]
  apply congrArg (List.all fs); funext f
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  have hvoll : ∀ x : D.Ax ⊕ D.Reg, x ∈ (Aufz.ax (D := D)).map Sum.inl ++ (Aufz.reg (D := D)).map Sum.inr := by
    intro x; cases x with
    | inl a => exact List.mem_append_left _ (List.mem_map_of_mem (Aufz.ax_mem a))
    | inr r => exact List.mem_append_right _ (List.mem_map_of_mem (Aufz.reg_mem r))
  constructor
  · intro h x hx
    have := h x (hvoll x)
    cases x <;> simp_all [stelleB]
  · intro h x _
    by_cases hx : x ∈ (P.rumpf f).ants
    · have := h x hx
      cases x <;> simp_all [stelleB]
    · simp [hx]

/-- **Component 7 (race freedom)**: its verdict cells decide it; the cells of `schreibGetrennt` are derived and never
    refuse. -/
theorem urteil_7 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 7 = komp P S fs ls cs ws 7 := by
  simp only [urteilAusZellen, zellen, komp, rennB, schreibGetrenntZellen, List.all_flatMap, List.all_append,
    List.all_cons, List.all_nil, List.all_map, Function.comp_def, Zelle.schlecht, Zelle.kern, Zelle.kern?,
    Option.getD_some, Bool.true_and, Bool.false_and, Bool.not_false, Bool.not_not, Bool.and_true, all_wahr]

/-- **Component 6 (single pool)**. -/
theorem urteil_6 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 6 = komp P S fs ls cs ws 6 := by
  simp only [urteilAusZellen, zellen, komp, einzelnPoolB, poolSicherWB, ausgenommenB, List.all_flatMap,
    List.all_append, List.all_map, Function.comp_def, Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some,
    Bool.true_and, Bool.not_not]
  rw [all_und]
  apply congrArg (List.all ws); funext w
  cases mehrfachB ws w <;> simp [all_oder, all_wahr, Bool.or_assoc]

/-- **Component 2 (footprint)**: its verdict cells (the footprint and the register part) decide it; the cells of
    `getrennt` and `geteilt` are derived and never refuse. -/
theorem urteil_2 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 2 = komp P S fs ls cs ws 2 := by
  simp only [urteilAusZellen, zellen, komp, fussWXB, getrenntZellen, geteiltZelle, List.all_flatMap,
    List.all_append, List.all_cons, List.all_nil, List.all_map, Function.comp_def, Zelle.schlecht, Zelle.kern,
    Zelle.kern?, Option.getD_some, Bool.true_and, Bool.false_and, Bool.not_false, Bool.not_not, Bool.and_true,
    all_wahr]
  rw [all_und]

/-- **Component 0 (fragment)**. -/
theorem urteil_0 (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    urteilAusZellen P S fs ls cs ws 0 = komp P S fs ls cs ws 0 := by
  simp only [urteilAusZellen, zellen, komp, programmImFragmentG, List.all_flatMap, List.all_map, Function.comp_def,
    Zelle.schlecht, Zelle.kern, Zelle.kern?, Option.getD_some, Bool.true_and, Bool.not_not, gOk_ohne_test]
  apply congrArg (List.all fs); funext f
  rw [show kandB P fs (fussOrteG P f) = fun n => fs.all fun g => !(D.passt g n) ||
      ((P.requires g).orte ++ (P.ensures g).orte).all fun o => (fussOrteG P f).any fun o' => decide (o' = o) from rfl,
    eGOk, kand_zerlegt]
  apply congrArg (List.all fs); funext g
  rw [indB_eq]
  generalize mE (ohneInd g) (P.rumpf f) = x
  have hc : ((vertragsOrte P g).any fun o => !(istIn (fussOrteG P f) o)) =
      !(((P.requires g).orte ++ (P.ensures g).orte).all fun o => (fussOrteG P f).any fun o' => decide (o' = o)) := by
    simp only [vertragsOrte, istIn]
    exact any_nicht _ _
  rw [hc]
  generalize (((P.requires g).orte ++ (P.ensures g).orte).all fun o => (fussOrteG P f).any fun o' => decide (o' = o)) = y
  cases x <;> cases y <;> rfl

/-! ## Step 1: the model's Bool is the conjunction over the cells -/

/-- Every component is decided by its cells, over complete member lists. -/
theorem urteil_komp (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (c : Fin 10) :
    urteilAusZellen P S fs ls cs ws c = komp P S fs ls cs ws c := by
  rcases c with ⟨n, hn⟩
  match n, hn with
  | 0, _ => exact urteil_0 P S fs ls cs ws
  | 1, _ => exact urteil_1 P S fs ls cs ws hvoll
  | 2, _ => exact urteil_2 P S fs ls cs ws
  | 3, _ => exact urteil_3 P S fs ls cs ws hls
  | 4, _ => exact urteil_4 P S fs ls cs ws hcs
  | 5, _ => exact urteil_5 P S fs ls cs ws
  | 6, _ => exact urteil_6 P S fs ls cs ws
  | 7, _ => exact urteil_7 P S fs ls cs ws
  | 8, _ => exact urteil_8 P S fs ls cs ws
  | 9, _ => exact urteil_9 P S fs ls cs ws hls
  | n + 10, hn => exact absurd hn (by omega)

/-- All cells of a program. -/
def alleZellen (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : List Zelle :=
  (List.finRange 10).flatMap (zellen P S fs ls cs ws)

/-- **Step 1.** The Lean model's Bool accepts a program exactly when the program has no bad cell. This is what makes
    the checker of the goal theorem a CONJUNCTIVE checker over the cells (the class of Theorems 4 and 5). -/
theorem akzeptiertX_zellen (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) :
    AkzeptiertX P S fs ls cs ws = true ↔ ∀ z ∈ alleZellen P S fs ls cs ws, z.schlecht = false := by
  rw [akzeptiertX_iff]
  constructor
  · intro h z hz
    obtain ⟨c, _, hzc⟩ := List.mem_flatMap.1 hz
    have := urteil_komp P S fs ls cs ws hvoll hls hcs c
    rw [h c] at this
    have h2 := (List.all_eq_true.1 this) z hzc
    simpa using h2
  · intro h c
    rw [← urteil_komp P S fs ls cs ws hvoll hls hcs c]
    apply List.all_eq_true.2
    intro z hz
    have := h z (List.mem_flatMap.2 ⟨c, List.mem_finRange c, hz⟩)
    simp [this]

end Gabbro.Grammatik.Gen
