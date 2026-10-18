/-
  File:      Grammatik/Gen/Erzeuger/Gueltig.lean
  Subject:   THE THEOREMS: soundness (S) and completeness (C) of the generator of VALID programs and of the
             generators of SINGLE-FAULT REFUSED programs, over the model's own acceptance `AkzeptiertX`.

  Valid  = `AkzeptiertX P S fs ls cs ws = true` (the Bool of the goal theorem's checker with the atomic rely).
  The Bool is the conjunction of TEN components (fragment, closedness, footprint, lock ranks, lock sites, roots,
  single-pool, race freedom, answers, masks); `komp c` is component `c`.
  Refused ONLY BY component `c` = component `c` is false and the other nine are true.

  Every `Programm D` is WELL TYPED by construction (the model's terms are intrinsically typed), so
  "well typed and refused only by `c`" is `nurAn c`.

  (S) `P ∈ genGueltig m → valid P`,  `P ∈ genBad c m → nurAn c P`   (and P is a `Programm D`, i.e. well typed)
  (C) `valid P → groesseProg P ≤ m → P ∈ genGueltig m`,  `nurAn c P → groesseProg P ≤ m → P ∈ genBad c m`
  and the union over `m` is every valid program, every single-fault program (`gueltig_alle`, `bad_alle`).
-/
import Grammatik.Gen.Erzeuger.Programm
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D]

/-- Component `c` of `AkzeptiertX`, in the order of the definition:
    0 fragment, 1 closedness, 2 footprint, 3 lock ranks, 4 lock sites, 5 roots, 6 single pool, 7 race freedom,
    8 answers, 9 masks. -/
def komp (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) : Fin 10 → Bool
  | 0 => programmImFragmentG P fs
  | 1 => abgAlleB P fs
  | 2 => fussWXB P S fs ws
  | 3 => stufenB P fs
  | 4 => sperrOrteB S ls
  | 5 => wurzelnB ws
  | 6 => einzelnPoolB P fs cs ws
  | 7 => rennB P fs cs ws
  | 8 => antwortenB P fs
  | 9 => maskenB P fs

/-- The Bool of the checker is the conjunction of the ten components. -/
theorem akzeptiertX_iff (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    AkzeptiertX P S fs ls cs ws = true ↔ ∀ c, komp P S fs ls cs ws c = true := by
  unfold AkzeptiertX
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ c
    rcases c with ⟨n, hn⟩
    match n, hn with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | 8, _ => exact h8
    | 9, _ => exact h9
    | n + 10, hn => exact absurd hn (by omega)
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩, h 5⟩, h 6⟩, h 7⟩, h 8⟩, h 9⟩

/-- **Refused only by component `c`**: `c` is false, the other nine components are true. -/
def NurAn (c : Fin 10) (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Prop :=
  komp P S fs ls cs ws c = false ∧ ∀ c', c' ≠ c → komp P S fs ls cs ws c' = true

instance (c : Fin 10) (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Decidable (NurAn c P S fs ls cs ws) := by
  unfold NurAn; infer_instance

/-- **The generator of valid programs** of size at most `m`: the generated programs the checker accepts. -/
def genGueltig (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (m : Nat) : List (Programm D) :=
  (genProg m).filter fun P => AkzeptiertX P S fs ls cs ws

/-- **The generator of single-fault refusals** of component `c`, size at most `m`. -/
def genBad (c : Fin 10) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (m : Nat) : List (Programm D) :=
  (genProg m).filter fun P => decide (NurAn c P S fs ls cs ws)

variable (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn)

/-- **(S) Soundness, valid.** -/
theorem gueltig_korrekt {m : Nat} {P : Programm D} (h : P ∈ genGueltig S fs ls cs ws m) :
    AkzeptiertX P S fs ls cs ws = true := by
  unfold genGueltig at h
  exact (List.mem_filter.1 h).2

/-- **(C) Completeness, valid, bounded by size.** -/
theorem gueltig_vollst {m : Nat} {P : Programm D} (hv : AkzeptiertX P S fs ls cs ws = true)
    (hg : groesseProg P ≤ m) : P ∈ genGueltig S fs ls cs ws m := by
  unfold genGueltig
  exact List.mem_filter.2 ⟨genProg_vollst m P hg, hv⟩

/-- **(C) for all valid programs: the union over the size bound.** -/
theorem gueltig_alle {P : Programm D} (hv : AkzeptiertX P S fs ls cs ws = true) :
    ∃ m, P ∈ genGueltig S fs ls cs ws m :=
  ⟨groesseProg P, gueltig_vollst S fs ls cs ws hv (Nat.le_refl _)⟩

/-- **(S) Soundness, single fault**: a generated program is refused by exactly the labelled component. -/
theorem bad_korrekt {c : Fin 10} {m : Nat} {P : Programm D} (h : P ∈ genBad c S fs ls cs ws m) :
    NurAn c P S fs ls cs ws := by
  unfold genBad at h
  exact of_decide_eq_true (List.mem_filter.1 h).2

/-- **(C) Completeness, single fault, bounded by size.** -/
theorem bad_vollst {c : Fin 10} {m : Nat} {P : Programm D} (hv : NurAn c P S fs ls cs ws)
    (hg : groesseProg P ≤ m) : P ∈ genBad c S fs ls cs ws m := by
  unfold genBad
  exact List.mem_filter.2 ⟨genProg_vollst m P hg, decide_eq_true hv⟩

/-- **(C) for all single-fault programs of a component.** -/
theorem bad_alle {c : Fin 10} {P : Programm D} (hv : NurAn c P S fs ls cs ws) :
    ∃ m, P ∈ genBad c S fs ls cs ws m :=
  ⟨groesseProg P, bad_vollst S fs ls cs ws hv (Nat.le_refl _)⟩

/-- A program is valid iff no component refuses it; refused by at least one iff `¬ valid`. -/
theorem gueltig_oder_nicht (P : Programm D) :
    AkzeptiertX P S fs ls cs ws = true ∨ ∃ c, komp P S fs ls cs ws c = false := by
  by_cases h : AkzeptiertX P S fs ls cs ws = true
  · exact Or.inl h
  · right
    refine Classical.byContradiction fun hn => h ((akzeptiertX_iff P S fs ls cs ws).2 fun c => ?_)
    cases hc : komp P S fs ls cs ws c
    · exact absurd ⟨c, hc⟩ hn
    · rfl

end Gabbro.Grammatik.Gen
