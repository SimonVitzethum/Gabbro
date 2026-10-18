/-
  File:      Grammatik/Gen/Erzeuger/Gueltig.lean
  Subject:   THE THEOREMS: soundness (S) and completeness (C) of the generator of VALID programs and of the generators
             of SINGLE-FAULT REFUSED programs, over the model's own acceptance `AkzeptiertX`.

  Valid  = `AkzeptiertX P S fs ls cs ws = true` (the Bool of the goal theorem's checker with the atomic rely).
  The Bool is the conjunction of TEN components (fragment, closedness, footprint, lock ranks, lock sites, roots,
  single-pool, race freedom, answers, masks); `komp c` is component `c`.
  Refused ONLY BY component `c` = component `c` is false and the other nine are true.

  Every `Programm D` is WELL TYPED by construction (the model's terms are intrinsically typed), so
  "well typed and refused only by `c`" is `NurAn c`.

  THE REDUCTIONS, each stated where it is used:
  * by SIZE: the streams are by exact size (`Gestuft.lean`), so the size bound of a theorem is the size of the
    program and nothing is generated beyond it.
  * PRUNING by the components that are conjunctions over the functions (the lock floors, `stufenB` = component 3,
    and the answers, `antwortenB` = component 8): a body that fails the component for its function is in no
    program that passes the component, so the bodies are filtered per function BEFORE the product. The other
    components (fragment, closedness, footprint, single-pool, race freedom, masks) read the call graph or the
    declared starts and are decided on the whole program at the end; the components of the starts and the lock
    sites (4, 5) do not read the program at all and are decided by the parameters.
  * CONTRACTS true in the workhorse stream (`Haut.programm`); the unreduced stream with every contract is `progS`.
    That a program with contracts is valid only if the same program with true contracts is valid is NOT proved
    here (the footprint reads the carriers of the contracts); the theorems below are about the programs of the
    stream, exactly.

  (S) `P ∈ genGueltig .. → valid P`,  `P ∈ genBad c .. → NurAn c P`
  (C) `valid (h.programm) → bounds → h.programm ∈ genGueltig .. (groesseHaut h)`, the same for `NurAn`, and the
      union over the size bound (`gueltig_alle`, `bad_alle`).
-/
import Grammatik.Gen.Erzeuger.Programm
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

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

/-! ## The pruning by the per-function components -/

/-- The body of `f` passes the lock floors (component 3, for this function). -/
def stufenOk (f : D.Fn) (b : Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))) :
    Bool := mE (bodenM f) b

/-- The body of `f` calls no axiom or reads no register at an answer type without a value (component 8). -/
def antwortOk (fs : List D.Fn) (f : D.Fn)
    (b : Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))) : Bool :=
  b.ants.all (stelleB fs)

/-- The filter that keeps the bodies which must pass component 3 (`p3`) and component 8 (`p8`). -/
def okFuer (p3 p8 : Bool) (fs : List D.Fn) (f : D.Fn)
    (b : Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))) : Bool :=
  (!p3 || stufenOk f b) && (!p8 || antwortOk fs f b)

variable {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn}

theorem stufenOk_of (hvoll : ∀ g : D.Fn, g ∈ fs) {P : Programm D} (h : komp P S fs ls cs ws 3 = true)
    (f : D.Fn) : stufenOk f (P.rumpf f) = true :=
  List.all_eq_true.1 h f (hvoll f)

theorem antwortOk_of (hvoll : ∀ g : D.Fn, g ∈ fs) {P : Programm D} (h : komp P S fs ls cs ws 8 = true)
    (f : D.Fn) : antwortOk fs f (P.rumpf f) = true :=
  List.all_eq_true.1 h f (hvoll f)

/-- A program that passes the components that must pass has every body accepted by the filter. -/
theorem okFuer_of (hvoll : ∀ g : D.Fn, g ∈ fs) {P : Programm D} {p3 p8 : Bool}
    (h3 : p3 = true → komp P S fs ls cs ws 3 = true) (h8 : p8 = true → komp P S fs ls cs ws 8 = true)
    (f : D.Fn) : okFuer p3 p8 fs f (P.rumpf f) = true := by
  unfold okFuer
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · cases hp : p3
    · exact Or.inl rfl
    · exact Or.inr (stufenOk_of hvoll (h3 hp) f)
  · cases hp : p8
    · exact Or.inl rfl
    · exact Or.inr (antwortOk_of hvoll (h8 hp) f)

/-! ## The generators -/

/-- **The generator of valid programs** of exact size `k` (the skeletons with bodies of size at most `n`): the
    generated programs the checker accepts. -/
def genGueltig (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (n : Nat) : Sz (Programm D) := fun k =>
  ((hautS (okFuer true true fs) n k).map Haut.programm).filter fun P => AkzeptiertX P S fs ls cs ws

/-- **The generator of single-fault refusals** of component `c`, exact size `k`. -/
def genBad (c : Fin 10) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (n : Nat) : Sz (Programm D) := fun k =>
  ((hautS (okFuer (decide (c ≠ 3)) (decide (c ≠ 8)) fs) n k).map Haut.programm).filter fun P =>
    decide (NurAn c P S fs ls cs ws)

/-- **(S) Soundness, valid.** -/
theorem gueltig_korrekt {n k : Nat} {P : Programm D} (h : P ∈ genGueltig S fs ls cs ws n k) :
    AkzeptiertX P S fs ls cs ws = true := by
  unfold genGueltig at h
  exact (List.mem_filter.1 h).2

/-- **(C) Completeness, valid.** A skeleton whose program (contracts true) is accepted, with every body of size at
    most `n`, is generated at its size. -/
theorem gueltig_vollst (hvoll : ∀ g : D.Fn, g ∈ fs) {n : Nat} (h : Haut D)
    (hv : AkzeptiertX h.programm S fs ls cs ws = true) (hn : ∀ f, groesseEnd (h.rumpf f) ≤ n)
    (hu : ∀ f, groesseEnd (h.rumpf f) < unendlich) : h.programm ∈ genGueltig S fs ls cs ws n (groesseHaut h) := by
  have hk := (akzeptiertX_iff _ S fs ls cs ws).1 hv
  have hok : ∀ f, okFuer true true fs f (h.rumpf f) = true := fun f =>
    okFuer_of (P := h.programm) hvoll (fun _ => hk 3) (fun _ => hk 8) f
  unfold genGueltig
  exact List.mem_filter.2 ⟨List.mem_map.2 ⟨h, hautS_vollst (okFuer true true fs) n h hn hu hok, rfl⟩, hv⟩

/-- **(C) for all valid skeletons: the union over the size bound.** -/
theorem gueltig_alle (hvoll : ∀ g : D.Fn, g ∈ fs) (h : Haut D)
    (hv : AkzeptiertX h.programm S fs ls cs ws = true) (hu : ∀ f, groesseEnd (h.rumpf f) < unendlich) :
    ∃ n, h.programm ∈ genGueltig S fs ls cs ws n (groesseHaut h) :=
  ⟨groesseHaut h, gueltig_vollst hvoll h hv (fun f => by
    unfold groesseHaut
    exact le_summe (fun f => groesseEnd (h.rumpf f)) (Aufz.fn_mem f)) hu⟩

/-- **(S) Soundness, single fault**: a generated program is refused by exactly the labelled component. -/
theorem bad_korrekt {c : Fin 10} {n k : Nat} {P : Programm D} (h : P ∈ genBad c S fs ls cs ws n k) :
    NurAn c P S fs ls cs ws := by
  unfold genBad at h
  exact of_decide_eq_true (List.mem_filter.1 h).2

/-- **(C) Completeness, single fault.** -/
theorem bad_vollst (hvoll : ∀ g : D.Fn, g ∈ fs) {c : Fin 10} {n : Nat} (h : Haut D)
    (hv : NurAn c h.programm S fs ls cs ws) (hn : ∀ f, groesseEnd (h.rumpf f) ≤ n)
    (hu : ∀ f, groesseEnd (h.rumpf f) < unendlich) :
    h.programm ∈ genBad c S fs ls cs ws n (groesseHaut h) := by
  have hok : ∀ f, okFuer (decide (c ≠ 3)) (decide (c ≠ 8)) fs f (h.rumpf f) = true := fun f =>
    okFuer_of (P := h.programm) hvoll
      (fun hp => hv.2 3 (by have h' : c ≠ 3 := by simpa using hp
                            exact fun e => h' e.symm))
      (fun hp => hv.2 8 (by have h' : c ≠ 8 := by simpa using hp
                            exact fun e => h' e.symm)) f
  unfold genBad
  exact List.mem_filter.2 ⟨List.mem_map.2 ⟨h, hautS_vollst _ n h hn hu hok, rfl⟩, decide_eq_true hv⟩

/-- **(C) for all single-fault skeletons of a component.** -/
theorem bad_alle (hvoll : ∀ g : D.Fn, g ∈ fs) {c : Fin 10} (h : Haut D) (hv : NurAn c h.programm S fs ls cs ws)
    (hu : ∀ f, groesseEnd (h.rumpf f) < unendlich) :
    ∃ n, h.programm ∈ genBad c S fs ls cs ws n (groesseHaut h) :=
  ⟨groesseHaut h, bad_vollst hvoll h hv (fun f => by
    unfold groesseHaut
    exact le_summe (fun f => groesseEnd (h.rumpf f)) (Aufz.fn_mem f)) hu⟩

/-- A program is valid iff no component refuses it; refused by at least one iff `¬ valid`. -/
theorem gueltig_oder_nicht (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    AkzeptiertX P S fs ls cs ws = true ∨ ∃ c, komp P S fs ls cs ws c = false := by
  by_cases h : AkzeptiertX P S fs ls cs ws = true
  · exact Or.inl h
  · right
    refine Classical.byContradiction fun hn => h ((akzeptiertX_iff P S fs ls cs ws).2 fun c => ?_)
    cases hc : komp P S fs ls cs ws c
    · exact absurd ⟨c, hc⟩ hn
    · rfl

/-! ## The unreduced statement: programs with every contract -/

/-- The valid programs among ALL programs (bodies of size at most `nb`, contracts of size at most `nc`). -/
def genGueltigAlle (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (nb nc : Nat) : Sz (Programm D) := fun k =>
  (progS nb nc k).filter fun P => AkzeptiertX P S fs ls cs ws

/-- **(C) for every program, contracts included.** -/
theorem gueltigAlle_vollst {nb nc : Nat} (P : Programm D) (hv : AkzeptiertX P S fs ls cs ws = true)
    (hb : ∀ f, groesseEnd (P.rumpf f) ≤ nb)
    (hc : ∀ f, groesseExpr (P.requires f) ≤ nc ∧ groesseExpr (P.ensures f) ≤ nc)
    (hi : ∀ i, groesseExpr (P.invariante i) ≤ nc) (hu : groesseProg P < unendlich) :
    P ∈ genGueltigAlle S fs ls cs ws nb nc (groesseProg P) :=
  List.mem_filter.2 ⟨progS_vollst nb nc P hb hc hi hu, hv⟩

/-- The single-fault programs of component `c` among ALL programs. -/
def genBadAlle (c : Fin 10) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob))
    (ws : List D.Fn) (nb nc : Nat) : Sz (Programm D) := fun k =>
  (progS nb nc k).filter fun P => decide (NurAn c P S fs ls cs ws)

/-- **(C) for every single-fault program, contracts included.** -/
theorem badAlle_vollst {c : Fin 10} {nb nc : Nat} (P : Programm D) (hv : NurAn c P S fs ls cs ws)
    (hb : ∀ f, groesseEnd (P.rumpf f) ≤ nb)
    (hc : ∀ f, groesseExpr (P.requires f) ≤ nc ∧ groesseExpr (P.ensures f) ≤ nc)
    (hi : ∀ i, groesseExpr (P.invariante i) ≤ nc) (hu : groesseProg P < unendlich) :
    P ∈ genBadAlle c S fs ls cs ws nb nc (groesseProg P) :=
  List.mem_filter.2 ⟨progS_vollst nb nc P hb hc hi hu, decide_eq_true hv⟩

end Gabbro.Grammatik.Gen
