/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Quelle.lean
  Subject:   Random sources as catalogue rows with draw laws (M9P foundations, B11(a)(b)).

  A random source is a catalogue row (`.zufall id`, see `Core.Katalog.Auswahl`) with a
  declared draw law, a Mathlib `PMF` over its outcomes. Random rows are platform
  rows (`Plattform.zufallZeilen`): a program selects them by name like every other
  catalogue row and never writes one. Safety already holds for every
  random outcome - a random number is one more oracle answer, and the goal quantifies
  over all answers. This file adds the QUANTITATIVE side: the law, the finite-event
  probability, and the proved non-degeneracy witness (a fair coin with an event
  strictly inside `(0, 1)`).

  Form-independence: no Ast inductive is touched. A random draw reaches the machine as
  an ordinary catalogue answer: the question is an `.exchange` on the binding's
  endpoint with the binding's tag, and the reply carries the drawn outcome as a
  register value. The future `random` source form (`planned.probability.draw`)
  elaborates to exactly such a question; its registry entry then pins this file's
  `Zufallsfrage` shape. Until then, `Zufallsbindung` is the model-side anchor.
-/
module

public import Core.Katalog.Auswahl
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog

/-- A random source: a platform catalogue row id with a declared draw law over `anz`
    outcomes (`anz` is positive, so the coin with `anz = 2` needs no side condition
    beyond `decide`). Draws are independent by the cylinder weights of `Hebung`,
    never by an extra premise here. -/
structure Zufallsquelle where
  id : Nat
  anz : Nat
  pos : 0 < anz
  gesetz : PMF (Fin anz)

/-- The fair coin: two outcomes, each drawn with probability `2⁻¹`. -/
theorem muenzSumme :
    Finset.sum Finset.univ (fun _ : Fin 2 => (2⁻¹ : ENNReal)) = 1 := by
  simp only [Fin.sum_univ_two]
  exact ENNReal.inv_two_add_inv_two

noncomputable def muenzQuelle : Zufallsquelle :=
  ⟨0, 2, by decide, PMF.ofFintype (fun _ => (2⁻¹ : ENNReal)) muenzSumme⟩

/-- Draw laws of the platform rows: row 0 is the fair coin on every platform. This
    is the platform profile's law assignment for `Plattform.zufallZeilen`; a program
    selects the row, the law is fixed here. -/
noncomputable def zufallGesetz : Plattform → Nat → Option Zufallsquelle
  | .x86_64, 0 => some muenzQuelle
  | .aarch64, 0 => some muenzQuelle
  | .riscv64, 0 => some muenzQuelle
  | _, _ => none

/-- The platform profile declares the coin law for row 0 on every platform. -/
theorem zufallGesetz_nationaleMuenze (p : Plattform) :
    zufallGesetz p 0 = some muenzQuelle := by
  cases p <;> rfl

/-- Completeness of the platform profile: every `.zufall` row of a platform is
    backed by exactly one declared source, and it carries the row's id. -/
theorem plattformZufallGesetz (p : Plattform) (id : Nat)
    (h : Zeile.zufall id ∈ p.zufallZeilen) :
    ∃! Q : Zufallsquelle, zufallGesetz p id = some Q ∧ Q.id = id := by
  rw [Plattform.zufallZeilen_inhalt] at h
  simp only [List.mem_singleton, Zeile.zufall.injEq] at h
  subst h
  refine ⟨muenzQuelle, ⟨zufallGesetz_nationaleMuenze _, rfl⟩, fun Q hQ => ?_⟩
  have htab := zufallGesetz_nationaleMuenze p
  have heq : muenzQuelle = Q := Option.some.inj (htab.symm.trans hQ.1)
  exact heq.symm

/-- Heads: the first outcome of the coin. Typed over the source so no unfolding
    is ever needed at use sites. -/
def muenzKopf : Fin muenzQuelle.anz := ⟨0, by decide⟩

/-- The coin event "the draw is heads". Noncomputable like the coin itself: its
    type mentions the noncomputable source. -/
noncomputable def muenzEreignis : Fin muenzQuelle.anz → Prop := (· = muenzKopf)

/-- Decidability of the coin event, given explicitly (from `Fin` equality). -/
noncomputable instance muenzEreignisDez : DecidablePred muenzEreignis :=
  fun x => decEq x muenzKopf

/-- A random binding: which source backs which catalogue question. The question is an
    `.exchange` on `endpunkt` with the tag `kennung`; the future `random` source form
    elaborates to exactly this shape. -/
structure Zufallsbindung where
  quelle : Zufallsquelle
  endpunkt : Endpunkt
  kennung : List UInt8

/-- Boolean test for a random-draw question. Boolean (not `DecidableEq` on the
    operation): the match is structural, so no instances are needed. -/
def istZufallsfrage (B : Zufallsbindung) (q : Frage) : Bool :=
  match q.operation with
  | .exchange m => q.endpoint == B.endpunkt && m == B.kennung
  | _ => false

/-- A question draws randomness for `B` exactly when the boolean test holds. -/
def Zufallsfrage (B : Zufallsbindung) (q : Frage) : Prop :=
  istZufallsfrage B q = true

/-- The binding's source row is selected in the catalogue. -/
def ZufallszeileZugelassen (k : Katalog) (B : Zufallsbindung) : Prop :=
  k.enthaelt (.zufall B.quelle.id)

/-- The answer carrying the drawn outcome `o`: the origin is witnessed by the caller
    (from their snapshot), no generation is invented here. -/
def ZiehungsAntwort (h : Herkunft) (o : Nat) : Antwort :=
  ⟨h, [], .ok (.register o)⟩

/-- The probability of a decidable outcome event: the finite sum of the law over the
    event. Finite by construction (`Fin`), so no measure theory is needed for the
    non-degeneracy witness; the lift to run measures is `Hebung`. -/
noncomputable def Wahrscheinlichkeit (Q : Zufallsquelle) (E : Fin Q.anz → Prop)
    [DecidablePred E] : ENNReal :=
  Finset.sum Finset.univ fun a => if E a then Q.gesetz a else 0

/-- A singleton event has exactly the law's probability at that outcome. -/
theorem wahrscheinlichkeitEinzel (Q : Zufallsquelle) (a : Fin Q.anz) :
    Wahrscheinlichkeit Q (· = a) = Q.gesetz a := by
  simp only [Wahrscheinlichkeit, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The coin event has probability `2⁻¹`. -/
theorem muenzWahrscheinlichkeit :
    Wahrscheinlichkeit muenzQuelle muenzEreignis = (2⁻¹ : ENNReal) := by
  have hW := wahrscheinlichkeitEinzel muenzQuelle muenzKopf
  change Wahrscheinlichkeit muenzQuelle (fun x => x = muenzKopf) = _
  rw [hW]
  exact PMF.ofFintype_apply muenzSumme muenzKopf

/-- Non-degeneracy, proved: the coin event is strictly inside `(0, 1)`. This is the
    `_erfuellbar` core of M9P: a real source whose event probability is neither `0`
    nor `1`, so no probabilistic statement over it holds vacuously. -/
theorem muenz_innen :
    0 < Wahrscheinlichkeit muenzQuelle muenzEreignis ∧
      Wahrscheinlichkeit muenzQuelle muenzEreignis < 1 := by
  rw [muenzWahrscheinlichkeit]
  exact ⟨ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top, ENNReal.one_half_lt_one⟩

end Gabbro.Core.Beobachtung
