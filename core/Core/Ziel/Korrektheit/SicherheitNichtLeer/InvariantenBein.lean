/-
  File:      core/Core/Ziel/Korrektheit/SicherheitNichtLeer/InvariantenBein.lean
  Subject:   THE INVARIANT LEG OF M7S AT A NON-EMPTY DECLARED SOURCE INVARIANT. From a unit with
             the invariants it declares (`UnitMitInvarianten`, `programmMitInvarianten`), the
             checker's acceptance verdict and an admitted implementation run, the exact
             `InvariantenErhalten` clause holds at the run's actual cuts: the declared part at
             every cut and the hand-off obligation at every non-crash transition. The proof
             reuses the generic safety of `invariantenSicherheit` and projects the invariant
             conjunct; nothing is weakened and no statement is changed. Declared invariants
             carry lock scope `none`; no lock-scoped source syntax is claimed anywhere. The
             closing example constructs a non-tautological predicate, exhibits an admitted run
             with a real cut, and reads the predicate off that cut through the clause.
-/
module

public import Core.Ziel.Korrektheit.PrueferKlauseln
public import Core.Ast.Semantik.Runtime.Klasse.ZugriffSicher.RennenLauf
public import Core.Maschine.Start
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.SicherheitNichtLeer

open Gabbro.Core
open Maschine Katalog
open Gabbro.Core.Sicherheit
open Gabbro.Core.Ast.Semantik

/-- The constructed predicate of the closing example: the region cell starts at `0`. -/
def konstruiertesPraedikat : Praedikat :=
  Praedikat.vgl .eq (.zelle (.region 0 0)) (.konst 0)

/-- The unit declaring exactly that one non-empty invariant. -/
def konstruierteEinheit : UnitMitInvarianten :=
  ⟨⟨[], .done⟩, [konstruiertesPraedikat]⟩

/-- The declared list is non-empty, so the leg is not about an empty clause table. -/
theorem konstruierteEinheit_nichtLeer : konstruierteEinheit.invarianten ≠ [] := by
  simp [konstruierteEinheit]

/-- The decidable checker accepts the constructed unit. -/
theorem konstruierteEinheit_akzeptiert (P : Katalog.Plattform) :
    pruefeEinheit (programmMitInvarianten konstruierteEinheit) konstruierteEinheit.invarianten = true := by
  rfl

/-- The constructed predicate is not a tautology: a state whose memory plan holds `1` refutes it. -/
theorem konstruiertesPraedikat_nichtTrivial :
    ∃ s : Zustand, ¬ konstruiertesPraedikat.gilt s := by
  refine ⟨{ Leerzustand with initial := fun _ => 1 }, ?_⟩
  simp only [Praedikat.gilt, konstruiertesPraedikat, Praedikat.haelt, Vergleich.haelt, Ausdruck.wert]
  omega

/-- THE INVARIANT LEG (M7S) for a non-empty declared source invariant. The acceptance verdict and
    the admitted implementation run are hypotheses; the conclusion is the exact clause, with the
    quantification over actual cuts and the hand-off obligation untouched. -/
theorem invariantenBein_nichtLeer (P : Katalog.Plattform) (u : UnitMitInvarianten)
    (hnichtleer : u.invarianten ≠ [])
    (ok : pruefeEinheit (programmMitInvarianten u) u.invarianten = true)
    (zugriff : ZugriffSicherAussage)
    (H : Katalog.Umgebung)
    (ρ : Sicherheit.Lauf ((programmMitInvarianten u).sicherheitsEinheit P))
    (lauf : Maschine.Laeufe (elaborierenMitInvarianten P u) H ρ) :
    InvariantenErhalten ((programmMitInvarianten u).sicherheitsEinheit P) H ρ := by
  exact (invariantenSicherheit P zugriff u ok H ρ lauf).2.1

/-- THE LEG IS CLOSED NON-VACUOUSLY: an admitted run of the constructed unit has a real cut at
    time zero, and the exact clause yields the constructed predicate at that cut. -/
theorem invariantenBein_nichtVakuum :
    ∃ (H : Katalog.Umgebung)
      (ρ : Sicherheit.Lauf ((programmMitInvarianten konstruierteEinheit).sicherheitsEinheit .x86_64)),
      Maschine.Laeufe (elaborierenMitInvarianten .x86_64 konstruierteEinheit) H ρ ∧
      ∃ (s : Zustand)
        (t : Maschine.Schnitt (elaborierenMitInvarianten .x86_64 konstruierteEinheit) ρ),
        ρ.zeit.zustand t.val = some s ∧ konstruiertesPraedikat.gilt s := by
  let P : Katalog.Plattform := .x86_64
  let u := konstruierteEinheit
  let E := elaborierenMitInvarianten P u
  let H := Umgebung.referenz P.katalog 2 (fun _ _ => .leer)
  let hw := Umgebung.referenzLauf P.katalog 2 (fun _ _ => .leer)
  have hwOk : Hardware P.katalog H :=
    Umgebung.referenz_hardware P.katalog 2 (fun _ _ => .leer)
      (Plattform.katalog_wohlgeformt P) (by decide)
  have fair : FairLaeufe P.katalog H hw :=
    Umgebung.referenz_fair P.katalog 2 (fun _ _ => .leer)
      (Plattform.katalog_wohlgeformt P) (by decide)
  obtain ⟨start, zul⟩ := zulStart_erfuellbar hwOk (elaboriert_bild_gueltig P u)
  obtain ⟨ρ, run, _, _⟩ := Maschine.fairer_lauf (E := E) zul fair
  have safe := invariantenBein_nichtLeer P u konstruierteEinheit_nichtLeer
    (konstruierteEinheit_akzeptiert P) zugriffSicherBeweis H ρ run
  have loaded : ∃ z, E.laden ρ.start (H.lade E.bild) = some z := by
    dsimp [E, H, elaborierenMitInvarianten, Fragment.einheit, Umgebung.referenz]
    rw [Ast.Semantik.laden, if_pos ⟨rfl, rfl⟩]
    exact ⟨_, rfl⟩
  obtain ⟨z, hz⟩ := loaded
  have at0 : ρ.zeit.zustand 0 = some z := run.2.2.2.trans hz
  let cut : Maschine.Schnitt E ρ := ⟨0, Or.inl rfl⟩
  have am := safe.1 cut z at0
  have hidx : (((programmMitInvarianten u).sicherheitsEinheit P).invarianten)[0]? =
      some (⟨none, konstruiertesPraedikat.gilt⟩ : Invariante Nat Zustand) := by
    simp [konstruierteEinheit, konstruiertesPraedikat]
  have writers : ∀ c, z.status c = .laeuft → ¬ z.buchung.schreibt c 0 := by
    intro c _ h
    exact h
  have gilt : konstruiertesPraedikat.gilt z := am.2 0 _ hidx writers
  refine ⟨H, ρ, run, ?_⟩
  exact ⟨z, cut, at0, gilt⟩

end Gabbro.Core.Ziel.Korrektheit.SicherheitNichtLeer
