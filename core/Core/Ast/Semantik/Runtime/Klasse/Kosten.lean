/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Kosten.lean
  Subject:   THE STATIC COST ROW OF AN EFFECT CLASS (MK-12). Every step of a class costs one
              abstract tick (the MK-12 cost marks count occupied ticks: `kostenSchrittAussage`),
              and only a lock action changes lock ownership (`FuehrtAus.sperre` is the one
              protocol action that rewrites `sperren`; the form interior keeps them through
              `Zustandsrahmen`). `KlassenKostenzeile` is the static row of a class: the cost of
              one step in abstract ticks, and the hold contribution of a step that holds a lock
              word (`none` for a class that never changes lock ownership). `kostenZeile` is the
              row of a class: cost one on every platform (no per-class hardware duration row is
              reviewed yet — `Plattform.dauerZeilen` is empty on all three targets — so the rows
              agree; the per-platform table is the refinement point, B19, and changes no source),
              hold only for the lock class. `KlassenKostenAussage` states both legs for a declared
              row over every embedded form: a step costs at most the declared class cost, and a
              step of a class that touches no lock word preserves every lock owner and declares no
              hold contribution. Two generic machine facts factor the hold leg:
              `FuehrtAus.sperren_erhalt` and `FuehrtSchrittAus.sperren_erhalt`. Proved per class as
              `klassenKosten` in `Klasse/Beweise/Kosten`, one arm per class, and assembled into
              `KlassenAussagen`.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Ast.Semantik.Runtime.Klasse.Einbettung
public import Core.Ast.Semantik.Runtime.Klasse.Sicherheit
public import Core.Maschine.Schritte

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett)

/-- The static cost row of an effect class (MK-12): the cost of one step of the class in
    abstract ticks, and the hold contribution of a step that holds a lock word (`none` for a
    class that never changes lock ownership). -/
structure KlassenKostenzeile where
  kosten : Nat
  halten : Option Nat

/-- The static cost row of a class: one abstract tick per step, hold only for the lock class.
    No per-class hardware duration row is reviewed yet, so every platform carries the same
    rows; the per-platform table refines them without changing sources. -/
def Wirkungsklasse.kostenZeile : Wirkungsklasse → KlassenKostenzeile
  | .sperre .. => ⟨1, some 1⟩
  | .lokal | .ruf | .lesen .. | .schreiben .. | .rmw .. | .zaun .. | .frage | .starte | .beende
  | .verbinde | .wechsle | .maskiere | .prioritaet | .sendeUnterbrechung | .leiteLeitung =>
    ⟨1, none⟩

/-- Every class row declares cost one: a step is one occupied tick. -/
theorem Wirkungsklasse.kostenZeile_kosten (k : Wirkungsklasse) :
    (k.kostenZeile).kosten = 1 := by
  cases k <;> rfl

/-- A class that touches no lock word declares no hold contribution. -/
theorem Wirkungsklasse.kostenZeile_halten_ohneSperrwort (k : Wirkungsklasse)
    (hne : k.beruehrtSperrwort = false) : (k.kostenZeile).halten = none := by
  cases k with
  | sperre a =>
      change true = false at hne
      cases hne
  | lokal | ruf | lesen _ | schreiben _ | rmw _ | zaun _ | frage | starte | beende | verbinde
  | wechsle | maskiere | prioritaet | sendeUnterbrechung | leiteLeitung => rfl

/-- The lock class declares hold one: a holding step costs its context one tick. -/
theorem Wirkungsklasse.kostenZeile_halten_sperre (a : SperrAktion) :
    ((Wirkungsklasse.sperre a).kostenZeile).halten = some 1 :=
  rfl

/-- **Cost and hold, once per class, for a declared row** (`KlassenKostenAussage`). A step of
    an embedded form costs at most the declared class cost (one plan, one occupied tick), and
    a step of a class that touches no lock word preserves every lock owner and declares no
    hold contribution: holding lasts only while the class holds a lock word. Open (MK-12).
    Difficulty: mittel. Sketch: the cost leg reads the single plan off the class rule (one arm
    per class in `klassenKosten`); the hold leg combines the plan shape of the class (never a
    lock action) with `FuehrtSchrittAus.sperren_erhalt` below. -/
def KlassenKostenAussage (z : Wirkungsklasse → KlassenKostenzeile) (k : Wirkungsklasse) : Prop :=
  (∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform),
    F.klasse = k → F.Eingebettet E f →
    ∀ (c : Kontext) (s : Zustand) (w : PUnit) (plans : List Plan) (u : Zustand),
      F.ideal c s w plans u → plans.length ≤ (z k).kosten)
  ∧ (k.beruehrtSperrwort = false →
    (z k).halten = none ∧
    ∀ (ι : Type) (E : Klasseneinheit ι) (f : ι) (F : Schrittform),
      F.klasse = k → F.Eingebettet E f →
      ∀ (t : Nat) (c : Kontext) (s u : Zustand) (w : PUnit) (plan : Plan)
        (spur : SchrittSpur Zelle Int) (nach : Zustand),
        F.ideal c s w [plan] u →
        FuehrtSchrittAus E.einrichtung t c s u plan spur nach →
        ∀ l : Nat, (nach.sperren l).besitzer = (s.sperren l).besitzer)

/-- A protocol action other than a lock action keeps the lock table: only `sperre` rewrites
    `sperren`, every other action keeps it by `rfl` on its record update. -/
theorem FuehrtAus.sperren_erhalt {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung} {t : Nat} {c : Kontext}
    {s u : Maschine.Zustand L Ort Wert Raum Lok Grund} {a : Aktion L Bedingung}
    {sperren : List (Etikett Ort Wert)} {spur : List Ereignis}
    {v : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h : FuehrtAus e t c s u a sperren spur v) (hne : ∀ (l : L) (b : SperrAktion), a ≠ .sperre l b) :
    v.sperren = u.sperren := by
  cases h with
  | intern => rfl
  | warte _ => rfl
  | sperre _ _ => exact False.elim (hne _ _ rfl)
  | frage _ => rfl
  | verbrauche _ => rfl
  | rueckkehr _ _ => rfl
  | starte _ => rfl
  | verbinde _ _ => rfl
  | beende _ => rfl
  | wechsle _ _ _ _ => rfl

/-- A full step whose plan is no lock action keeps every lock owner: the protocol action keeps
    the lock table (`FuehrtAus.sperren_erhalt`), the form interior keeps it
    (`Zustandsrahmen`), and the graph replacement touches only the graph. -/
theorem FuehrtSchrittAus.sperren_erhalt {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung} {t : Nat} {c : Kontext}
    {s u : Maschine.Zustand L Ort Wert Raum Lok Grund} {plan : SchrittPlan L Ort Wert Bedingung}
    {spur : SchrittSpur Ort Wert} {nach : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h : FuehrtSchrittAus e t c s u plan spur nach)
    (hne : ∀ (l : L) (b : SperrAktion), plan.aktion ≠ .sperre l b) (l : L) :
    (nach.sperren l).besitzer = (s.sperren l).besitzer := by
  obtain ⟨rahmen, _, _, v, fuehrt, _, heq⟩ := h
  have hv : v.sperren = u.sperren := FuehrtAus.sperren_erhalt fuehrt hne
  rw [heq]
  show (v.sperren l).besitzer = (s.sperren l).besitzer
  rw [hv, rahmen.sperren]

end Gabbro.Core.Ast.Semantik
