/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Beine.lean
  Subject:   THE SAFETY LEGS THE ACCESS CLASSES CARRY ARE NOT TRIVIAL (MK-04). The memory legs of one implementation
             step (`Klasse/Sicherheit`: `KlassenSpeicherbeinAussage`) and the race leg
             (`RennfreiAusLokalAussage`) are statements about runs of the machine. For each leg the model represents a
             run that violates it, so that the leg can fail and the class guard, the booking and the lock discipline
             have something to exclude:
             * the memory leg (`Speichersicher`): a plain write through a handle of an earlier generation of an object;
             * the race leg (`Rennfrei`): two threads write the same plain location and nothing orders them;
             * the invariant leg (`InvariantenErhalten`): a loaded writer releases a lock whose invariant is false;
             * the commit leg (`ToctouFrei`): an unmediated outside commit after its endpoint's object died.
             The statements are the existing proved non-emptiness theorems of `Core/Sicherheit`, stated under the leg's
             name so that the legs the access classes carry have their `_nichtTrivial` lemma next to them. The
             question leg and the device leg belong to the class `frage` (MK-06): an access instruction asks no
             question and touches no device register, so for the classes of this package they hold by
             `KlassenFragenbeinAussage` and `KlassenRegisterbeinAussage` with an empty outside record.
-/
module

public import Core.Sicherheit.Erfuellbar
public import Core.Sicherheit.InvariantenNichtLeer
public import Core.Sicherheit.AussenNichtLeer

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core Maschine Katalog Sicherheit

/-- **The memory leg is not trivial**: a run of the machine writes through a stale handle, and `Speichersicher` fails. -/
theorem speicherbein_nichtTrivial :
    ∃ (E : Laufkonstruktion.Modell) (H : Umgebung) (ρ : Lauf E),
      Maschine.Laeufe E.maschine H ρ ∧ ¬ Speichersicher E H ρ :=
  speichersicher_nichtLeer

/-- **The race leg is not trivial**: a run of the machine has two unordered conflicting plain writes. -/
theorem rennenbein_nichtTrivial :
    ∃ (E : Laufkonstruktion.Modell) (H : Umgebung) (ρ : Lauf E),
      Maschine.Laeufe E.maschine H ρ ∧ ¬ Rennfrei E H ρ :=
  rennfrei_nichtLeer

/-- **The invariant leg is not trivial**: a run of the machine releases a lock with its declared invariant false. -/
theorem invariantenbein_nichtTrivial :
    ∃ (E : Laufkonstruktion.Modell) (H : Umgebung) (ρ : Lauf E),
      Maschine.Laeufe E.maschine H ρ ∧ ¬ InvariantenErhalten E H ρ :=
  invarianten_nichtLeer

/-- **The commit leg is not trivial**: a run of the machine commits an outside operation after its endpoint died. -/
theorem commitbein_nichtTrivial :
    ∃ (E : Laufkonstruktion.Modell) (H : Umgebung) (ρ : Lauf E),
      Maschine.Laeufe E.maschine H ρ ∧ ¬ ToctouFrei E H ρ :=
  toctoufrei_nichtLeer

end Gabbro.Core.Ast.Semantik
