/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Klasse.lean
  Subject:   THE EFFECT CLASS OF AN INSTRUCTION (MK-03). Every instruction has exactly one class, and the
             class fixes what its step may touch: the shape of its plan (`Klasse/Schritt`), the authority it
             needs, and the machine duties it owes. The duties of an instruction (simulation, locality,
             progress, determinacy, safety, information flow, the footprint on the bounds) are proved ONCE PER
             CLASS (`Klasse/Pflichten`); an instruction pays its class assignment and what its frame transfer
             adds. A new class is a new constructor at the END of `Wirkungsklasse`, and the guard demands its
             registry packet before an instruction can use it (`Befehl.klasse` has no wildcard, so a new
             instruction must be classified).
             * `lokal`, `ruf` change the acting frame only (private step).
             * `lesen`, `schreiben`, `rmw` access one cell of the shared memory in a mode (a load, a store, an
               atomic update): the plan carries the access, the frame names the cell.
             * `sperre` draws a ticket, takes or gives one lock of the unit.
             * `frage` issues one question to the outside world.
             The classes of waiting, thread start and join, authority, time, persistence, randomness and
             guests are appended by the packages that introduce their first instruction.
-/
module

public import Core.Ast.Semantik.Runtime.Befehl

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- **The effect class of an instruction.**
    * `lokal`: one private step whose only effect is the acting frame; it never deepens the call stack.
    * `ruf`: the same, but the step may push one continuation (a call, or the start of the program).
    * `lesen m`: a read of one cell in mode `m`; the value read is chosen by the memory model.
    * `schreiben m`: a write of one cell in mode `m`.
    * `rmw m`: an atomic read-modify-write of one cell in mode `m`.
    * `sperre a`: one lock action `a` (ticket, take, give) on one lock of the unit.
    * `frage`: one question to the outside world; its answer arrives later, as its own transition. -/
inductive Wirkungsklasse where
  | lokal
  | ruf
  | lesen (modus : Gabbro.Core.Speicher.Modus)
  | schreiben (modus : Gabbro.Core.Speicher.Modus)
  | rmw (modus : Gabbro.Core.Speicher.Modus)
  | sperre (aktion : Gabbro.Core.Maschine.SperrAktion)
  | frage

/-- **The class of an access instruction** (MK-04): a load and the confirming observation read, a store and the
    publication write, an update (exchange, compare-and-swap, fetch-and-add) is an update, each in the mode the
    instruction names. -/
def Zugriffsform.klasse : Zugriffsform → Wirkungsklasse
  | .lade _ _ _ _ m => .lesen m
  | .erwarte _ _ _ _ _ m => .lesen m
  | .speichere _ _ _ m => .schreiben m
  | .veroeffentliche _ _ _ m => .schreiben m
  | .tausche _ _ _ _ _ m => .rmw m
  | .vergleicheTausche _ _ _ _ _ _ m => .rmw m
  | .holeUndAddiere _ _ _ _ _ m => .rmw m

/-- Classify every instruction. A new instruction must be classified: there is no wildcard. -/
def Befehl.klasse : Befehl → Wirkungsklasse
  | .zugriff form => form.klasse
  | .rufe .. | .starte .. => .ruf
  | .literal .. | .binaer .. | .wahrheitswert .. | .lesen .. | .negativ ..
  | .negieren .. | .verneinen .. | .teilen .. | .vergleichen ..
  | .binden .. | .springeWenn .. | .zuweisen .. | .zurueck .. | .springe ..
  | .blockEnde .. | .bindeWert .. | .ende | .bindeRegion ..
  | .definiere .. | .rueckVoid | .pruefeMass .. | .setzePasszahl ..
  | .whileTest .. | .forAnfang .. | .forTest .. | .forNaechster .. | .zurueckSprung ..
  | .baueArray .. | .liesArray .. | .baueTupel .. | .liesTupelfeld .. | .bindeTupel ..
  | .definiereRecord .. | .baueRecord .. | .liesRecordFeld .. | .setzeRecordFeld ..
  | .definiereVariante .. | .baueVariante .. | .waehleVariante ..
  | .definiereTraeger .. | .optionIstBesetzt .. | .definiereEffektgruppe .. | .waehleUmgebung ..
  | .textLiteral .. | .textConcat .. | .textIndex .. | .substring .. | .textLength .. => .lokal

/-- **The stack effect of an instruction**: the frame it steps grows its continuation stack by at
    most `k`. -/
def Befehl.Stapelwirkung (b : Befehl) (k : Nat) : Prop :=
  ∀ (frame : Rahmen) (live : Nat → Bool),
    (b.auswerten frame live).fortsetzungen.length ≤ frame.fortsetzungen.length + k

/-- **The stack effect of a class**: only a `ruf` instruction deepens the stack, by at most one frame;
    every other class steps its frame without pushing a continuation. -/
def Wirkungsklasse.Stapel : Wirkungsklasse → Nat
  | .ruf => 1
  | .lokal | .lesen .. | .schreiben .. | .rmw .. | .sperre .. | .frage => 0

/-- Frame-level fact each instruction pays for its class: its stack effect is the one of its class.
    Difficulty: leicht-mittel. Sketch: case split on the instruction; every case but `rufe` and `starte` is
    `Rahmen.schreibe`, a `{ frame with … }` update that keeps `fortsetzungen`, `Rahmen.halt`, or
    `Rahmen.rueckkehr` (which pops); `rufe` and `starte` end in `Rahmen.ruf`, which pushes one
    continuation or halts; the `Id.run do` bodies (`forAnfang`, `forTest`, `forNaechster`, `starte`,
    `bindeRegion`, `textIndex`, `substring`, `waehleVariante`) split on their guards and end in one of
    these updates. -/
def KlassenStapelAussage : Prop :=
  ∀ b : Befehl, b.Stapelwirkung b.klasse.Stapel

end Gabbro.Core.Ast.Semantik
