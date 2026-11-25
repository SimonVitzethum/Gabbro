/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Sicherheit.lean
  Subject:   THE SAFETY LEGS OF AN EFFECT CLASS (MK-03, PERFECT-MODEL §3.6). The safety of one implementation
             step (`Sicherheit.SchrittSicherheit`) has six legs. FOUR are determined by the class alone and are
             stated here once per class, each as its own pinned unit so that the provers can take them
             independently:
             * `KlassenSpeicherbeinAussage`: every access the step records is booked in the ledger with a
               handle and a right, and the step releases nothing it should not;
             * `KlassenFragenbeinAussage`: the authority of every pending question survives the step;
             * `KlassenRegisterbeinAussage`: a device access has the exclusive authority of the device;
             * `KlassenCommitbeinAussage`: a committed outside operation holds its handles and validates.
             The other two legs are NOT class duties, and no statement of them is pinned here, because a pinned
             statement that no design can make true is worse than none:
             * the INVARIANT legs (`InvariantenAmSchnitt`, `InvariantenBeimWechsel`): `Sicherheit.Invariante.gilt`
               is an opaque predicate over the whole state and has no footprint, so a write form cannot say which
               invariant it endangers and the ledger cannot name the writer scope (`buchung.schreibt c i`);
               the invariant leg needs the footprint of a declared invariant (MK-04, MK-05);
             * the RACE leg (`RennenImGraph`): it holds for the atomic modes, and for the non-atomic modes only
               under the lock sections that order the conflicting accesses (`RennfreiAusLokalAussage`, MK-04).
             The class `sperre` is excluded from the booking leg: the machine records a change of the lock owner
             as a memory event on the lock word, `ZugriffGebucht` asks for a handle for it, and `Zustand.griff` has
             none for a lock word (`kein_zugriff_sperre`). The lock word needs its own authority (an exemption of
             the lock word in `ZugriffGebucht`, or a handle for it): a finding for MK-05.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Einbettung
public import Core.Sicherheit.Regel

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- Does a step of the class change the owner of a lock, so that the machine records an event on the lock
    word? Only the lock actions do. -/
def Wirkungsklasse.beruehrtSperrwort : Wirkungsklasse → Bool
  | .sperre .. => true
  | .lokal | .ruf | .lesen .. | .schreiben .. | .rmw .. | .frage | .starte | .beende | .verbinde
  | .wechsle => false

/-- **Booking and releases, once per class.** In a safety unit that embeds a form of the class, every memory
    access the step records is booked with a handle and the right it needs (the class books the address,
    `Schrittform.buchungNach`), and the step's releases are valid. Open (MK-04). Difficulty: schwer for the
    memory classes, leicht for the others. Sketch: `Speicherfolge` appends at most one lazily materialised
    initial write before the access (`Initialisierung`, case split on `HatQuelle`), so the access sits at
    index `Zustand.zugriffsereignis`; `Speicherzugriff` is `Zustand.befugt` of the guard; the step releases
    nothing, so `neu = []`, `NeueWirkungen` is the unchanged ledger and `FreigabenGueltig` is empty. For a
    class without a memory event the record has no access and the leg is `rfl`-shaped. -/
def KlassenSpeicherbeinAussage (k : Wirkungsklasse) : Prop :=
  k.beruehrtSperrwort = false →
    ∀ (ι : Type) (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι) (f : ι)
      (F : Schrittform), F.klasse = k → F.Eingebettet E.maschine f →
      ∀ (hw : HwLauf) (t : Nat) (c : Kontext) (w : PUnit) (vor zwischen nach : Zustand) (plan : Plan)
        (spur : SchrittSpur Zelle Int),
        E.maschine.system.kopf vor c = some f →
        (E.maschine.system.regel f).impl c vor w [plan] zwischen →
        FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach →
        Sicherheit.ZugriffGebucht vor nach spur ∧
          ∃ neu, Sicherheit.NeueWirkungen vor nach spur neu ∧
            Sicherheit.FreigabenGueltig vor nach hw t spur neu

/-- **The authority of pending questions, once per class.** A step of the class keeps every pending question
    authorised (`OffeneFragenBefugt`), including the question it issues: its guard (`fragenBefugt`) holds
    the handles and, for a register access, the device. Open. Difficulty: mittel for `frage`, leicht for the
    other classes (they change neither the questions nor the answers nor the ledger of handles). Sketch:
    `FuehrtAus.frage` appends `stelleFrage t c q`; its context is `c.nummer` and its question is `q`, which
    the guard authorises at the pre-state, and `buchung` is the same in the post-state. -/
def KlassenFragenbeinAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι) (f : ι)
    (F : Schrittform), F.klasse = k → F.Eingebettet E.maschine f → Sicherheit.RegelAntwortSicher E f

/-- **Device authority, once per class.** A step of the class that records a register access had the exclusive
    authority of the device at the pre-state, and the effects it adds to the ledger are its own. Open.
    Difficulty: leicht. Sketch: only `frage` records an outside event, and its guard contains
    `RegisterErlaubt`; every other class has an empty outside record and adds no effect. -/
def KlassenRegisterbeinAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι) (f : ι)
    (F : Schrittform), F.klasse = k → F.Eingebettet E.maschine f →
    ∀ (hw : HwLauf) (t : Nat) (c : Kontext) (w : PUnit) (vor zwischen nach : Zustand) (plan : Plan)
      (spur : SchrittSpur Zelle Int),
      E.maschine.system.kopf vor c = some f →
      (E.maschine.system.regel f).impl c vor w [plan] zwischen →
      FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach →
      Sicherheit.RegisterImSchritt hw t vor spur nach

/-- **Committed outside operations, once per class.** A step of the class commits no outside operation: the
    question it issues is a question, not a commit, so the commit leg holds without a premise. Open.
    Difficulty: leicht. Sketch: `ErfolgreicherCommit e a` needs an answer event in the step's outside record;
    the record of a class step is empty or holds one question event. -/
def KlassenCommitbeinAussage (k : Wirkungsklasse) : Prop :=
  ∀ (ι : Type) (E : Sicherheit.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι) (f : ι)
    (F : Schrittform), F.klasse = k → F.Eingebettet E.maschine f →
    ∀ (H : Katalog.Umgebung) (ρ : Sicherheit.Lauf E) (t : Nat) (c : Kontext) (w : PUnit)
      (vor zwischen nach : Zustand) (plan : Plan) (spur : SchrittSpur Zelle Int),
      E.maschine.system.kopf vor c = some f →
      (E.maschine.system.regel f).impl c vor w [plan] zwischen →
      FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach →
      Sicherheit.CommitImSchritt E H ρ t vor spur nach

/-- **The class-determined safety legs of one class, together.** -/
def KlassenSicherheitAussage (k : Wirkungsklasse) : Prop :=
  KlassenSpeicherbeinAussage k ∧ KlassenFragenbeinAussage k ∧ KlassenRegisterbeinAussage k ∧
    KlassenCommitbeinAussage k

end Gabbro.Core.Ast.Semantik
