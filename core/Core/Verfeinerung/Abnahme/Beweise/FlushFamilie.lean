/-
  File:      core/Core/Verfeinerung/Abnahme/Beweise/FlushFamilie.lean
  Subject:   CONSEQUENCES OF THE FLUSH FAMILY DUTY. The duty, its satisfiability, its refutability and
             the transport to concrete runs are proved in `Abnahme/Flush.lean`. This file closes the
             connection from the duty to the memory guarantee: under the declared cache laws a release
             of the run's decoded protocol leaves no cell of the revoked range on any existing core,
             both on the ideal run and on every concrete run matched to it. It also records that the
             duty is not a universal guarantee of the unit type and names the missing premise.
-/
module

public import Core.Verfeinerung.Abnahme.Flush

@[expose] public section

namespace Gabbro.Core.Maschine.I

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]

/-- The family duty is not a property of the unit wrapper alone. The missing premise is the binding
    faithfulness of `U`: the decoder `U.bindung.sicht.lesen` must actually emit the send, per-core
    handler, acknowledgement and release of `FlushProtokoll` on every admitted ideal run (in
    particular a send naming every core that exists), and every member of `U.bindung.mitglied` must
    really simulate its rule. A declaration that reads a crash as a release breaks that premise;
    `FlushFamilienAussage_nichtTrivial` is exactly such a declaration. The premise is a per-unit
    GabbroProve obligation, not a language rule, so the duty stays a declaration to discharge. -/
theorem FlushFamilienAussage.nichtAllgemein :
    ¬ ∀ U : FlushEinheit Unit Unit Unit Unit Bool Unit Unit Unit Unit, FlushFamilienAussage U := by
  intro alle
  obtain ⟨U, gegen⟩ := FlushFamilienAussage_nichtTrivial
  exact gegen (alle U)

/-- The family duty delivers the release guarantee on an ideal run, once the declared cache laws
    hold: cells sit on existing cores, no revoked cell is refilled after the send, and a handler
    clears its core's cells of the range. The protocol is taken from the duty rather than supplied
    again, so a release read from the declared decoder leaves no cell of the range. -/
theorem FlushFamilienAussage.keineZelleBeiFreigabe
    (U : FlushEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (pflicht : FlushFamilienAussage U)
    {η : Lauf U.einheit} (valid : Laeufe U.einheit η)
    {Zelle : Type} (zellen : Nat → Zelle → Prop) (kernVon : Zelle → Kern) (bereich : Zelle → Prop)
    (nurKerne : ∀ t z, zellen t z → kernVon z < η.umgebung.kernzahl)
    (keineFuellung : ∀ id s ziele t z,
      U.bindung.sicht.lesen (η.zeit.spur s) = some (id, .senden ziele) → s ≤ t → bereich z →
        zellen (t + 1) z → zellen t z)
    (handlerLeert : ∀ id k t z,
      U.bindung.sicht.lesen (η.zeit.spur t) = some (id, .handler k) → bereich z → kernVon z = k →
        ¬ zellen (t + 1) z)
    {key : U.bindung.Id} {a : Nat}
    (release : U.bindung.sicht.lesen (η.zeit.spur a) = some (key, .freigeben))
    (z : Zelle) (bereichZ : bereich z) : ¬ zellen a z :=
  FlushProtokoll.frei_bei_freigabe (pflicht.2 η valid) zellen kernVon bereich nurKerne
    keineFuellung handlerLeert release z bereichZ

/-- The same guarantee on a concrete run. `konkret` moves the decoded protocol from the matched
    ideal run to the concrete one; the crash predicate moves with it, so the release read from the
    concrete decoder is still the release of that protocol and the cache laws apply at the same
    ticks. -/
theorem FlushFamilienAussage.konkretKeineZelle
    (U : FlushEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (pflicht : FlushFamilienAussage U)
    {ρ : Maschine.Lauf U.einheit} {η : Lauf U.einheit}
    (valid : Laeufe U.einheit η) (matched : Laufabgleich ρ η)
    {Zelle : Type} (zellen : Nat → Zelle → Prop) (kernVon : Zelle → Kern) (bereich : Zelle → Prop)
    (nurKerne : ∀ t z, zellen t z → kernVon z < η.umgebung.kernzahl)
    (keineFuellung : ∀ id s ziele t z,
      U.bindung.sicht.lesen (ρ.zeit.spur s) = some (id, .senden ziele) → s ≤ t → bereich z →
        zellen (t + 1) z → zellen t z)
    (handlerLeert : ∀ id k t z,
      U.bindung.sicht.lesen (ρ.zeit.spur t) = some (id, .handler k) → bereich z → kernVon z = k →
        ¬ zellen (t + 1) z)
    {key : U.bindung.Id} {a : Nat}
    (release : U.bindung.sicht.lesen (ρ.zeit.spur a) = some (key, .freigeben))
    (z : Zelle) (bereichZ : bereich z) : ¬ zellen a z := by
  have protokoll := FlushFamilienAussage.konkret U pflicht valid matched
  exact FlushProtokoll.frei_bei_freigabe protokoll zellen kernVon bereich nurKerne
    keineFuellung handlerLeert release z bereichZ

end Gabbro.Core.Maschine.I
