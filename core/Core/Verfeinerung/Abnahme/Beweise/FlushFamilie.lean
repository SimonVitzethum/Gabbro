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
public import Core.Ast.LowLevel.Mem.Execution
import Core.Ast.LowLevel.Mem.Proofs.Flush.Flush

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

private theorem flushLabelGleich {Id : Type} (sicht : FlushSicht Ort Wert Wahl Id)
    {konkret ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (matched : SpurAbgleich konkret ideal) {phase} (seen : sicht.lesen konkret = some phase) :
    konkret = ideal := by
  cases matched with
  | pause => rfl
  | privat c w =>
    rw [sicht.privat, sicht.leer] at seen
    cases seen
  | schritt event => rfl

/-- The observed release belongs to the specified send. Every existing core has a handler and
    acknowledgement between those cuts, with full labels preserved at those same cuts in I.
    The send and release observations must come from the unit's actual staged binding. -/
theorem FlushFamilienAussage.konkretFreigabekette
    (U : FlushEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (pflicht : FlushFamilienAussage U)
    {ρ : Maschine.Lauf U.einheit} {η : Lauf U.einheit}
    (valid : Laeufe U.einheit η) (matched : Laufabgleich ρ η)
    {id : U.bindung.Id} {s r : Nat} {targets : List Kern}
    (send : U.bindung.sicht.lesen (ρ.zeit.spur s) = some (id, .senden targets))
    (release : U.bindung.sicht.lesen (ρ.zeit.spur r) = some (id, .freigeben)) :
    s < r ∧ (∀ t, s ≤ t → t < r → ρ.zeit.spur t ≠ some (.absturz, absturzSpur)) ∧
    ρ.zeit.spur s = η.zeit.spur s ∧ ρ.zeit.spur r = η.zeit.spur r ∧
    ∀ k, k < η.umgebung.kernzahl → ∃ h a, s < h ∧ h < a ∧ a < r ∧
      U.bindung.sicht.lesen (ρ.zeit.spur h) = some (id, .handler k) ∧
      U.bindung.sicht.lesen (ρ.zeit.spur a) = some (id, .bestaetigen k) ∧
      ρ.zeit.spur h = η.zeit.spur h ∧ ρ.zeit.spur a = η.zeit.spur a := by
  have protocol := FlushFamilienAussage.konkret U pflicht valid matched
  obtain ⟨s', targets', before, sent, noCrash, all⟩ := protocol.freigabe id r release
  have sameCut := protocol.eineSendung id targets targets' s s' send sent
  subst s'
  refine ⟨before, noCrash, flushLabelGleich _ (matched.spur s) send,
    flushLabelGleich _ (matched.spur r) release, ?_⟩
  intro k existsCore
  obtain ⟨h, a, sh, ha, ar, handler, ack⟩ :=
    all k (protocol.abdeckung id targets' s sent k existsCore)
  exact ⟨h, a, sh, ha, ar, handler, ack, flushLabelGleich _ (matched.spur h) handler,
    flushLabelGleich _ (matched.spur a) ack⟩

open Gabbro.Core.Ast.LowLevel Gabbro.Core.Katalog (Zuruecknahme)

/-- The existing flush effect projection reads the checked Mem completion label. -/
def memFlushSicht : FlushSicht Nat UInt8 PUnit (Nat × Zuruecknahme) where
  lesen
    | some (.kontext _ _, ⟨_, [.ruecknahmeAbgeschlossen epoch token]⟩) =>
      some ((epoch, token), .freigeben)
    | _ => none
  leer := rfl
  privat _ _ := rfl

/-- Mem steps, including completion, leave the software interrupt queue intact. -/
theorem memKontextSoftwareUnveraendert {k : Katalog.Katalog} {code : List MemInstruction}
    {hw : Katalog.HwLauf} {t : Nat} {s next : MemState} {c : Kontext} {w : PUnit}
    {trace : SchrittSpur Nat UInt8}
    (step : ImplSchritt (memProgram k code).einrichtung (memProgram k code).system k hw t
      s (.kontext c w, trace) next) : next.software = s.software := by
  obtain ⟨_, _, _, _, _, rfl⟩ := memKontextSchrittGenau step
  rfl

private theorem memZustandGleich {k : Katalog.Katalog} {code : List MemInstruction}
    {s i : MemState} (related : Zustandsbezug (memProgram k code) s i) : s = i := by
  obtain ⟨shared, locals⟩ := related
  change s.lokal = i.lokal at locals
  change { s with lokal := i.lokal } = i at shared
  rw [← locals] at shared
  cases s
  exact shared

private theorem memKontextAmSchnitt {k : Katalog.Katalog} {code : List MemInstruction}
    {ρ : Maschine.Lauf (memProgram k code)} {η : Lauf (memProgram k code)}
    (matched : Laufabgleich ρ η) {t : Nat} {c : Kontext} {w : PUnit}
    {trace : SchrittSpur Nat UInt8} {op : MemInstruction}
    (cut : ρ.zeit.spur t = some (.kontext c w, trace))
    (head : (memProgram k code).system.kopf (η.zeit.zustand t) c = some op) :
    let s := η.zeit.zustand t
    let next := η.zeit.zustand (t + 1)
    ρ.zeit.zustand t = some s ∧ ρ.zeit.zustand (t + 1) = some next ∧
    ∃ frame, op.evaluate k.plattform.ziel s c = some frame ∧
      trace = op.schrittSpur s c ∧ next = frame.advance c s := by
  obtain ⟨s, atBefore, relatedBefore⟩ := matched.zustand t
  obtain ⟨next, atAfter, relatedAfter⟩ := matched.zustand (t + 1)
  have before := atBefore.trans (congrArg some (memZustandGleich relatedBefore))
  have after := atAfter.trans (congrArg some (memZustandGleich relatedAfter))
  refine ⟨before, after, ?_⟩
  have tick := ρ.zeit.takt t
  rw [before, after, cut] at tick
  cases tick with
  | wartet absent _ _ => cases absent
  | schritt recorded runStep =>
    cases recorded
    cases runStep with
    | schritt step =>
      obtain ⟨actual, frame, chosen, eval, label, advance⟩ := memKontextSchrittGenau step
      cases Option.some.inj (chosen.symm.trans head)
      exact ⟨frame, eval, label, advance⟩

/-- The common completion label records the bound token and the epoch of the common pre-state.
    The successor contains the corresponding result and consumes all bindings of that token. -/
theorem memFlushKennungImLauf {k : Katalog.Katalog} {code : List MemInstruction}
    {ρ : Maschine.Lauf (memProgram k code)} {η : Lauf (memProgram k code)}
    (matched : Laufabgleich ρ η) {t : Nat} {c : Kontext} {w : PUnit}
    {trace : SchrittSpur Nat UInt8} {name : Ast.Identifier}
    (cut : ρ.zeit.spur t = some (.kontext c w, trace))
    (head : (memProgram k code).system.kopf (η.zeit.zustand t) c = some (.flushSpace name)) :
    let s := η.zeit.zustand t
    let next := η.zeit.zustand (t + 1)
    ρ.zeit.zustand t = some s ∧ ρ.zeit.zustand (t + 1) = some next ∧
    ∃ token,
      ((s.lokal c).marken.find? (fun p => p.1.val == name.val)).map Prod.snd = some token ∧
      next.epoche = s.epoche ∧
      (next.lokal c).result = some (if token.nurRechte then .«protected»
        else .frames (token.frames k.plattform.ziel.seitengranule)) ∧
      (∀ bound ∈ (next.lokal c).marken, bound.2 ≠ token) ∧
      ρ.zeit.spur t = some (.kontext c w, ⟨[], [.ruecknahmeAbgeschlossen s.epoche token]⟩) ∧
      ρ.zeit.spur t = η.zeit.spur t ∧
      memFlushSicht.lesen (ρ.zeit.spur t) = some ((s.epoche, token), .freigeben) := by
  obtain ⟨before, after, frame, eval, label, advance⟩ := memKontextAmSchnitt matched cut head
  obtain ⟨token, binding, result, removed⟩ := MemInstruction.flushToken eval
  have key : (MemInstruction.flushSpace name).abschluss (η.zeit.zustand t) c = some token := binding
  have recorded : ρ.zeit.spur t = some (.kontext c w,
      ⟨[], [.ruecknahmeAbgeschlossen (η.zeit.zustand t).epoche token]⟩) := by
    rw [cut, label, MemInstruction.schrittSpur, key]
    rfl
  have observed : memFlushSicht.lesen (ρ.zeit.spur t) =
      some (((η.zeit.zustand t).epoche, token), .freigeben) := by
    rw [recorded]
    rfl
  refine ⟨before, after, token, binding, ?_, ?_, ?_, recorded,
    flushLabelGleich memFlushSicht (matched.spur t) observed, observed⟩
  · rw [advance]
    rfl
  · simpa only [advance, MemFrame.advance, Function.update_self] using result
  · simpa only [advance, MemFrame.advance, Function.update_self] using removed

/-- At consecutive named bind and completion cuts the key comes from the original pending result,
    with its epoch preserved. The bind is silent and the matched completion records that key. -/
theorem memBindFlushKennungImLauf {k : Katalog.Katalog} {code : List MemInstruction}
    {ρ : Maschine.Lauf (memProgram k code)} {η : Lauf (memProgram k code)}
    (matched : Laufabgleich ρ η) {t : Nat} {c : Kontext} {name : Ast.Identifier}
    {bindTrace flushTrace : SchrittSpur Nat UInt8}
    (bindCut : ρ.zeit.spur t = some (.kontext c (), bindTrace))
    (flushCut : ρ.zeit.spur (t + 1) = some (.kontext c (), flushTrace))
    (bindHead : (memProgram k code).system.kopf (η.zeit.zustand t) c = some (.bindToken name))
    (flushHead : (memProgram k code).system.kopf (η.zeit.zustand (t + 1)) c = some (.flushSpace name)) :
    let issued := η.zeit.zustand t
    let bound := η.zeit.zustand (t + 1)
    let completed := η.zeit.zustand (t + 1 + 1)
    ρ.zeit.spur t = some (.kontext c (), ⟨[], []⟩) ∧ completed.epoche = issued.epoche ∧
    ∃ token, (issued.lokal c).result = some (.pending token) ∧
      ((bound.lokal c).marken.find? (fun p => p.1.val == name.val)).map Prod.snd = some token ∧
      (completed.lokal c).result = some (if token.nurRechte then .«protected»
        else .frames (token.frames k.plattform.ziel.seitengranule)) ∧
      memFlushSicht.lesen (ρ.zeit.spur (t + 1)) = some ((issued.epoche, token), .freigeben) ∧
      ρ.zeit.spur (t + 1) = η.zeit.spur (t + 1) := by
  obtain ⟨_, _, frame, eval, label, advance⟩ := memKontextAmSchnitt matched bindCut bindHead
  obtain ⟨token, pending, lookup⟩ := MemInstruction.bindTokenLookup eval
  obtain ⟨_, _, finished, selected, epoch, result, _, _, matchedLabel, observed⟩ :=
    memFlushKennungImLauf matched flushCut flushHead
  have bound : (((η.zeit.zustand (t + 1)).lokal c).marken.find?
      (fun p => p.1.val == name.val)).map Prod.snd = some token := by
    simpa only [advance, MemFrame.advance, Function.update_self] using lookup
  have sameToken : finished = token := Option.some.inj (selected.symm.trans bound)
  subst finished
  have sameEpoch : (η.zeit.zustand (t + 1)).epoche = (η.zeit.zustand t).epoche := by
    rw [advance]
    rfl
  refine ⟨bindCut.trans (by rw [label]; rfl), epoch.trans sameEpoch,
    token, pending, bound, result, ?_, matchedLabel⟩
  simpa only [sameEpoch] using observed

end Gabbro.Core.Maschine.I
