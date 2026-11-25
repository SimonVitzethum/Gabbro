/-
  File:      core/Core/Annahme/DomaeneBeweise/NI.lean
  Subject:   MK-17 open item 2 — the domain noninterference connection `DomaenenNIAussage`
              (core/Core/Annahme/Domaene.lean). This file does not change any statement; it proves
              the partial results that are available and locates the missing step exactly.

  Finding. `DomaenenNIAussage` is equivalent to the generic claim "every accepted unit is
  noninterferent". The channel premise `KanalTragenNiedrig` is vacuous for the single-domain plan
  and contributes nothing to the flow argument: `ni_akzeptierter_einheit` never reads it. The generic
  claim is proved in this tree only for fragment units (`Beobachtung.fragment_nichtinterferent`);
  for an arbitrary accepted `Einheit` the four run-level bridges (Start, Regel, Protokoll, Pause)
  are not consequences of `Akzeptiert E`, because acceptance inspects only `.ideal` and leaves the
  implementation machine `.impl` — the thing runs and therefore `Nichtinterferent` quantify over —
  unconstrained. `KanalTragenNiedrig` only constrains `E.etiketten.frage` labels, not `.impl` runs.

  Delivered here: the vacuity lemma, the equivalence, and the strengthened theorem that closes the
  statement once the four bridges are supplied as premises. Missing step: supply those four bridges
  for an arbitrary accepted unit (or refute the generic claim at the implementation machine).
-/
module

public import Core.Annahme.Domaene
public import Core.Beobachtung.Satz

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- The channel-lowering premise is vacuous for the single-domain plan: both the object domain and
    the context domain are `0`, so no cross-domain question exists to be constrained. -/
theorem kanalTragenNiedrig_eineDomaene
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    KanalTragenNiedrig E eineDomaene := by
  intro c q h
  exact (h rfl).elim

/-- If the generic accepted-implies-noninterference claim holds, the domain statement follows;
    the plan and its channel premise are not used. -/
theorem domaenenNI_aus_akzeptiertNI
    (h : ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι),
      Akzeptiert E → Beobachtung.Nichtinterferent E) :
    DomaenenNIAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl ι inst E plan hE hkanal
  exact h E hE

/-- Conversely the domain statement already contains the generic claim: instantiate it at the
    single-domain plan, whose channel premise is vacuous. Hence the two statements are equivalent
    and `KanalTragenNiedrig` is redundant for this statement. -/
theorem akzeptiertNI_aus_domaenenNI (h : DomaenenNIAussage) :
    ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι),
      Akzeptiert E → Beobachtung.Nichtinterferent E := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl ι inst E hE
  exact h E eineDomaene hE (kanalTragenNiedrig_eineDomaene E)

/-- Strengthened form: with the four run-level NI bridges as premises the domain statement is a
    direct instance of `ni_akzeptierter_einheit`. These four bridges are the exact missing step;
    acceptance supplies only their source-level counterparts `StartFlussLokal` / `RegelFluss`. -/
theorem domaenenNI_aus_pflichten
    (start : ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι),
      Beobachtung.StartFlussLokal E → Beobachtung.StartNIPflicht E)
    (formen : ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι),
      ∀ f, Beobachtung.RegelFluss E f → Beobachtung.RegelNIPflicht E f)
    (protokoll : ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι),
      Beobachtung.ProtokollNIPflicht E)
    (pause : ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι),
      Beobachtung.PausenNIPflicht E) :
    DomaenenNIAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl ι inst E plan hE hkanal
  exact Beobachtung.ni_akzeptierter_einheit E hE (start E) (formen E) (protokoll E) (pause E)

end Gabbro.Core.Annahme
