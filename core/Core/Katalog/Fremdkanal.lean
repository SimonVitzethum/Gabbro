module

public import Core.Katalog.Aussen

@[expose] public section

namespace Gabbro.Core.Katalog

/-- A channel to a foreign process: a process in an address space outside the image,
    reached socket/pipe-style through the pinned `cProcess` row. Messages are byte
    sequences; `leihe` is the optional region currently lent to the foreign side
    (the only extent shared with the foreign address space). -/
structure FremdKanal where
  kanal : Nat
  leihe : Option Leihe
  deriving DecidableEq, Repr

/-- A message on the wire: copied bytes only, never a pointer and never a handle. -/
abbrev FremdNachricht := List UInt8

/-- The transport failure channel: refusal, unknown channel, oversize message. -/
inductive FremdFehler where
  | abgelehnt
  | keinKanal
  | zuGross
  deriving DecidableEq, Repr

/-- A foreign answer: delivered bytes or a transport error. -/
abbrev FremdErgebnis := Except FremdFehler FremdNachricht

/-- The byte store visible across the boundary. Gabbro cells are never mapped into
    the foreign address space; only the loaned extent is shared. -/
abbrev FremdSpeicher := Nat → UInt8

/-- The foreign step over the boundary: every byte outside the loaned extent is
    unchanged. The question and the answer are intentionally unconstrained: the row
    promises transport only (delivery or error) and nothing about foreign behaviour
    (arbitrary-change rely); answers are historical data, never currency. -/
def FremdSchritt (k : FremdKanal) (vor nach : FremdSpeicher) (_frage : FremdNachricht)
    (_antwort : FremdErgebnis) : Prop :=
  ∀ a, (∀ r, k.leihe = some r → ¬ r.region.drin a) → nach a = vor a

/-- The loan protocol over `Leihe`: owned (`eigen`) versus lent (`verliehen`).
    While lent, the foreign side may change bytes inside the loaned extent; on
    take-back the program revalidates, since foreign bytes are historical data. -/
inductive FremdPhase where
  | eigen
  | verliehen (loan : Leihe)
  deriving DecidableEq, Repr

inductive FremdLeiheAktion where
  | ausleihen (loan : Leihe)
  | zurueck (loan : Leihe)
  deriving DecidableEq, Repr

/-- Lend and take-back between the owned and the lent phase. -/
inductive FremdLeiheUebergang : FremdPhase → FremdLeiheAktion → FremdPhase → Prop where
  | ausleihen (loan : Leihe) : FremdLeiheUebergang .eigen (.ausleihen loan) (.verliehen loan)
  | zurueck (loan : Leihe) : FremdLeiheUebergang (.verliehen loan) (.zurueck loan) .eigen

/-- The phase of a channel is determined by its loan. -/
def FremdKanal.phase (k : FremdKanal) : FremdPhase :=
  match k.leihe with
  | none => .eigen
  | some loan => .verliehen loan

theorem fremdkanal_phase_eigen (kanal : Nat) :
    (⟨kanal, none⟩ : FremdKanal).phase = .eigen := by
  rfl

theorem fremdkanal_phase_verliehen (kanal : Nat) (loan : Leihe) :
    (⟨kanal, some loan⟩ : FremdKanal).phase = .verliehen loan := by
  rfl

/-- The channel question runs over the existing question class (`frage`): an
    `exchange` on the pinned `cProcess` row, with no additional objects. No new
    command constructor is needed (commands belong to MK-06; none is required here). -/
def FremdKanal.frage (k : FremdKanal) (h : Handle) (msg : FremdNachricht) : Frage :=
  ⟨.cProcess, h, [], .exchange msg⟩

/-- The row offers the channel question: `exchange` on `cProcess` with no extra objects. -/
theorem fremdkanal_angebot (p : Plattform) (k : FremdKanal) (h : Handle) (msg : FremdNachricht) :
    p.operationAngeboten (k.frage h msg) = true := by
  cases p <;> rfl

/-- The failure channel: a denied handle is answered explicitly, never silently dropped. -/
theorem fremdkanal_fehlerkanal (p : Plattform) (s : AussenSicht) (k : FremdKanal) (h : Handle)
    (msg : FremdNachricht)
    (denied : (k.frage h msg).zugriffe.all (s.gueltig .cProcess) = false) :
    ∃ a, atomar p s (k.frage h msg) = .antwort a ∧ a.result.isOk = false :=
  ⟨_, atomar_ungueltig (fremdkanal_angebot p k h msg) denied, rfl⟩

/-- **The foreign-channel statement.** In every trace through the channel — the only
    way foreign code acts in a run of an accepted unit — the foreign side changes no
    byte outside the loaned extent, and no guarantee rests on its behaviour: every
    answer (any bytes, any transport error) is a possible foreign step, so the
    foreign side delivers at most wrong answers. Acceptance never constrains foreign
    answers; commit validity is re-established atomically per question or not at all. -/
def FremdKanalAussage : Prop :=
  (∀ (k : FremdKanal) (vor nach : FremdSpeicher) (frage : FremdNachricht) (antwort : FremdErgebnis),
    FremdSchritt k vor nach frage antwort →
    ∀ a, (∀ r, k.leihe = some r → ¬ r.region.drin a) → nach a = vor a)
  ∧ ∀ (k : FremdKanal) (vor : FremdSpeicher) (frage : FremdNachricht) (antwort : FremdErgebnis),
    ∃ nach, FremdSchritt k vor nach frage antwort

/-- The row keeps its promise: integrity by unfolding, answer freedom by stuttering. -/
theorem fremdkanal_gilt : FremdKanalAussage := by
  refine ⟨?_, ?_⟩
  · intro k vor nach frage antwort schritt a ausserhalb
    exact schritt a ausserhalb
  · intro k vor frage antwort
    exact ⟨vor, fun _ _ => rfl⟩

/-- Satisfiability: a channel with no loan, the identical store, and a refused answer. -/
theorem FremdKanalAussage_erfuellbar :
    ∃ (k : FremdKanal) (vor nach : FremdSpeicher) (frage : FremdNachricht) (antwort : FremdErgebnis),
      FremdSchritt k vor nach frage antwort :=
  ⟨⟨0, none⟩, fun _ => 0, fun _ => 0, [], .error .abgelehnt, fun _ _ => rfl⟩

/-- Non-triviality: without address-space separation — a foreign step writing an
    unloaned byte — the integrity conjunct breaks. -/
theorem FremdKanalAussage_nichtTrivial :
    ∃ (k : FremdKanal) (vor nach : FremdSpeicher) (a : Nat),
      (∀ r, k.leihe = some r → ¬ r.region.drin a) ∧ nach a ≠ vor a := by
  refine ⟨⟨0, none⟩, fun _ => 0, fun b => if b = 0 then 1 else 0, 0, ?_, ?_⟩
  · intro r hr
    cases hr
  · show (1 : UInt8) ≠ 0
    intro h
    have t : (1 : Nat) = 0 := congrArg UInt8.toNat h
    exact absurd t (by decide)

end Gabbro.Core.Katalog
