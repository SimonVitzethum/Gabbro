/-
  File:      Grammatik/SperrImpl.lean
  Subject:   THE LOCK-IMPLEMENTATION CONTRACT -- what an own `nimm`/`gib`
              owes the checker (N042, tenth case).

  CONTEXT. Locks are declaration facts with ticket proofs (`ticket_ausschluss`
  in `CTicket.lean`, `Schlusssatz124Ticket.lean`), but the transfer to the
  IMPLEMENTATION is open: the contract an own `nimm`/`gib` pair owes -- the
  C bodies behind the prototypes the emitter writes for `lock TOR`
  (`emit.rs`: only `void TOR_nimm(void);` / `void TOR_gib(void);`, "the
  primitive itself is trust base, not product"; the names the generator forms
  are `erzeugernamen.rs`: `{Lock}_nimm`, `{Lock}_gib`) -- is not written down.
  The tenth case of `N042` (`namen.rs`): `lock TOR` next to
  `extern fn TOR_nimm()` compiles clean (`void TOR_nimm(void);` twice is a
  legal repetition in C), so the acquire call lands in the foreign function
  at link time with nothing in the chain saying a word. Such a foreign
  `nimm`/`gib` is a LOCK IMPLEMENTATION, and this file is what it owes.

  THE CONTRACT (`LockImplVertrag`, §1). One predicate over the abstract lock
  meaning `SperrSem` (`CNebenlaeufig.lean`): every behaviour of the
  implementation is a behaviour of `sperrAbstrakt`. That is exactly the field
  `LaufzeitC.sperre` -- no new premise shape. Its three named aspects (§2):
  * ATOMICITY (`lockVertrag_atomar`): a primitive step touches only its own
    lock's holder entry (`sperrAbstrakt_rahmen`); program memory is untouched
    by construction (`ticket_frame` for the ticket lock).
  * ORDER (`lockVertrag_ordnung_nimm`, `lockVertrag_ordnung_gib`): `nimm`
    fires only on a free lock, `gib` only for the holder.
  * HOLD TIME (`lockVertrag_halte_nimm`, `lockVertrag_halte_gib`,
    `lockVertrag_exklusiv`): the acquire makes the caller the holder, the
    release frees exactly that entry, and on every reachable configuration
    at most one thread holds one lock.

  WHO DISCHARGES IT, WHO DEMANDS IT (§3-§5).
  * The ticket lock DISCHARGES it (`ticket_erfuellt_lockImplVertrag`, from
    `ticketLP_sperrAbstrakt`): the `LaufzeitC.sperre` clause of stage (b) is
    a theorem for it, not an assumption.
  * A declaration lock `L : D.Lock` DEMANDS the per-lock form
    (`LockGiltAn`, `lockGiltAn_aus_vertrag`) at its runtime number `lnr L`
    -- the number the `SegPasst` `gibt`/`nimmt` fields tie the G lock steps
    to. An own `nimm`/`gib` (an `extern fn TOR_nimm`, N042 tenth case) OWES
    that clause.
  * DOCKING. The contract plugs into `LaufzeitC.sperre`
    (`lockVertrag_gibt_laufzeitC`): premise group (d)-side of stage (b), the
    runtime list. `NutzerPflicht` (the user's logic) and `HardwareAnnahmen`
    (`GutO`, `RegLokal`, `AxVertragO`: frames of foreign code, not lock
    order) are UNCHANGED, and the text of `GabbroZiel`
    (`Zielsatz/Spec.lean`) is UNCHANGED.

  SHARPNESS (§4). The contract rules out exactly the unchecked release:
  `rohLP` (release without holder check, the abstraction of `gibtRoh`) does
  NOT satisfy it (`rohLP_verletzt`) -- the finding `gib_ohne_wache`: the
  guard `L ∈ haelt t` is supplied by the PROGRAM (the checker's lock
  discipline), not by the lock. What it does NOT demand: FIFO
  (`ticket_mehr_als_frei`: the ticket order is visible beyond held-or-free,
  strictly more than `sperrAbstrakt_nur_eigen`; `ticket_fifo` stays a
  ticket-only strength, needed for the waiting bound `FifoSperre`, not for
  safety). Wraparound at 2^32 stays a CUT of `CTicket.lean`.

  WITNESSES (rule 13, `zeugenpflicht`): every ∀-theorem below has its
  `_zeuge`: `lockVertrag_instanz_zeuge` (the contract has instances),
  `sperrAbstrakt_instanz_zeuge` (the specification itself is non-empty),
  `lockGiltAn_zeuge` (the per-lock form is inhabited),
  `lockVertrag_atomar_zeuge`, `lockVertrag_ordnung_nimm_zeuge`,
  `lockVertrag_ordnung_gib_zeuge`, `lockVertrag_halte_nimm_zeuge`,
  `lockVertrag_halte_gib_zeuge` (each aspect fires on the ticket lock),
  `lockVertrag_exklusiv_zeuge` (exclusion on the contended run of
  `schlusssatz_124_zeuge`), `lockVertrag_laufzeit_zeuge` (the docking lemma
  fires on `c124` with the ticket lock). `rohLP_verletzt` is a refutation
  and needs none.
-/
import Grammatik.CTicket
import Grammatik.Schlusssatz124

namespace Gabbro.Grammatik

/-! ## 1. The contract, whole and per lock -/

/-- **THE LOCK-IMPLEMENTATION CONTRACT.** Every behaviour of the lock
    primitive `LP` is a behaviour of `sperrAbstrakt`: `nimm` only on a free
    lock making the caller its holder, `gib` only by the holder freeing it.
    This is exactly the field `LaufzeitC.sperre` (`CNebenlaeufig.lean`); an
    own `nimm`/`gib` (N042 tenth case: `extern fn TOR_nimm()` next to
    `lock TOR`) owes it, a declaration lock demands its per-lock form
    (`LockGiltAn`) at its runtime number. -/
def LockImplVertrag (LP : SperrSem) : Prop :=
  ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h'

/-- **The per-lock form.** What the declaration lock at runtime number `L`
    demands of the primitive linked there (`lnr L` in `SegPasst`): the
    `sperrAbstrakt` behaviour for calls about `L`. -/
def LockGiltAn (LP : SperrSem) (L : Nat) : Prop :=
  ∀ t op h h', op.nr = L → LP t op h h' → sperrAbstrakt t op h h'

/-- The whole contract gives every lock's clause. -/
theorem lockGiltAn_aus_vertrag {LP : SperrSem} (hv : LockImplVertrag LP) (L : Nat) :
    LockGiltAn LP L :=
  fun _ _ _ _ _ hs => hv _ _ _ _ hs

/-- The lock clauses give the whole contract. -/
theorem vertrag_aus_lockGiltAn {LP : SperrSem} (hv : ∀ L, LockGiltAn LP L) :
    LockImplVertrag LP :=
  fun t op h h' hs => hv op.nr t op h h' rfl hs

/-! ## 2. The three aspects: atomicity, order, hold time -/

/-- **ATOMICITY.** A contract-faithful primitive changes nothing but its own
    lock's holder entry. -/
theorem lockVertrag_atomar {LP : SperrSem} (hv : LockImplVertrag LP) {t : Faden}
    {op : SperrOp} {h h' : Halter} (hs : LP t op h h') (L : Nat) (hL : L ≠ op.nr) :
    h' L = h L :=
  sperrAbstrakt_rahmen (hv t op h h' hs) L hL

/-- **ORDER, acquire.** `nimm` fires only on a free lock. -/
theorem lockVertrag_ordnung_nimm {LP : SperrSem} (hv : LockImplVertrag LP) {t : Faden}
    {L : Nat} {h h' : Halter} (hs : LP t (.nimm L) h h') : h L = none := by
  obtain ⟨hfrei, -⟩ := hv t (.nimm L) h h' hs
  exact hfrei

/-- **ORDER, release.** `gib` fires only for the holder. -/
theorem lockVertrag_ordnung_gib {LP : SperrSem} (hv : LockImplVertrag LP) {t : Faden}
    {L : Nat} {h h' : Halter} (hs : LP t (.gib L) h h') : h L = some t := by
  obtain ⟨hhalt, -⟩ := hv t (.gib L) h h' hs
  exact hhalt

/-- **HOLD TIME, acquire.** The acquire makes the caller the holder. -/
theorem lockVertrag_halte_nimm {LP : SperrSem} (hv : LockImplVertrag LP) {t : Faden}
    {L : Nat} {h h' : Halter} (hs : LP t (.nimm L) h h') :
    h' = halterSetze h L (some t) := by
  obtain ⟨-, rfl⟩ := hv t (.nimm L) h h' hs
  rfl

/-- **HOLD TIME, release.** The release frees exactly that entry. -/
theorem lockVertrag_halte_gib {LP : SperrSem} (hv : LockImplVertrag LP) {t : Faden}
    {L : Nat} {h h' : Halter} (hs : LP t (.gib L) h h') :
    h' = halterSetze h L none := by
  obtain ⟨-, rfl⟩ := hv t (.gib L) h h' hs
  rfl

/-- **One step keeps single-holders.** With `K` fixed (as in `schrittC_inv`),
    a `SchrittC` step under a contract-faithful primitive preserves the
    at-most-one-holder property. (Auxiliary to `lockVertrag_exklusiv`;
    witnessed by `lockVertrag_exklusiv_zeuge`.) -/
theorem lockVertrag_schritt {E : CEinheit} {K K' : KonfC} {t : Faden} {ℓ : Etikett}
    {LP : SperrSem} (hv : LockImplVertrag LP) (hs : SchrittC E LP K t ℓ K')
    (ih : ∀ L t' u', K.halter L = some t' → K.halter L = some u' → t' = u') :
    ∀ L t' u', K'.halter L = some t' → K'.halter L = some u' → t' = u' := by
  cases hs with
  | teile a b k ρ _ =>
      intro L t' u' h1 h2
      exact ih L t' u' h1 h2
  | ende ρ _ =>
      intro L t' u' h1 h2
      exact ih L t' u' h1 h2
  | block s k ρ st' ρ' _ _ _ =>
      intro L t' u' h1 h2
      exact ih L t' u' h1 h2
  | rueck s k ρ st' v _ _ _ =>
      intro L t' u' h1 h2
      exact ih L t' u' h1 h2
      | sperre n k ρ op h' _ _ hl =>
          have hab := hv t op K.halter h' hl
          cases op with
          | nimm L0 =>
              obtain ⟨-, rfl⟩ := hab
              intro L t' u' h1 h2
              have h1' : halterSetze K.halter L0 (some t) L = some t' := h1
              have h2' : halterSetze K.halter L0 (some t) L = some u' := h2
              by_cases eL : L = L0
              · subst eL
                rw [halterSetze_eq] at h1' h2'
                cases h1'
                cases h2'
                rfl
              · rw [halterSetze_ne _ _ _ _ eL] at h1' h2'
                exact ih L t' u' h1' h2'
          | gib L0 =>
              obtain ⟨-, rfl⟩ := hab
              intro L t' u' h1 h2
              have h1' : halterSetze K.halter L0 none L = some t' := h1
              have h2' : halterSetze K.halter L0 none L = some u' := h2
              by_cases eL : L = L0
              · subst eL
                rw [halterSetze_eq] at h1'
                cases h1'
              · rw [halterSetze_ne _ _ _ _ eL] at h1' h2'
                exact ih L t' u' h1' h2'

/-- **HOLD TIME, reachable exclusion.** On every configuration reachable from
    a holder-free start under a contract-faithful primitive, at most one
    thread holds one lock. -/
theorem lockVertrag_exklusiv {E : CEinheit} {K0 K : KonfC} {LP : SperrSem}
    (hv : LockImplVertrag LP) (h0 : ∀ L, K0.halter L = none)
    (h : ErreichbarC E LP K0 K) : ∀ L t u, K.halter L = some t → K.halter L = some u →
      t = u := by
  induction h with
  | start =>
      intro L t u ht hu
      rw [h0 L] at ht
      cases ht
  | schritt hR hs ih =>
      exact lockVertrag_schritt hv hs ih

/-- **DOCKING.** The contract discharges the `sperre` field of the runtime
    list: with thread creation at declared roots, a contract-faithful
    primitive IS the `LaufzeitC` stage (b) assumes. `NutzerPflicht` and
    `HardwareAnnahmen` are untouched. -/
theorem lockVertrag_gibt_laufzeitC {E : CEinheit} {wurzeln : List Nat} {st0 : CSt}
    {K0 : KonfC} {LP : SperrSem} (hf : FadenStartC E wurzeln st0 K0)
    (hv : LockImplVertrag LP) : LaufzeitC E wurzeln st0 K0 LP :=
  ⟨hf, fun t op h h' hs => hv t op h h' hs⟩

/-! ## 3. The ticket lock discharges the contract -/

/-- **THE TICKET LOCK MEETS THE CONTRACT.** The `sperre` clause of stage (b)
    for the lock the runtime has: `ticketLP_sperrAbstrakt`, read as the
    implementation contract. -/
theorem ticket_erfuellt_lockImplVertrag : LockImplVertrag ticketLP :=
  ticketLP_sperrAbstrakt

/-- The per-lock form at any runtime number. -/
theorem ticket_giltAn (L : Nat) : LockGiltAn ticketLP L :=
  fun _ _ _ _ _ hs => ticket_erfuellt_lockImplVertrag _ _ _ _ hs

/-- The specification itself meets the contract (non-vacuity at the spec). -/
theorem sperrAbstrakt_erfuellt : LockImplVertrag sperrAbstrakt :=
  fun _ _ _ _ h => h

/-! ## 4. Sharpness: the unchecked release violates the contract -/

/-- **The release the runtime does NOT perform, as an abstract primitive**:
    `now++` without a holder check (`gibtRoh` in `CTicket.lean`): any caller
    frees the lock. -/
def rohLP : SperrSem :=
  fun _ op h h' => ∃ L, op = .gib L ∧ h' = halterSetze h L none

/-- **The unchecked release violates the contract** (`gib_ohne_wache` at the
    abstract level): from a free lock, `rohLP` releases -- `sperrAbstrakt`
    does not. So the guard `L ∈ haelt t` is owed by the program (the
    checker's lock discipline: a `L_gib()` is emitted only where the holder
    stands), and an own `gib` without it does not meet `LockImplVertrag`. -/
theorem rohLP_verletzt : ¬ LockImplVertrag rohLP := by
  intro hv
  have hs : rohLP 5 (.gib 0) (fun _ => none) (halterSetze (fun _ => none) 0 none) :=
    ⟨0, rfl, rfl⟩
  have hc := (hv 5 (.gib 0) _ _ hs).1
  simp at hc

/-! ## 5. Witnesses -/

/-- The contract has instances: the ticket lock takes lock `0` from free. -/
theorem lockVertrag_instanz_zeuge :
    ∃ t op h h', ticketLP t op h h' ∧ sperrAbstrakt t op h h' := by
  obtain ⟨hIe, _, hAe, _, _, _, _⟩ := ticket_mehr_als_frei
  have hfrei : ∀ u, (0 : Nat) ∉ zEins.haelt u := by
    intro u hu
    have e : (none : Option Faden) = some u := (hAe 0 u).mpr hu
    cases e
  exact ⟨7, .nimm 0, fun _ => none, halterSetze (fun _ => none) 0 (some 7),
    ⟨zEins, trittT zEins 7 0, hIe, hAe, abs_tritt (t := 7) hAe hfrei,
      TSchritt.tritt zEins 7 0 0 rfl rfl⟩,
    ⟨rfl, rfl⟩⟩

/-- The specification itself is non-empty. -/
theorem sperrAbstrakt_instanz_zeuge : ∃ t op h h', sperrAbstrakt t op h h' :=
  ⟨7, .nimm 0, fun _ => none, halterSetze (fun _ => none) 0 (some 7), rfl, rfl⟩

/-- The per-lock form is inhabited (at lock `0`, by the ticket lock). -/
theorem lockGiltAn_zeuge : LockGiltAn ticketLP 0 :=
  fun _ _ _ _ _ hs => ticket_erfuellt_lockImplVertrag _ _ _ _ hs

/-- Atomicity fires: the ticket acquire of lock `0` leaves lock `1` alone. -/
theorem lockVertrag_atomar_zeuge :
    ∃ t h h', ticketLP t (.nimm 0) h h' ∧ h' 1 = h 1 := by
  obtain ⟨hIe, _, hAe, _, _, _, _⟩ := ticket_mehr_als_frei
  have hfrei : ∀ u, (0 : Nat) ∉ zEins.haelt u := by
    intro u hu
    have e : (none : Option Faden) = some u := (hAe 0 u).mpr hu
    cases e
  exact ⟨7, fun _ => none, halterSetze (fun _ => none) 0 (some 7),
    ⟨zEins, trittT zEins 7 0, hIe, hAe, abs_tritt (t := 7) hAe hfrei,
      TSchritt.tritt zEins 7 0 0 rfl rfl⟩,
    by decide⟩

/-- Order fires, acquire: the ticket `nimm` needs the lock free. -/
theorem lockVertrag_ordnung_nimm_zeuge :
    ∃ t h h', ticketLP t (.nimm 0) h h' ∧ h 0 = none := by
  obtain ⟨hIe, _, hAe, _, _, _, _⟩ := ticket_mehr_als_frei
  have hfrei : ∀ u, (0 : Nat) ∉ zEins.haelt u := by
    intro u hu
    have e : (none : Option Faden) = some u := (hAe 0 u).mpr hu
    cases e
  exact ⟨7, fun _ => none, halterSetze (fun _ => none) 0 (some 7),
    ⟨zEins, trittT zEins 7 0, hIe, hAe, abs_tritt (t := 7) hAe hfrei,
      TSchritt.tritt zEins 7 0 0 rfl rfl⟩,
    rfl⟩

/-- Membership in the ticket state `zDrin`: thread `1` holds lock `0`, and
    nothing else is held. -/
theorem zDrin_halt_zeuge (u K : Nat) : K ∈ zDrin.haelt u ↔ (u = 1 ∧ K = 0) := by
  show K ∈ (if u = 1 then [(0 : Nat)] else []) ↔ _
  by_cases e : u = 1
  · subst e
    rw [if_pos rfl]
    constructor
    · intro hK
      rcases List.mem_cons.mp hK with rfl | h'
      · exact ⟨rfl, rfl⟩
      · exact absurd h' List.not_mem_nil
    · rintro ⟨-, rfl⟩
      exact List.mem_cons_self
  · rw [if_neg e]
    constructor
    · intro hK
      exact absurd hK List.not_mem_nil
    · rintro ⟨rfl, -⟩
      exact absurd rfl e

/-- Order fires, release: the ticket `gib` needs the caller holding. -/
theorem lockVertrag_ordnung_gib_zeuge :
    ∃ t h h', ticketLP t (.gib 0) h h' ∧ h 0 = some t := by
  obtain ⟨hId, h10, _, _⟩ := gib_ohne_wache
  have hAbs : AbsT zDrin (halterSetze (fun _ => none) 0 (some 1)) := by
    intro K u
    by_cases eK : K = 0
    · subst eK
      rw [halterSetze_eq]
      constructor
      · intro he
        have e : (1 : Faden) = u := Option.some.inj he
        subst e
        exact h10
      · intro hu
        have hu1 : u = 1 := ((zDrin_halt_zeuge u 0).mp hu).1
        subst hu1
        rfl
    · rw [halterSetze_ne _ _ _ _ eK]
      constructor
      · intro he
        have e : (none : Option Faden) = some u := he
        cases e
      · intro hu
        have hK0 : K = 0 := ((zDrin_halt_zeuge u K).mp hu).2
        exact absurd hK0 eK
  exact ⟨1, halterSetze (fun _ => none) 0 (some 1),
    halterSetze (halterSetze (fun _ => none) 0 (some 1)) 0 none,
    ⟨zDrin, gibtT zDrin 1 0, hId, hAbs, abs_gibt hId hAbs h10,
      TSchritt.gibt zDrin 1 0 h10⟩,
    by rw [halterSetze_eq]⟩

/-- Hold time fires, acquire: the ticket `nimm` makes the caller the holder. -/
theorem lockVertrag_halte_nimm_zeuge :
    ∃ t h h', ticketLP t (.nimm 0) h h' ∧ h' 0 = some t := by
  obtain ⟨hIe, _, hAe, _, _, _, _⟩ := ticket_mehr_als_frei
  have hfrei : ∀ u, (0 : Nat) ∉ zEins.haelt u := by
    intro u hu
    have e : (none : Option Faden) = some u := (hAe 0 u).mpr hu
    cases e
  exact ⟨7, fun _ => none, halterSetze (fun _ => none) 0 (some 7),
    ⟨zEins, trittT zEins 7 0, hIe, hAe, abs_tritt (t := 7) hAe hfrei,
      TSchritt.tritt zEins 7 0 0 rfl rfl⟩,
    by rw [halterSetze_eq]⟩

/-- Hold time fires, release: the ticket `gib` frees the entry. -/
theorem lockVertrag_halte_gib_zeuge :
    ∃ t h h', ticketLP t (.gib 0) h h' ∧ h' 0 = none := by
  obtain ⟨hId, h10, _, _⟩ := gib_ohne_wache
  have hAbs : AbsT zDrin (halterSetze (fun _ => none) 0 (some 1)) := by
    intro K u
    by_cases eK : K = 0
    · subst eK
      rw [halterSetze_eq]
      constructor
      · intro he
        have e : (1 : Faden) = u := Option.some.inj he
        subst e
        exact h10
      · intro hu
        have hu1 : u = 1 := ((zDrin_halt_zeuge u 0).mp hu).1
        subst hu1
        rfl
    · rw [halterSetze_ne _ _ _ _ eK]
      constructor
      · intro he
        have e : (none : Option Faden) = some u := he
        cases e
      · intro hu
        have hK0 : K = 0 := ((zDrin_halt_zeuge u K).mp hu).2
        exact absurd hK0 eK
  exact ⟨1, halterSetze (fun _ => none) 0 (some 1),
    halterSetze (halterSetze (fun _ => none) 0 (some 1)) 0 none,
    ⟨zDrin, gibtT zDrin 1 0, hId, hAbs, abs_gibt hId hAbs h10,
      TSchritt.gibt zDrin 1 0 h10⟩,
    by rw [halterSetze_eq]⟩

/-- Exclusion is non-vacuous: on the contended run of `schlusssatz_124_zeuge`
    thread `0` holds lock `0`, and no second holder fits beside it. -/
theorem lockVertrag_exklusiv_zeuge :
    ∃ K : KonfC, ErreichbarC K124.c124 sperrAbstrakt K124.KAB K ∧ K.halter 0 = some 0 ∧
      ∀ t u, K.halter 0 = some t → K.halter 0 = some u → t = u := by
  obtain ⟨_, _, _, Kb, _, _, hKbE, hKbH, _⟩ := K124.schlusssatz_124_zeuge
  exact ⟨Kb, hKbE, hKbH, fun t u ht hu =>
    lockVertrag_exklusiv (fun _ _ _ _ h => h) (fun _ => rfl) hKbE 0 t u ht hu⟩

/-- The docking lemma fires: `c124` with the ticket lock IS a `LaufzeitC`. -/
theorem lockVertrag_laufzeit_zeuge :
    LaufzeitC K124.c124 [2, 3] K124.st0 K124.KAB ticketLP :=
  lockVertrag_gibt_laufzeitC
    ⟨K124.wAB, rfl, K124.wAB_wurzeln.1, K124.wAB_wurzeln.2⟩
    ticket_erfuellt_lockImplVertrag

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.lockGiltAn_aus_vertrag
#print axioms Gabbro.Grammatik.vertrag_aus_lockGiltAn
#print axioms Gabbro.Grammatik.lockVertrag_atomar
#print axioms Gabbro.Grammatik.lockVertrag_ordnung_nimm
#print axioms Gabbro.Grammatik.lockVertrag_ordnung_gib
#print axioms Gabbro.Grammatik.lockVertrag_halte_nimm
#print axioms Gabbro.Grammatik.lockVertrag_halte_gib
#print axioms Gabbro.Grammatik.lockVertrag_schritt
#print axioms Gabbro.Grammatik.lockVertrag_exklusiv
#print axioms Gabbro.Grammatik.lockVertrag_gibt_laufzeitC
#print axioms Gabbro.Grammatik.ticket_erfuellt_lockImplVertrag
#print axioms Gabbro.Grammatik.ticket_giltAn
#print axioms Gabbro.Grammatik.sperrAbstrakt_erfuellt
#print axioms Gabbro.Grammatik.rohLP_verletzt
#print axioms Gabbro.Grammatik.lockVertrag_instanz_zeuge
#print axioms Gabbro.Grammatik.lockVertrag_exklusiv_zeuge
#print axioms Gabbro.Grammatik.lockVertrag_laufzeit_zeuge
