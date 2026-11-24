module

public import Core.Verfeinerung.Abnahme.Effekte
public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

inductive FlushPhase where
  | senden (ziele : List Kern)
  | handler (kern : Kern)
  | bestaetigen (kern : Kern)
  | freigeben

/-- The ordering of one revocation's phases. Each key identifies one revocation, including its generation
    and epoch. The prefix may end after any phase. A release needs evidence for every target, and a
    reset cannot turn pre-crash evidence into a valid release. This chain alone admits a release after
    a send to nobody (`FlushKette.ohne_abdeckung`), so it is never the whole protocol. -/
structure FlushKette {Id : Type} (spur : Nat → Option (Id × FlushPhase))
    (absturz : Nat → Prop) : Prop where
  eindeutig : ∀ id phase t u, spur t = some (id, phase) → spur u = some (id, phase) → t = u
  eineSendung : ∀ id xs ys t u, spur t = some (id, .senden xs) →
    spur u = some (id, .senden ys) → t = u
  sendung : ∀ id k t, spur t = some (id, .handler k) →
    ∃ s ziele, s < t ∧ spur s = some (id, .senden ziele) ∧ k ∈ ziele ∧
      ∀ u, s ≤ u → u < t → ¬ absturz u
  bestaetigung : ∀ id k t, spur t = some (id, .bestaetigen k) →
    ∃ h, h < t ∧ spur h = some (id, .handler k) ∧
      ∀ u, h ≤ u → u < t → ¬ absturz u
  freigabe : ∀ id t, spur t = some (id, .freigeben) →
    ∃ s ziele, s < t ∧ spur s = some (id, .senden ziele) ∧
      (∀ u, s ≤ u → u < t → ¬ absturz u) ∧
      ∀ k, k ∈ ziele → ∃ h a, s < h ∧ h < a ∧ a < t ∧
        spur h = some (id, .handler k) ∧ spur a = some (id, .bestaetigen k)

/-- **The shootdown protocol.** The chain, and the send names every core that exists (`kern`): a core
    left out would keep a stale translation while its frames are released. -/
structure FlushProtokoll {Id : Type} (spur : Nat → Option (Id × FlushPhase))
    (absturz : Nat → Prop) (kern : Kern → Prop) : Prop extends FlushKette spur absturz where
  abdeckung : ∀ id ziele t, spur t = some (id, .senden ziele) → ∀ k, kern k → k ∈ ziele

/-- Why the chain is not enough: a send to nobody followed by a release satisfies every chain
    condition, so a release without any invalidation, on any core, is a legal trace of the chain. -/
theorem FlushKette.ohne_abdeckung :
    ∃ spur : Nat → Option (Nat × FlushPhase), FlushKette spur (fun _ => False) ∧
      ∃ k, ¬ ∀ ziele t, spur t = some (0, .senden ziele) → k ∈ ziele := by
  let spur : Nat → Option (Nat × FlushPhase) := fun t =>
    if t = 0 then some (0, .senden []) else if t = 1 then some (0, .freigeben) else none
  have inv : ∀ t id phase, spur t = some (id, phase) →
      (t = 0 ∧ id = 0 ∧ phase = .senden []) ∨ (t = 1 ∧ id = 0 ∧ phase = .freigeben) := by
    intro t id phase h
    by_cases t0 : t = 0
    · have e : spur t = some (0, FlushPhase.senden []) := by simp only [spur, if_pos t0]
      rw [e] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨t0, h.1.symm, h.2.symm⟩
    · by_cases t1 : t = 1
      · have e : spur t = some (0, FlushPhase.freigeben) := by
          simp only [spur, if_neg t0, if_pos t1]
        rw [e] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inr ⟨t1, h.1.symm, h.2.symm⟩
      · have e : spur t = none := by simp only [spur, if_neg t0, if_neg t1]
        rw [e] at h
        cases h
  refine ⟨spur, ⟨?_, ?_, ?_, ?_, ?_⟩, 0, fun all => ?_⟩
  · intro id phase t u ht hu
    rcases inv t id phase ht with ⟨h1, _, h2⟩ | ⟨h1, _, h2⟩ <;>
      rcases inv u id phase hu with ⟨h3, _, h4⟩ | ⟨h3, _, h4⟩ <;>
        first | omega | exact absurd (h2.symm.trans h4) (by intro h; cases h)
  · intro id xs ys t u ht hu
    rcases inv t id _ ht with ⟨h1, _, h2⟩ | ⟨h1, _, h2⟩ <;>
      rcases inv u id _ hu with ⟨h3, _, h4⟩ | ⟨h3, _, h4⟩ <;>
        first | omega | (cases h2; done) | (cases h4; done)
  · intro id k t ht
    rcases inv t id _ ht with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · intro id k t ht
    rcases inv t id _ ht with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  · intro id t ht
    rcases inv t id _ ht with ⟨h1, _, h2⟩ | ⟨h1, h0, _⟩
    · cases h2
    · subst h1
      subst h0
      exact ⟨0, [], by omega, rfl, fun _ _ _ h => h, fun k hk => by cases hk⟩
  · have := all [] 0 rfl
    cases this

/-- **Release leaves no stale translation.** Under the protocol, every core that exists has run its handler
    before the release, no handler is undone (no refill of a revoked page: its table entries are gone
    from the send on), and a cell sits on an existing core only: no cell of the range survives the release. -/
theorem FlushProtokoll.frei_bei_freigabe {Id : Type} {spur : Nat → Option (Id × FlushPhase)}
    {absturz : Nat → Prop} {kern : Kern → Prop} (protokoll : FlushProtokoll spur absturz kern)
    {Zelle : Type} (zellen : Nat → Zelle → Prop) (kernVon : Zelle → Kern) (bereich : Zelle → Prop)
    (nurKerne : ∀ t z, zellen t z → kern (kernVon z))
    (keineFuellung : ∀ id s ziele t z, spur s = some (id, .senden ziele) → s ≤ t → bereich z →
      zellen (t + 1) z → zellen t z)
    (handlerLeert : ∀ id k t z, spur t = some (id, .handler k) → bereich z → kernVon z = k →
      ¬ zellen (t + 1) z)
    {key : Id} {a : Nat} (release : spur a = some (key, .freigeben)) (z : Zelle) (bereichZ : bereich z) :
    ¬ zellen a z := by
  intro hz
  obtain ⟨s, ziele, sa, send, _, covered⟩ := protokoll.freigabe key a release
  have onCore := nurKerne a z hz
  have inZiele := protokoll.abdeckung key ziele s send (kernVon z) onCore
  obtain ⟨h, h', sh, hh', h'a, handler, _⟩ := covered (kernVon z) inZiele
  have gone := handlerLeert key (kernVon z) h z handler bereichZ rfl
  have persist : ∀ n, zellen (h + 1 + n) z → zellen (h + 1) z := by
    intro n
    induction n with
    | zero => exact fun x => x
    | succ n ih =>
      intro hn
      exact ih (keineFuellung key s ziele (h + 1 + n) z send (by omega) bereichZ hn)
  have ha : h + 1 ≤ a := by omega
  exact gone (persist (a - (h + 1)) (by rw [Nat.add_sub_of_le ha]; exact hz))

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

abbrev FlushSicht (Ort Wert Wahl Id : Type) :=
  EffektSicht Ort Wert Wahl (Id × FlushPhase)

/-- A multi-phase flush family supplies one step obligation per staged
    machine rule and proves the protocol from every actual ideal run. The
    decoder must be tied to those rules by the form's semantics proof. -/
def FlushSimAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (phase : F → Prop) {Id : Type} (sicht : FlushSicht Ort Wert Wahl Id) : Prop :=
  (∀ f, phase f → RegelSimulation E f) ∧
    ∀ (η : Lauf E), Laeufe E η →
      FlushProtokoll (fun t => sicht.lesen (η.zeit.spur t))
        (fun t => η.zeit.spur t = some (.absturz, absturzSpur))
        (fun k => k < η.umgebung.kernzahl)

private theorem absturzGleich
    {konkret ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (matched : SpurAbgleich konkret ideal) :
    (konkret = some (.absturz, absturzSpur)) ↔ (ideal = some (.absturz, absturzSpur)) := by
  cases matched with
  | pause => exact Iff.rfl
  | privat c w => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | schritt event => exact Iff.rfl

theorem FlushSimAussage.konkret {phase : F → Prop} {Id : Type}
    {sicht : FlushSicht Ort Wert Wahl Id} (pflicht : FlushSimAussage E phase sicht)
    {ρ : Maschine.Lauf E} {η : Lauf E} (valid : Laeufe E η) (matched : Laufabgleich ρ η) :
    FlushProtokoll (fun t => sicht.lesen (ρ.zeit.spur t))
      (fun t => ρ.zeit.spur t = some (.absturz, absturzSpur))
      (fun k => k < η.umgebung.kernzahl) := by
  have phases : (fun t => sicht.lesen (ρ.zeit.spur t)) =
      (fun t => sicht.lesen (η.zeit.spur t)) :=
    funext fun t => matched.effekte sicht t
  have crash : (fun t => ρ.zeit.spur t = some (.absturz, absturzSpur)) =
      (fun t => η.zeit.spur t = some (.absturz, absturzSpur)) := by
    exact funext fun t => propext (absturzGleich (matched.spur t))
  rw [phases, crash]
  exact pflicht.2 η valid

/-- The protocol is satisfiable: the four-phase run of the single core `0`, with no crash and with
    `kern` naming exactly that core, is a legal trace - including the coverage requirement. -/
theorem FlushProtokoll_erfuellbar :
    ∃ spur : Nat → Option (Nat × FlushPhase),
      spur 0 = some (0, .senden [0]) ∧
      spur 1 = some (0, .handler 0) ∧
      spur 2 = some (0, .bestaetigen 0) ∧
      spur 3 = some (0, .freigeben) ∧
      FlushProtokoll spur (fun _ => False) (fun k => k = 0) := by
  let spur : Nat → Option (Nat × FlushPhase) := fun t =>
    if t = 0 then some (0, .senden [0])
    else if t = 1 then some (0, .handler 0)
    else if t = 2 then some (0, .bestaetigen 0)
    else if t = 3 then some (0, .freigeben)
    else none
  have inv : ∀ t id phase, spur t = some (id, phase) →
      (t = 0 ∧ id = 0 ∧ phase = .senden [0]) ∨
      (t = 1 ∧ id = 0 ∧ phase = .handler 0) ∨
      (t = 2 ∧ id = 0 ∧ phase = .bestaetigen 0) ∨
      (t = 3 ∧ id = 0 ∧ phase = .freigeben) := by
    intro t id phase h
    by_cases t0 : t = 0
    · have e : spur t = some (0, FlushPhase.senden [0]) := by simp only [spur, if_pos t0]
      rw [e] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨t0, h.1.symm, h.2.symm⟩
    · by_cases t1 : t = 1
      · have e : spur t = some (0, FlushPhase.handler 0) := by
          simp only [spur, if_neg t0, if_pos t1]
        rw [e] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inr (Or.inl ⟨t1, h.1.symm, h.2.symm⟩)
      · by_cases t2 : t = 2
        · have e : spur t = some (0, FlushPhase.bestaetigen 0) := by
            simp only [spur, if_neg t0, if_neg t1, if_pos t2]
          rw [e] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact Or.inr (Or.inr (Or.inl ⟨t2, h.1.symm, h.2.symm⟩))
        · by_cases t3 : t = 3
          · have e : spur t = some (0, FlushPhase.freigeben) := by
              simp only [spur, if_neg t0, if_neg t1, if_neg t2, if_pos t3]
            rw [e] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact Or.inr (Or.inr (Or.inr ⟨t3, h.1.symm, h.2.symm⟩))
          · have e : spur t = none := by
              simp only [spur, if_neg t0, if_neg t1, if_neg t2, if_neg t3]
            rw [e] at h
            cases h
  let phasenIndex : FlushPhase → Nat := fun phase =>
    match phase with
    | .senden _ => 0
    | .handler _ => 1
    | .bestaetigen _ => 2
    | .freigeben => 3
  have posIndex : ∀ {t id phase}, spur t = some (id, phase) → t = phasenIndex phase := by
    intro t id phase h
    cases phase with
    | senden ziele =>
        rcases inv t id (.senden ziele) h with h0 | h0 | h0 | h0
        · exact h0.1
        · cases h0.2.2
        · cases h0.2.2
        · cases h0.2.2
    | handler k =>
        rcases inv t id (.handler k) h with h0 | h0 | h0 | h0
        · cases h0.2.2
        · exact h0.1
        · cases h0.2.2
        · cases h0.2.2
    | bestaetigen k =>
        rcases inv t id (.bestaetigen k) h with h0 | h0 | h0 | h0
        · cases h0.2.2
        · cases h0.2.2
        · exact h0.1
        · cases h0.2.2
    | freigeben =>
        rcases inv t id .freigeben h with h0 | h0 | h0 | h0
        · cases h0.2.2
        · cases h0.2.2
        · cases h0.2.2
        · exact h0.1
  refine ⟨spur, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro id phase t u ht hu
        have ht' := posIndex ht
        have hu' := posIndex hu
        omega
      · intro id xs ys t u ht hu
        have ht' := posIndex ht
        have hu' := posIndex hu
        change t = 0 at ht'
        change u = 0 at hu'
        omega
      · intro id k t ht
        rcases inv t id (.handler k) ht with h0 | h0 | h0 | h0
        · cases h0.2.2
        · have ht1 : t = 1 := h0.1
          have hid0 : id = 0 := h0.2.1
          have hkEq : (FlushPhase.handler k) = FlushPhase.handler 0 := h0.2.2
          cases hkEq
          subst t
          subst id
          refine ⟨0, [0], by omega, ?_, ?_, ?_⟩
          · rfl
          · simp only [List.mem_singleton]
          · intro u hus huu hcrash
            exact hcrash
        · cases h0.2.2
        · cases h0.2.2
      · intro id k t ht
        rcases inv t id (.bestaetigen k) ht with h0 | h0 | h0 | h0
        · cases h0.2.2
        · cases h0.2.2
        · have ht2 : t = 2 := h0.1
          have hid0 : id = 0 := h0.2.1
          have hkEq : (FlushPhase.bestaetigen k) = FlushPhase.bestaetigen 0 := h0.2.2
          cases hkEq
          subst t
          subst id
          refine ⟨1, by omega, ?_, ?_⟩
          · rfl
          · intro u hu1 hu2 hcrash
            exact hcrash
        · cases h0.2.2
      · intro id t ht
        rcases inv t id .freigeben ht with h0 | h0 | h0 | h0
        · cases h0.2.2
        · cases h0.2.2
        · cases h0.2.2
        · have ht3 : t = 3 := h0.1
          have hid0 : id = 0 := h0.2.1
          subst t
          subst id
          refine ⟨0, [0], by omega, ?_, ?_, ?_⟩
          · rfl
          · intro u hu0 hu3 hcrash
            exact hcrash
          · intro k hk
            simp only [List.mem_singleton] at hk
            subst k
            refine ⟨1, 2, by omega, by omega, by omega, ?_, ?_⟩
            · rfl
            · rfl
    · intro id ziele t ht
      rcases inv t id (.senden ziele) ht with h0 | h0 | h0 | h0
      · cases h0.2.2
        intro k hk
        simp only [List.mem_singleton]
        exact hk
      · cases h0.2.2
      · cases h0.2.2
      · cases h0.2.2

end Gabbro.Core.Maschine.I
