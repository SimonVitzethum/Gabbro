module

public import Core.Verfeinerung.Abnahme.Effekte
public import Core.Verfeinerung.Formpflichten
public import Core.Katalog.Erfuellbar

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

abbrev FlushSicht (Ort Wert Wahl Id : Type) :=
  EffektSicht Ort Wert Wahl (Id × FlushPhase)

/-- A flush family declares its staged-rule set, its event type and the decoder of actual steps as
    data of the family's unit wrapper. None of them is chosen by the proof of the duty, so an empty
    decoder can no longer satisfy the statement for every unit. -/
structure FlushBindung (Ort Wert Wahl F : Type) where
  Id : Type
  mitglied : F → Prop
  sicht : FlushSicht Ort Wert Wahl Id

/-- The subject of the family duty: a unit together with its declared flush binding. -/
structure FlushEinheit (L Ort Wert Raum Lok Grund Bedingung Wahl F : Type) [DecidableEq L] where
  einheit : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F
  bindung : FlushBindung Ort Wert Wahl F

/-- Every declared staged rule is simulated, and every actual ideal run of the declared unit
    decodes to a shootdown protocol trace. -/
def FlushFamilienAussage (U : FlushEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F) : Prop :=
  (∀ f, U.bindung.mitglied f → RegelSimulation U.einheit f) ∧
    ∀ η : Lauf U.einheit, Laeufe U.einheit η →
      FlushProtokoll (fun t => U.bindung.sicht.lesen (η.zeit.spur t))
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

theorem FlushFamilienAussage.konkret (U : FlushEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (pflicht : FlushFamilienAussage U)
    {ρ : Maschine.Lauf U.einheit} {η : Lauf U.einheit} (valid : Laeufe U.einheit η)
    (matched : Laufabgleich ρ η) :
    FlushProtokoll (fun t => U.bindung.sicht.lesen (ρ.zeit.spur t))
      (fun t => ρ.zeit.spur t = some (.absturz, absturzSpur))
      (fun k => k < η.umgebung.kernzahl) := by
  have phases : (fun t => U.bindung.sicht.lesen (ρ.zeit.spur t)) =
      (fun t => U.bindung.sicht.lesen (η.zeit.spur t)) :=
    funext fun t => matched.effekte U.bindung.sicht t
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

/-- The duty is satisfiable by a runnable unit: the empty member set discharges the step
    obligations and a decoder that emits no event makes every ideal run a legal trace. -/
theorem FlushFamilienAussage_erfuellbar :
    ∃ U : FlushEinheit Unit Unit Unit Unit Bool Unit Unit Unit Unit,
      FlushFamilienAussage U ∧ ∃ η : Lauf U.einheit, Laeufe U.einheit η := by
  let k := Plattform.x86_64.katalog
  let bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩
  let entry := Kontext.faden 0
  let daten (kern : Nat) : Startdaten Unit Unit Bool Unit :=
    ⟨fun _ => false, fun c => if c = entry then .laeuft else .ruht,
      fun j => ⟨if j = kern then some entry else none, .nutzer, (), fun _ => false, 0, false, []⟩,
      ⟨fun _ => false, fun _ => 0⟩⟩
  let e : Einrichtung Unit Unit Unit Unit Bool Unit Unit :=
    ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False,
      fun _ _ => True, ⟨0, 1⟩, ⟨entry, 0, fun _ => daten 0, fun _ _ => ()⟩, fun _ => 0, fun _ _ _ => none⟩
  let plan : SchrittPlan Unit Unit Unit Unit := ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩
  let update (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) :=
    { s with lokal := Function.update s.lokal c (!s.lokal c) }
  let impl (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (_ : Unit) plans u :=
    plans = [plan] ∧ u = update c s
  let sy : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨fun _ => ⟨impl, impl⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩
  let E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨k, bild, e, sy, fun s => daten s.bootCore, fun _ _ => 0,
      (fun s _ =>
        let d := daten s.bootCore
        some (Zustand.start d.lokal d.status d.kerne d.rechte e.initial (.leer (fun _ => 0)))),
      Eq, (fun _ => 1), .leer, eineTabelle, .leer, .leer, .leer⟩
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ =>
    ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩
  let h := Umgebung.referenz k 1 sicht
  let hw := Umgebung.referenzLauf k 1 sicht
  have fair : FairLaeufe k h hw := Umgebung.referenz_fair k 1 sicht
    Plattform.x86_64.katalog_wohlgeformt (Nat.zero_lt_succ _)
  have image : bild.gueltig k.plattform.ziel := by
    refine ⟨List.Mem.head _, ?_, ?_⟩
    · intro a byte present
      change (if a = 0 then some 0 else none) = some byte at present
      split at present
      · rename_i atZero
        subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases present
    · intro a mem
      have ha : a = 0 := List.mem_singleton.mp mem
      subst a
      exact ⟨0, rfl⟩
  obtain ⟨s, admissible⟩ := zulStart_erfuellbar fair.hardware image
  obtain ⟨η, valid, _, _⟩ := I.lauf_mit_hw E fair.hardware admissible fair.konform
  let U : FlushEinheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨E, ⟨Nat, fun _ => False, { lesen := fun _ => none, leer := rfl, privat := fun _ _ => rfl }⟩⟩
  refine ⟨U, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro f member
      cases member
    · intro ξ _
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro id phase t u ht
        change none = some (id, phase) at ht
        cases ht
      · intro id xs ys t u ht
        change none = some (id, FlushPhase.senden xs) at ht
        cases ht
      · intro id kk t ht
        change none = some (id, FlushPhase.handler kk) at ht
        cases ht
      · intro id kk t ht
        change none = some (id, FlushPhase.bestaetigen kk) at ht
        cases ht
      · intro id t ht
        change none = some (id, FlushPhase.freigeben) at ht
        cases ht
      · intro id ziele t ht
        change none = some (id, FlushPhase.senden ziele) at ht
        cases ht
  · exact ⟨η, valid⟩

/-- The duty is sharp: a runnable unit whose ideal run crashes at the first cut and a decoder that
    reads a crash as a release fail the chain, because no send precedes that release. -/
theorem FlushFamilienAussage_nichtTrivial :
    ∃ U : FlushEinheit Unit Unit Unit Unit Bool Unit Unit Unit Unit,
      ¬ FlushFamilienAussage U := by
  let k := Plattform.x86_64.katalog
  let bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩
  let entry := Kontext.faden 0
  let daten (kern : Nat) : Startdaten Unit Unit Bool Unit :=
    ⟨fun _ => false, fun c => if c = entry then .laeuft else .ruht,
      fun j => ⟨if j = kern then some entry else none, .nutzer, (), fun _ => false, 0, false, []⟩,
      ⟨fun _ => false, fun _ => 0⟩⟩
  let e : Einrichtung Unit Unit Unit Unit Bool Unit Unit :=
    ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False,
      fun _ _ => True, ⟨0, 1⟩, ⟨entry, 0, fun _ => daten 0, fun _ _ => ()⟩, fun _ => 0, fun _ _ _ => none⟩
  let plan : SchrittPlan Unit Unit Unit Unit := ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩
  let update (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) :=
    { s with lokal := Function.update s.lokal c (!s.lokal c) }
  let impl (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (_ : Unit) plans u :=
    plans = [plan] ∧ u = update c s
  let sy : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨fun _ => ⟨impl, impl⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩
  let E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨k, bild, e, sy, fun s => daten s.bootCore, fun _ _ => 0,
      (fun s _ =>
        let d := daten s.bootCore
        some (Zustand.start d.lokal d.status d.kerne d.rechte e.initial (.leer (fun _ => 0)))),
      Eq, (fun _ => 1), .leer, eineTabelle, .leer, .leer, .leer⟩
  let sicht : Nat → AussenVerlauf → AussenSicht := fun _ _ =>
    ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩
  let h := Umgebung.referenz k 1 sicht
  let hw := Umgebung.referenzLauf k 1 sicht
  have fair : FairLaeufe k h hw := Umgebung.referenz_fair k 1 sicht
    Plattform.x86_64.katalog_wohlgeformt (Nat.zero_lt_succ _)
  have image : bild.gueltig k.plattform.ziel := by
    refine ⟨List.Mem.head _, ?_, ?_⟩
    · intro a byte present
      change (if a = 0 then some 0 else none) = some byte at present
      split at present
      · rename_i atZero
        subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases present
    · intro a mem
      have ha : a = 0 := List.mem_singleton.mp mem
      subst a
      exact ⟨0, rfl⟩
  obtain ⟨s, admissible⟩ := zulStart_erfuellbar fair.hardware image
  have persistence : E.katalog.enthaelt .persistence := by
    change .persistence ∈ (ZielZeilen ++ .persistence :: _ : List Zeile)
    exact List.mem_append.mpr (Or.inr (List.Mem.head _))
  obtain ⟨_, η, _, valid, _, _, _, _, _, crash0⟩ :=
    absturz_laeufe_erfuellbar (E := E) admissible fair persistence rfl
  let decoder : EffektSicht Unit Unit Unit (Nat × FlushPhase) :=
    { lesen := fun
        | none => none
        | some (.absturz, _) => some ((0 : Nat), FlushPhase.freigeben)
        | some _ => none
      leer := rfl
      privat := by intro c w; rfl }
  let U : FlushEinheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨E, ⟨Nat, fun _ => False, decoder⟩⟩
  refine ⟨U, ?_⟩
  intro dies
  have release : U.bindung.sicht.lesen (η.zeit.spur 0) = some ((0 : Nat), FlushPhase.freigeben) := by
    change decoder.lesen (η.zeit.spur 0) = some ((0 : Nat), FlushPhase.freigeben)
    rw [crash0]
  obtain ⟨_, _, before, _, _, _⟩ := (dies.2 η valid).freigabe 0 0 release
  omega

end Gabbro.Core.Maschine.I
