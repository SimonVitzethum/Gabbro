module

public import Core.Maschine.Start

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]

/-- A crash-free tick leaves the stack alone, pushes a frame, or pops one frame and
    installs its saved dispatch and NMI state. -/
private inductive StapelSchritt (vor nach : KernZustand Raum) : Prop where
  | bleibt (gleich : nach.stapel = vor.stapel)
  | eintritt (rahmen : Option Kontext × Bool) (stapel : nach.stapel = rahmen :: vor.stapel)
  | rueckkehr (rahmen : Option Kontext × Bool) (stapel : vor.stapel = rahmen :: nach.stapel)
      (kontext : nach.laeuft = rahmen.1) (nmi : nach.nmiAktiv = rahmen.2)

private theorem stapel_update_rueckkehr (kerne : Kern → KernZustand Raum) (k r : Kern) :
    StapelSchritt (kerne k) (Function.update kerne r (kerne r).zurueck k) := by
  by_cases gleich : k = r
  · subst r
    rw [Function.update_self]
    cases h : (kerne k).stapel with
    | nil => exact .bleibt (by simp only [KernZustand.zurueck, h])
    | cons rahmen rest =>
      cases rahmen with
      | mk c nmi =>
        apply StapelSchritt.rueckkehr (c, nmi) <;> simp only [KernZustand.zurueck, h]
  · rw [Function.update_of_ne gleich]
    exact .bleibt rfl

private theorem vollzug_stapel {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
    {t c s u plan spur s'} (vollzug : FuehrtSchrittAus e t c s u plan spur s') (k : Kern) :
    StapelSchritt (s.kerne k) (s'.kerne k) := by
  obtain ⟨rahmen, _, _, _, aktion, _, gleich⟩ := vollzug
  rw [gleich]
  have bleibt := congrArg (fun kerne : Kern → KernZustand Raum => (kerne k).stapel) rahmen.kerne
  generalize plan.aktion = auswahl at aktion
  generalize spur.aussen = ereignisse at aktion
  cases aktion with
  | @rueckkehr r _ _ _ =>
    change StapelSchritt (s.kerne k) (Function.update u.kerne r (u.kerne r).zurueck k)
    rw [rahmen.kerne]
    exact stapel_update_rueckkehr s.kerne k r
  | beende _ =>
    change StapelSchritt (s.kerne k) ((Abschlussrueckkehr s u c).kerne k)
    cases c with
    | faden _ => exact .bleibt bleibt
    | handler r _ _ | nmi r _ =>
      simp only [Abschlussrueckkehr]
      split
      · rw [rahmen.kerne]
        exact stapel_update_rueckkehr s.kerne k r
      · exact .bleibt bleibt
  | @wechsle r _ _ _ _ _ =>
    apply StapelSchritt.bleibt
    by_cases eq : k = r
    · subst r
      simpa only [Function.update_self] using bleibt
    · simpa only [Function.update_of_ne eq] using bleibt
  | maskiere _ _ | prioritaet _ =>
    apply StapelSchritt.bleibt
    dsimp only
    split <;> exact bleibt
  | _ => exact .bleibt bleibt

private theorem zustellt_stapel {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
    {hw t id s spur s'} (zustellt : UnterbrechungsSchritt e hw t id s spur s') (k : Kern) :
    StapelSchritt (s.kerne k) (s'.kerne k) := by
  obtain ⟨r, _, c, nmi, _, _, _, _, _, _, gleich⟩ := zustellt
  rw [gleich]
  change StapelSchritt (s.kerne k) (Function.update s.kerne r ((s.kerne r).unterbrechen c nmi) k)
  by_cases eq : k = r
  · subst r
    rw [Function.update_self]
    exact .eintritt ((s.kerne k).laeuft, (s.kerne k).nmiAktiv) rfl
  · rw [Function.update_of_ne eq]
    exact .bleibt rfl

variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι}

private theorem takt_stapel {ρ : Lauf E} {t k s} (vor : ρ.zeit.zustand t = some s)
    (keinAbsturz : ¬ AbsturzAngeboten E.katalog ρ.hw t) :
    ∃ s', ρ.zeit.zustand (t + 1) = some s' ∧ StapelSchritt (s.kerne k) (s'.kerne k) := by
  have takt := ρ.zeit.takt t
  rw [vor] at takt
  cases takt with
  | wartet _ gleich _ => exact ⟨s, gleich, .bleibt rfl⟩
  | schritt _ schritt =>
    cases zustand : ρ.zeit.zustand (t + 1) with
    | none => rw [zustand] at schritt; cases schritt
    | some s' =>
      rw [zustand] at schritt
      refine ⟨s', rfl, ?_⟩
      cases schritt with
      | schritt bewegt =>
        cases bewegt with
        | kontext _ _ _ vollzug => exact vollzug_stapel vollzug k
        | antwort _ ankunft =>
          obtain ⟨_, _, _, gleich⟩ := ankunft
          rw [gleich]
          exact .bleibt rfl
        | interrupt _ zustellt => exact zustellt_stapel zustellt k
        | absturz absturz => exact (keinAbsturz absturz.1).elim

private theorem StapelSchritt.rahmen {vor nach : KernZustand Raum} (schritt : StapelSchritt vor nach)
    {c : Kontext} {nmi : Bool} {rest : List (Option Kontext × Bool)}
    (gespeichert : ∃ oben, vor.stapel = oben ++ (some c, nmi) :: rest) :
    (∃ oben, nach.stapel = oben ++ (some c, nmi) :: rest) ∨
      (nach.laeuft = some c ∧ nach.nmiAktiv = nmi ∧ nach.stapel = rest) := by
  obtain ⟨oben, gleich⟩ := gespeichert
  cases schritt with
  | bleibt stapel => exact Or.inl ⟨oben, stapel.trans gleich⟩
  | eintritt rahmen stapel => exact Or.inl ⟨rahmen :: oben, stapel.trans (congrArg (List.cons rahmen) gleich)⟩
  | rueckkehr rahmen stapel kontext nmiZustand =>
    rw [gleich] at stapel
    cases oben with
    | nil =>
      obtain ⟨rfl, hrest⟩ := List.cons.inj stapel
      exact Or.inr ⟨kontext, nmiZustand, hrest.symm⟩
    | cons frame oben => exact Or.inl ⟨oben, (List.cons.inj stapel).2.symm⟩

public section

/-- In a crash-free interval, if the stack reaches a depth below a saved frame, a
    real terminal step has reinstated that frame on the same core. Arbitrarily many
    intervening deliveries and returns are allowed above it. -/
theorem Lauf.gespeicherter_kontext_kehrt_zurueck {ρ : Lauf E} {a b : Nat} {k : Kern}
    {s u : Zustand L Ort Wert Raum Lok Grund} {c : Kontext} {nmi : Bool}
    {rest : List (Option Kontext × Bool)}
    (von : ρ.zeit.zustand a = some s) (bis : ρ.zeit.zustand b = some u)
    (geordnet : a ≤ b) (crashfrei : ∀ t, a ≤ t → t < b → ¬ AbsturzAngeboten E.katalog ρ.hw t)
    (gespeichert : ∃ oben, (s.kerne k).stapel = oben ++ (some c, nmi) :: rest)
    (abgebaut : (u.kerne k).stapel.length ≤ rest.length) :
    ∃ t v, a < t ∧ t ≤ b ∧ ρ.zeit.zustand t = some v ∧ (v.kerne k).laeuft = some c ∧
      (v.kerne k).nmiAktiv = nmi ∧ (v.kerne k).stapel = rest := by
  let RueckkehrBis (ende : Nat) :=
    ∃ t v, a < t ∧ t ≤ ende ∧ ρ.zeit.zustand t = some v ∧ (v.kerne k).laeuft = some c ∧
      (v.kerne k).nmiAktiv = nmi ∧ (v.kerne k).stapel = rest
  have folge (n : Nat) (grenze : a + n ≤ b) :
      (∃ z, ρ.zeit.zustand (a + n) = some z ∧
        ∃ oben, (z.kerne k).stapel = oben ++ (some c, nmi) :: rest) ∨ RueckkehrBis (a + n) := by
    induction n with
    | zero => exact Or.inl ⟨s, von, gespeichert⟩
    | succ n ih =>
      have tick : a + n < a + (n + 1) := by omega
      rcases ih (tick.le.trans grenze) with ⟨z, hz, rahmen⟩ | ⟨t, v, ht, le, hv, restored⟩
      · obtain ⟨z', hz', schritt⟩ := takt_stapel (k := k) hz
          (crashfrei (a + n) (by omega) (tick.trans_le grenze))
        rcases schritt.rahmen rahmen with erhalten | restored
        · exact Or.inl ⟨z', hz', erhalten⟩
        · exact Or.inr ⟨a + (n + 1), z', by omega, Nat.le_refl _, hz', restored⟩
      · exact Or.inr ⟨t, v, ht, le.trans tick.le, hv, restored⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le geordnet
  rcases folge n (Nat.le_refl _) with ⟨z, hz, oben, gle⟩ | restored
  · have gleich : z = u := Option.some.inj (hz.symm.trans bis)
    subst z
    rw [gle, List.length_append, List.length_cons] at abgebaut
    omega
  · exact restored

/-- To discharge preemption return, it suffices that every occupied core receiving an
    interrupt later reaches its old stack depth during the same crash-free interval.
    An interrupt on another core leaves the dispatch in place at the next cut. -/
theorem Lauf.verdraengung_kehrt_zurueck_bei_abbau {ρ : Lauf E}
    (abbau : ∀ {t s k c id spur irq},
      ρ.zeit.zustand t = some s → (s.kerne k).laeuft = some c → s.status c = .laeuft →
      ρ.zeit.spur t = some (.interrupt id, spur) → spur.aussen = [.interrupt k irq .handler] →
      ∃ b u, t + 1 ≤ b ∧ ρ.zeit.zustand b = some u ∧
        (∀ i, t + 1 ≤ i → i < b → ¬ AbsturzAngeboten E.katalog ρ.hw i) ∧
        (u.kerne k).stapel.length ≤ (s.kerne k).stapel.length) :
    VerdraengungKehrtZurueck E ρ := by
  intro c k t ⟨s, vor, laeuft, aktiv⟩ ⟨id, spur, label⟩
  have takt := ρ.zeit.takt t
  rw [vor, label] at takt
  cases takt with
  | wartet h _ _ => cases h
  | schritt h schritt =>
    cases h
    cases next : ρ.zeit.zustand (t + 1) with
    | none => rw [next] at schritt; cases schritt
    | some s' =>
      rw [next] at schritt
      cases schritt with
      | schritt bewegt =>
        cases bewegt with
        | interrupt _ zustellt =>
          obtain ⟨r, irq, handler, nmi, _, _, _, _, ereignis, _, gleich⟩ := zustellt
          have kern : s'.kerne k = Function.update s.kerne r ((s.kerne r).unterbrechen handler nmi) k :=
            congrArg (fun z => z.kerne k) gleich
          by_cases hk : k = r
          · subst r
            rw [Function.update_self] at kern
            obtain ⟨b, u, ordnung, bis, crashfrei, kurz⟩ := abbau vor laeuft aktiv label ereignis
            have gespeichert : (s'.kerne k).stapel =
                [] ++ (some c, (s.kerne k).nmiAktiv) :: (s.kerne k).stapel := by
              simp only [kern, KernZustand.unterbrechen, laeuft, List.nil_append]
            obtain ⟨t', v, danach, _, hv, dispatch, _, _⟩ :=
              Lauf.gespeicherter_kontext_kehrt_zurueck (ρ := ρ)
                next bis ordnung crashfrei ⟨[], gespeichert⟩ kurz
            exact ⟨t', (Nat.lt_succ_self t).trans danach, k, v, hv, dispatch⟩
          · rw [Function.update_of_ne hk] at kern
            exact ⟨t + 1, Nat.lt_succ_self t, k, s', next,
              (congrArg KernZustand.laeuft kern).trans laeuft⟩

end

end Gabbro.Core.Maschine
