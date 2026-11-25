module

public import Core.Sicherheit.Grenzen

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
variable {H : Umgebung} {ρ : Lauf E}

private def SchnittSicher (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  InvariantenAmSchnitt E s ∧ RennenImGraph s.graph ∧ FragenVor t s ∧ OffeneFragenBefugt s

private theorem impl_sicher (grenzen : GrenzenSicher E)
    (regeln : ∀ f, RegelPflichten E f)
    (lauf : Maschine.Laeufe E.maschine H ρ)
    {t wspur vor nach}
    (h : ImplSchritt E.maschine.einrichtung E.maschine.system E.maschine.katalog ρ.hw t vor wspur nach)
    (vorher : SchnittSicher E t vor) :
    SchrittSicherheit E H ρ t vor nach wspur.2 ∧ SchnittSicher E (t + 1) nach := by
  have sicher : SchrittSicherheit E H ρ t vor nach wspur.2 ∧
      FragenVor (t + 1) nach ∧ OffeneFragenBefugt nach := by
    cases h with
    | kontext _ _ regel aus =>
      obtain ⟨f, kopf, impl⟩ := regel
      obtain ⟨schritt, antwort⟩ := regeln f
      exact ⟨schritt H ρ _ _ _ _ _ _ _ _ kopf impl aus, kontext_fragen_vor aus vorher.2.2.1,
        antwort _ _ _ _ _ _ _ _ kopf impl aus vorher.2.2.2⟩
    | antwort _ schritt =>
      exact antwort_sicher grenzen lauf.1 lauf.2.1.1 schritt vorher.2.2.1 vorher.2.2.2
    | interrupt _ schritt => exact interrupt_sicher grenzen schritt vorher.2.2.1 vorher.2.2.2
    | absturz schritt => exact absturz_sicher grenzen schritt vorher.2.2.1
  exact ⟨sicher.1, sicher.1.invarianten vorher.1, sicher.1.rennen vorher.2.1, sicher.2⟩

/-- The safety induction runs over hardware ticks. Pauses preserve the state, and the
    recorded label at an active tick selects its concrete rule or protocol transition. -/
theorem sicherheit_aus_regeln (grenzen : GrenzenSicher E) :
    (∀ f, RegelPflichten E f) → ∀ H ρ, Maschine.Laeufe E.maschine H ρ →
      Speichersicher E H ρ ∧ InvariantenErhalten E H ρ ∧ Rennfrei E H ρ ∧ ToctouFrei E H ρ := by
  intro regeln H ρ lauf
  have geladen {s} (anfang : ρ.zeit.zustand 0 = some s) :=
    grenzen.laden H ρ.start s lauf.1 lauf.2.2.1 (lauf.2.2.2.symm.trans anfang)
  have schnitte (t : Nat) : ∀ s, ρ.zeit.zustand t = some s → SchnittSicher E t s := by
    induction t with
    | zero =>
      intro s anfang
      obtain ⟨ereignisse, _, fragen, invariant⟩ := geladen anfang
      exact ⟨invariant, rennen_bei_leeren_ereignissen ereignisse, fragen_leer fragen⟩
    | succ t ih =>
      intro s nachher
      cases ρ.zeit.takt t with
      | wartet _label gleich _pause =>
        have vorher := ih s (gleich.symm.trans nachher)
        exact ⟨vorher.1, vorher.2.1, fun q mem => Nat.lt_succ_of_lt (vorher.2.2.1 q mem), vorher.2.2.2⟩
      | schritt _label step =>
        rw [nachher] at step
        cases vorher : ρ.zeit.zustand t with
        | none =>
          rw [vorher] at step
          cases step
        | some vor =>
          rw [vorher] at step
          cases step with
          | schritt h => exact (impl_sicher grenzen regeln lauf h (ih vor vorher)).2
  have uebergaenge (t vor spur nach) (h : Uebergang E ρ t vor spur nach) :
      SchrittSicherheit E H ρ t vor nach spur := by
    obtain ⟨vorher, ⟨w, label⟩, nachher⟩ := h
    have takt := ρ.zeit.takt t
    rw [vorher, label, nachher] at takt
    cases takt with
    | wartet impossible _ _ => cases impossible
    | schritt gleich step =>
      cases Option.some.inj gleich
      cases step with
      | schritt h => exact (impl_sicher grenzen regeln lauf h (schnitte t vor vorher)).1
  exact ⟨⟨fun _ h => ⟨(geladen h).1, (geladen h).2.1⟩, fun t vor spur nach h => (uebergaenge t vor spur nach h).speicher⟩,
    ⟨fun t s h => (schnitte t.val s h).1, fun t vor spur nach h => (uebergaenge t vor spur nach h).sperrwechsel⟩,
    ⟨fun t s h => (schnitte t.val s h).2.1, fun t vor spur nach h => (uebergaenge t vor spur nach h).register⟩,
    ⟨fun _ h => (geladen h).2.1, fun t vor spur nach h => (uebergaenge t vor spur nach h).toctou⟩⟩

private theorem aktion_sperrwechsel
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
    {t c vor zwischen a locks events nach l}
    (aktion : FuehrtAus e t c vor zwischen a locks events nach)
    (rahmen : Zustandsrahmen vor zwischen) (wechselt : (vor.sperren l).Wechsel (nach.sperren l)) :
    ∃ ops, a = .sperre l ops := by
  cases aktion with
  | @sperre ziel ops next _ _ =>
    by_cases gleich : l = ziel
    · subst l
      exact ⟨ops, rfl⟩
    · exact (wechselt (congrArg SperrZustand.besitzer (Function.update_of_ne gleich _ _)).symm).elim
  | intern | warte _ | frage _ | verbrauche _ | rueckkehr _ _ | starte _ | verbinde _ | beende _
    | wechsle _ _ _ _ =>
    exact (wechselt (congrArg SperrZustand.besitzer (congrFun rahmen.sperren l)).symm).elim

/-- Only a lock action can hand off or otherwise change an owner. The form needs to
    establish the final predicates only for the one lock selected by the action. A
    handler return restores a frame and needs no hand-off obligation. -/
theorem kontext_sperrwechsel {t c vor zwischen plan spur nach}
    (schritt : FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach)
    (amZiel : ∀ l ops, plan.aktion = .sperre l ops →
      (vor.sperren l).Wechsel (nach.sperren l) →
      E.maschine.einrichtung.invariant nach l ∧
        ∀ d ∈ E.invarianten, d.sperre = some l → d.gilt nach) :
    InvariantenBeimWechsel E vor nach := by
  obtain ⟨rahmen, _, _, v, aktion, _, zustand⟩ := schritt
  intro l wechselt
  have imRahmen : (vor.sperren l).Wechsel (v.sperren l) :=
    (congrArg (fun s => s.sperren l) zustand) ▸ wechselt
  obtain ⟨ops, amLock⟩ := aktion_sperrwechsel aktion rahmen imRahmen
  exact amZiel l ops amLock wechselt

end Gabbro.Core.Sicherheit
