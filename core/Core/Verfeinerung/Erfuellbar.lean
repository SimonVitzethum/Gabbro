module

public import Core.Verfeinerung.Folgen

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

omit [DecidableEq L] in
private theorem zustandsbezug_eq {s i : Zustand L Ort Wert Raum Lok Grund}
    (rel : Zustandsbezug Eq s i) : s = i := by
  obtain ⟨shared, localEq⟩ := rel
  change { s with lokal := i.lokal } = i at shared
  rw [← localEq] at shared
  exact shared

/-- At a unit boundary with identical machine states, matching forward and
    backward form rules discharge the M4 obligations with no private steps. -/
theorem abgleich_aus_gleichen_regeln
    {laenge : F → Nat}
    (laden : ∀ h s, Hardware E.katalog h → E.ZulStart h s →
      E.laden s (h.lade E.bild) = some (start E s).2)
    (regeln : ∀ f c s w plans u, (E.system.regel f).impl c s w plans u ↔
      (E.system.regel f).ideal c s w plans u)
    (schranke : ∀ h ρ η, Maschine.Laeufe E h ρ → Laufabgleich ρ η Eq → StotterSchranke laenge η) :
    AbgleichPflichten E Eq laenge := by
  refine ⟨fun _ => rfl, fun h s hw zul => ⟨_, laden h s hw zul, ProtokollBezug.refl _, rfl⟩, ?_, ?_, schranke⟩
  · intro f hw t c w s u s' i plan spur rel normal bereit kopf impl execute
    have same := zustandsbezug_eq rel
    subst i
    exact Or.inl ⟨s', .kontext normal bereit ⟨f, kopf, (regeln f c s w [plan] u).mp impl⟩ execute,
      ProtokollBezug.refl _, rfl⟩
  · intro hw t s i rel stuck label next step
    have same := zustandsbezug_eq rel
    subst i
    cases step with
    | kontext normal ready rule execute =>
      obtain ⟨f, kopf, form⟩ := rule
      exact stuck _ _ (.schritt (.kontext normal ready ⟨f, kopf, (regeln _ _ _ _ _ _).mpr form⟩ execute))
    | antwort normal arrives => exact stuck _ _ (.schritt (.antwort normal arrives))
    | interrupt normal enters => exact stuck _ _ (.schritt (.interrupt normal enters))
    | absturz crash => exact stuck _ _ (.schritt (.absturz crash))

/-- A one-form unit changes a local value on a fair hardware history. Its loader,
    per-form simulation, and maximality obligations hold jointly. -/
theorem abgleich_erfuellbar :
    ∃ E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit,
      AbgleichPflichten E Eq (fun _ => 1) ∧
      ∃ (h : Umgebung) (ρ : Maschine.Lauf E) (η : Lauf E),
        Maschine.Laeufe E h ρ ∧ FairLaeufe E.katalog h ρ.hw ∧ Laeufe E η ∧
        Laufabgleich ρ η Eq ∧
        ∃ label before after, ρ.zeit.spur 0 = some label ∧
          ρ.zeit.zustand 0 = some before ∧ ρ.zeit.zustand 1 = some after ∧
          before.lokal (.faden 0) = false ∧ after.lokal (.faden 0) = true := by
  let k := Plattform.x86_64.katalog
  let bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩
  let entry := Kontext.faden 0
  let daten (kern : Nat) : Startdaten Unit Unit Bool Unit :=
    ⟨fun _ => false, fun c => if c = entry then .laeuft else .ruht,
      fun j => ⟨if j = kern then some entry else none, .nutzer, (), fun _ => false, 0, false, []⟩,
      ⟨fun _ => false, fun _ => 0⟩⟩
  let e : Einrichtung Unit Unit Unit Unit Bool Unit Unit :=
    ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False,
      fun _ _ => True, ⟨0, 1⟩, ⟨entry, 0, fun _ => daten 0, fun _ _ => ()⟩⟩
  let plan : SchrittPlan Unit Unit Unit Unit := ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩
  let update (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) :=
    { s with lokal := Function.update s.lokal c (!s.lokal c) }
  let impl c s (_ : Unit) plans u := plans = [plan] ∧ u = update c s
  let sy : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨fun _ => ⟨impl, impl⟩, fun _ _ => some (), fun _ _ => False, fun _ _ _ => False⟩
  let E₀ : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨k, bild, e, sy, fun s => daten s.bootCore, fun _ _ => 0,
      fun s _ =>
        let d := daten s.bootCore
        some (Zustand.start d.lokal d.status d.kerne d.rechte e.initial (.leer (fun _ => 0)))⟩
  have abgleich : AbgleichPflichten E₀ Eq (fun _ => 1) := by
    refine abgleich_aus_gleichen_regeln (fun _ _ _ _ => rfl) (fun _ _ _ _ _ _ => Iff.rfl) ?_
    intro _ ρ η _ matched
    apply StotterSchranke.ohne_stottern
    intro t
    cases occupied : η.belegt t with
    | none => rfl
    | some c =>
      obtain ⟨w, _, label, _⟩ := matched.belegt t c occupied
      have idle : η.zeit.spur t = none := by
        by_contra h
        rw [(matched.frei t).mpr (Or.inr h)] at occupied
        cases occupied
      obtain ⟨before, load, rel⟩ := matched.zustand t
      obtain ⟨after, loadedAfter, relAfter⟩ := matched.zustand (t + 1)
      have same := (zustandsbezug_eq relAfter).trans ((η.zeit.wartet idle).1.trans (zustandsbezug_eq rel).symm)
      have tick := ρ.zeit.takt t
      rw [load, loadedAfter, label, same] at tick
      cases tick with
      | wartet empty _ _ => cases empty
      | schritt chosen step =>
        cases Option.some.inj chosen
        cases step with
        | schritt step =>
          cases step with
          | kontext _ _ form exec =>
            obtain ⟨_, _, planEq, rfl⟩ := form
            cases (List.cons.inj planEq).1
            obtain ⟨_, _, _, _, action, _, state⟩ := exec
            cases action
            have impossible := congrArg (fun z : Zustand Unit Unit Unit Unit Bool Unit => z.lokal c) state
            change before.lokal c = Function.update before.lokal c (!before.lokal c) c at impossible
            rw [Function.update_self] at impossible
            have toggles (b : Bool) : b ≠ !b := by intro eq; cases b <;> cases eq
            exact (toggles _ impossible).elim
  let sicht : Nat → AussenVerlauf → AussenSicht :=
    fun _ _ => ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩
  let hw := Umgebung.referenzLauf k 1 sicht
  let h := Umgebung.referenz k 1 sicht
  have fair : FairLaeufe k h hw := Umgebung.referenz_fair k 1 sicht Plattform.x86_64.katalog_wohlgeformt
    (Nat.zero_lt_succ _)
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
      have h : a = 0 := List.mem_singleton.mp mem
      subst a
      exact ⟨0, rfl⟩
  obtain ⟨s, admissible⟩ := zulStart_erfuellbar fair.hardware image
  have boot : s.bootCore = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ admissible.2.1)
  let z := (start E₀ s).2
  let z' := update entry z
  let label : SchrittWahl Unit × SchrittSpur Unit Unit := (.kontext entry (), ⟨[], []⟩)
  have execute : FuehrtSchrittAus e 0 entry z z' plan label.2 z' :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ hn => (List.not_mem_nil hn).elim,
      [], z', .intern, .nil _, rfl⟩
  have first : Lauffolge E₀ hw 0 (some z) label (some z') := by
    refine .schritt (.kontext rfl ⟨0, rfl, ?_, ?_⟩ ⟨(), rfl, rfl, rfl⟩ execute)
    · change (if 0 = s.bootCore then some entry else none) = some entry
      rw [boot, ite_eq_left rfl]
    · change (if entry = entry then Status.laeuft else Status.ruht) = (Status.laeuft : Status Unit Unit)
      exact ite_eq_left rfl
  obtain ⟨tail, after⟩ := Zeitlauf.existiert (fun t => Lauffolge E₀ hw (t + 1)) (some z')
  let ρ : Maschine.Lauf E₀ := ⟨s, hw, {
    zustand := fun | 0 => some z | t + 1 => tail.zustand t
    spur := fun | 0 => some label | t + 1 => tail.spur t
    takt := fun
      | 0 => by
        apply Takt.schritt rfl
        change Lauffolge E₀ hw 0 (some z) label (tail.zustand 0)
        rw [after]
        exact first
      | t + 1 => by
        cases tail.takt t with
        | schritt mark step => exact .schritt mark step
        | wartet mark same stuck => exact .wartet mark same stuck }⟩
  have konkret : Maschine.Laeufe E₀ h ρ := ⟨fair.hardware, fair.konform, admissible, rfl⟩
  obtain ⟨η, ideal, matched⟩ := laufabgleich abgleich konkret
  refine ⟨E₀, abgleich, h, ρ, η, konkret, fair, ideal, matched, label, z, z', rfl, rfl, after, rfl, ?_⟩
  change Function.update z.lokal entry (!z.lokal entry) entry = true
  rw [Function.update_self]
  rfl

end Gabbro.Core.Maschine.I
