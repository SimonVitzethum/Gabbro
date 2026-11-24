module

public import Core.Verfeinerung.Fortschritt

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

private theorem fortschritt_aus_schrittfolge {ρ : Maschine.Lauf E} {η : Lauf E} {entry : Kontext}
    (fertig : ∀ s c, E.system.kopf s c = none → E.system.fertig s c)
    (regeln : ∀ f, Gabbro.Core.Ideal.RegelFortschritt E.system f)
    (komponierbar : ∀ f, RegelKomponierbar E.einrichtung E.system f)
    (slot : ∀ t, ∃ k, ((η.zeit.zustand t).kerne k).laeuft = some entry ∧ η.hw.gelegenheit t k)
    (dispatch : ∀ t k c, ((η.zeit.zustand t).kerne k).laeuft = some c → c = entry)
    (head : ∀ t, ∃ f, E.system.kopf (η.zeit.zustand t) entry = some f)
    (ticks : ∀ t, ∃ w spur, ρ.zeit.spur t = some (.kontext entry w, spur) ∧
      η.zeit.spur t = some (.kontext entry w, spur)) :
    FortschrittsPflichten (.lockFree (fun _ => True)) ρ η (fun _ c => c = entry) := by
  refine ⟨fertig, regeln, komponierbar, ?_, ?_, ?_, ?_⟩
  · rintro t _ rfl
    exact slot t
  · rintro t _ rfl _
    obtain ⟨w, spur, event, _⟩ := ticks t
    exact ⟨w, spur, event⟩
  · intro _ a c f opened _ _ _
    obtain ⟨k, running⟩ := opened.1
    cases dispatch a k c running
    obtain ⟨w, spur, _, event⟩ := ticks a
    exact ((opened.2 a (Nat.le_refl _)).2.2 (Or.inl ⟨w, spur, event⟩)).elim
  · intro _ a _ absent
    obtain ⟨f, form⟩ := head a
    obtain ⟨w, spur, _, event⟩ := ticks a
    exact (absent ⟨a, Nat.le_refl _, Or.inr ⟨entry, f, w, spur, trivial, form, event⟩⟩).elim

/-- A one-form unit repeatedly changes a local value on a fair hardware
    history. The concrete, simulation, safety and progress premises hold jointly. -/
theorem fortschritt_erfuellbar :
    ∃ E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit,
      SimPflichten E Eq (fun _ => 1) ∧
      ∃ (h : Umgebung) (ρ : Maschine.Lauf E) (η : Lauf E),
        Maschine.Laeufe E h ρ ∧ FairLaeufe E.katalog h ρ.hw ∧ Laeufe E η ∧
        Laufabgleich ρ η Eq ∧ Sim E ρ η ∧ (∀ k, ZielFX E h ρ k) ∧
        (∃ nutzbar, FortschrittsPflichten (.lockFree (fun _ => True)) ρ η nutzbar) ∧
        (∀ c, ¬ Haengt E ρ η c) ∧ FortschrittDerKlasse (.lockFree (fun _ => True)) η ∧
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
      fun _ _ => True, ⟨0, 1⟩, ⟨entry, 0, fun _ => daten 0, fun _ _ => ()⟩, fun _ => 0, fun _ _ _ => none⟩
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
  have frei {ρ : Maschine.Lauf E₀} {η : Lauf E₀} (matched : Laufabgleich ρ η Eq) (t : Nat) :
      η.belegt t = none := by
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
  have abgleich : AbgleichPflichten E₀ Eq (fun _ => 1) :=
    abgleich_aus_gleichen_regeln (fun _ _ _ _ => rfl) (fun _ _ _ _ _ _ => Iff.rfl)
      (fun _ _ _ _ matched => StotterSchranke.ohne_stottern (frei matched))
  have pflicht : SimPflichten E₀ Eq (fun _ => 1) := by
    refine ⟨abgleich, ?_, ?_⟩
    · intro _h _run _valid _t _s _next _c _w _spur _u _plan _load _after _label _normal _ready form _execute
      obtain ⟨_, _, planEq, _⟩ := form
      cases (List.cons.inj planEq).1
      exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
    · intro s i rel
      cases zustandsbezug_eq rel
      exact fun _ => ⟨rfl, Iff.rfl, fun _ => Iff.rfl⟩
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
  have execute (t : Nat) (c : Kontext) (x : Zustand Unit Unit Unit Unit Bool Unit) :
      FuehrtSchrittAus e t c x (update c x) plan label.2 (update c x) :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ hn => (List.not_mem_nil hn).elim,
      [], update c x, .intern, .nil _, rfl⟩
  let zustand (t : Nat) : Zustand Unit Unit Unit Unit Bool Unit :=
    Nat.rec z (fun _ => update entry) t
  have protocol (t : Nat) : (zustand t).kerne = z.kerne ∧ (zustand t).status = z.status := by
    induction t with
    | zero => exact ⟨rfl, rfl⟩
    | succ t ih => exact ih
  have dispatch : (z.kerne 0).laeuft = some entry := by
    change (if 0 = s.bootCore then some entry else none) = some entry
    rw [boot, ite_eq_left rfl]
  have live : z.status entry = .laeuft := by
    change (if entry = entry then Status.laeuft else Status.ruht) = (Status.laeuft : Status Unit Unit)
    exact ite_eq_left rfl
  have opportunity (t : Nat) : hw.gelegenheit t 0 := congrArg some (Nat.mod_one _)
  have step (t : Nat) : Lauffolge E₀ hw t (some (zustand t)) label (some (zustand (t + 1))) :=
    .schritt (.kontext rfl ⟨0, opportunity t,
      (congrArg (fun cores => (cores 0).laeuft) (protocol t).1).trans dispatch,
      (congrFun (protocol t).2 entry).trans live⟩ ⟨(), rfl, rfl, rfl⟩ (execute t entry (zustand t)))
  let ρ : Maschine.Lauf E₀ := ⟨s, hw, {
    zustand := fun t => some (zustand t)
    spur := fun _ => some label
    takt := fun t => .schritt rfl (step t) }⟩
  have konkret : Maschine.Laeufe E₀ h ρ := ⟨fair.hardware, fair.konform, admissible, rfl⟩
  obtain ⟨η, ideal, matched, env⟩ := laufabgleich abgleich konkret
  have sim := matched.sim ideal (abgleich.schranke h ρ η konkret matched)
    (pflicht.autoritaet h ρ konkret) pflicht.fortsetzung
  have idealState (t : Nat) : η.zeit.zustand t = zustand t := by
    obtain ⟨x, state, rel⟩ := matched.zustand t
    exact (zustandsbezug_eq rel).symm.trans ((Option.some.inj state).symm)
  have idealEvent (t : Nat) : η.zeit.spur t = some label := by
    have aligned : SpurAbgleich (some label) (η.zeit.spur t) := matched.spur t
    rcases aligned.ideales_etikett with event | step
    ·
      rcases (matched.frei t).mp (frei matched t) with no | yes
      · exact (Option.some_ne_none label no).elim
      · exact (yes event).elim
    · exact step
  have progress : FortschrittsPflichten (.lockFree (fun _ => True)) ρ η (fun _ c => c = entry) := by
    apply fortschritt_aus_schrittfolge
    · exact fun _ _ h => (Option.some_ne_none () h).elim
    · exact fun _ x c _ => Or.inl ⟨(), [plan], update c x, rfl, rfl⟩
    · intro f t x c w plans u _ _ rule
      obtain ⟨rfl, rfl⟩ := rule
      exact ⟨plan, label.2, update c x, rfl, execute t c x⟩
    · intro t
      rw [idealState t, (protocol t).1, matched.hardware]
      exact ⟨0, dispatch, opportunity t⟩
    · intro t j c running
      rw [idealState t, (protocol t).1] at running
      change (if j = s.bootCore then some entry else none) = some c at running
      split at running
      · exact (Option.some.inj running).symm
      · cases running
    · exact fun _ => ⟨(), rfl⟩
    · exact fun t => ⟨(), label.2, rfl, idealEvent t⟩
  have result := matched.fortschritt ideal (abgleich.schranke h ρ η konkret matched) progress (env.symm ▸ fair)
  refine ⟨E₀, pflicht, h, ρ, η, konkret, fair, ideal, matched, sim, pflicht.zielFX konkret,
    ⟨_, progress⟩, result.1, result.2, label, z, z', rfl, rfl, rfl, rfl, ?_⟩
  change Function.update z.lokal entry (!z.lokal entry) entry = true
  rw [Function.update_self]
  rfl

end Gabbro.Core.Maschine.I
