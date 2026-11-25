/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Kosten.lean
  Subject:   THE COST ROW OF AN EFFECT CLASS, PROVED ONCE PER CLASS (MK-12,
             `KlassenKostenAussage`). Every ideal step of a class is one plan against the declared
             class cost (`kostenZeile`: one tick), and off the lock class every full step preserves
             every lock owner. One arm per class: the direct arms (`lokal`, `ruf`, the four
             interrupt-control classes) step the private plan; the access arms (`lesen`,
             `schreiben`, `rmw`, `zaun`, `frage`) refuse with the private plan or plan their class
             shape; the lifecycle arms (`starte`, `beende`, `verbinde`, `wechsle`) refuse or plan
             their protocol action; the consume class (`verbrauche`) steps the private plan like
             the frame-only classes; the lock arm (`sperre`) closes the hold leg vacuously through
             the contradictory `beruehrtSperrwort` premise. New constructors go at the END of
             `Wirkungsklasse`, with one arm each. `klassenKosten_erfuellbar` (the
             static rows hold jointly) and `klassenKosten_nichtTrivial` (a declared cost of zero is
             violated by a real step) accompany the statement.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- **Cost and hold, once per class** (`KlassenKostenAussage` over the static rows). -/
theorem klassenKosten (k : Wirkungsklasse) :
    KlassenKostenAussage Wirkungsklasse.kostenZeile k := by
  constructor
  · intro ι E f F hklasse hemb c s w plans u hideal
    obtain ⟨k', o, tr⟩ := F
    cases k' with
    | lokal =>
        rcases hideal with ⟨hp, _⟩
        rw [hp, Wirkungsklasse.kostenZeile_kosten]
        exact Nat.le_refl 1
    | ruf =>
        rcases hideal with ⟨hp, _⟩
        rw [hp, Wirkungsklasse.kostenZeile_kosten]
        exact Nat.le_refl 1
    | lesen _ =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, _, _, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | schreiben _ =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, _, _, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | rmw _ =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, _, _, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | zaun _ =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, _, _, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | sperre _ =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, _, _, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | frage =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, _, _, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | starte =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | beende =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | verbinde =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | wechsle =>
        rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
        · rw [hp, Wirkungsklasse.kostenZeile_kosten]
          exact Nat.le_refl 1
    | verbrauche =>
        rcases hideal with ⟨hp, _⟩
        rw [hp, Wirkungsklasse.kostenZeile_kosten]
        exact Nat.le_refl 1
    | maskiere =>
        rcases hideal with ⟨hp, _⟩
        rw [hp, Wirkungsklasse.kostenZeile_kosten]
        exact Nat.le_refl 1
    | prioritaet =>
        rcases hideal with ⟨hp, _⟩
        rw [hp, Wirkungsklasse.kostenZeile_kosten]
        exact Nat.le_refl 1
    | sendeUnterbrechung =>
        rcases hideal with ⟨hp, _⟩
        rw [hp, Wirkungsklasse.kostenZeile_kosten]
        exact Nat.le_refl 1
    | leiteLeitung =>
        rcases hideal with ⟨hp, _⟩
        rw [hp, Wirkungsklasse.kostenZeile_kosten]
        exact Nat.le_refl 1
  · intro hber
    cases k with
    | lokal =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .lokal hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .lokal := hklasse
        subst hk'
        rcases hideal with ⟨hp, _⟩
        have heq : plan.aktion = .intern := by
          have hplan : plan = Semantik.plan := (List.cons.inj hp).1
          subst hplan
          rfl
        exact FuehrtSchrittAus.sperren_erhalt haus (fun l a hsp => by rw [heq] at hsp; cases hsp) l
    | ruf =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .ruf hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .ruf := hklasse
        subst hk'
        rcases hideal with ⟨hp, _⟩
        have heq : plan.aktion = .intern := by
          have hplan : plan = Semantik.plan := (List.cons.inj hp).1
          subst hplan
          rfl
        exact FuehrtSchrittAus.sperren_erhalt haus (fun l a hsp => by rw [heq] at hsp; cases hsp) l
    | lesen m =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort (.lesen m) hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .lesen m := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, v, _, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.lesen m, o, tr⟩ (s.lokal c) v :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | schreiben m =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort (.schreiben m) hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .schreiben m := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, v, _, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.schreiben m, o, tr⟩ (s.lokal c) v :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | rmw m =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort (.rmw m) hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .rmw m := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, v, _, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.rmw m, o, tr⟩ (s.lokal c) v :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | zaun m =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort (.zaun m) hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .zaun m := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, v, _, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.zaun m, o, tr⟩ (s.lokal c) v :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | sperre a =>
        change true = false at hber
        cases hber
    | frage =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .frage hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .frage := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, v, _, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.frage, o, tr⟩ (s.lokal c) v :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            simp only [Schrittform.plan, Wirkungsklasse.plan, Operand.fragePlan] at hsp
            cases hq : (o (s.lokal c)).frage with
            | some _ =>
              rw [hq] at hsp
              cases hsp
            | none =>
              rw [hq] at hsp
              cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | starte =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .starte hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .starte := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.starte, o, tr⟩ (s.lokal c) 0 :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | beende =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .beende hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .beende := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.beende, o, tr⟩ (s.lokal c) 0 :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | verbinde =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .verbinde hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .verbinde := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.verbinde, o, tr⟩ (s.lokal c) 0 :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | wechsle =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .wechsle hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .wechsle := hklasse
        subst hk'
        have hne : ∀ (l : Nat) (a : SperrAktion), plan.aktion ≠ .sperre l a := by
          intro l a hsp
          rcases hideal with ⟨_, hp, _⟩ | ⟨_, hp, _⟩
          · have hplan : plan = Semantik.plan := (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
          · have hplan : plan = Schrittform.plan ⟨.wechsle, o, tr⟩ (s.lokal c) 0 :=
              (List.cons.inj hp).1
            rw [hplan] at hsp
            cases hsp
        exact FuehrtSchrittAus.sperren_erhalt haus hne l
    | verbrauche =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .verbrauche hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .verbrauche := hklasse
        subst hk'
        rcases hideal with ⟨hp, _⟩
        have heq : plan.aktion = .intern := by
          have hplan : plan = Semantik.plan := (List.cons.inj hp).1
          subst hplan
          rfl
        exact FuehrtSchrittAus.sperren_erhalt haus (fun l a hsp => by rw [heq] at hsp; cases hsp) l
    | maskiere =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .maskiere hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .maskiere := hklasse
        subst hk'
        rcases hideal with ⟨hp, _⟩
        have heq : plan.aktion = .intern := by
          have hplan : plan = Semantik.plan := (List.cons.inj hp).1
          subst hplan
          rfl
        exact FuehrtSchrittAus.sperren_erhalt haus (fun l a hsp => by rw [heq] at hsp; cases hsp) l
    | prioritaet =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .prioritaet hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .prioritaet := hklasse
        subst hk'
        rcases hideal with ⟨hp, _⟩
        have heq : plan.aktion = .intern := by
          have hplan : plan = Semantik.plan := (List.cons.inj hp).1
          subst hplan
          rfl
        exact FuehrtSchrittAus.sperren_erhalt haus (fun l a hsp => by rw [heq] at hsp; cases hsp) l
    | sendeUnterbrechung =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .sendeUnterbrechung hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .sendeUnterbrechung := hklasse
        subst hk'
        rcases hideal with ⟨hp, _⟩
        have heq : plan.aktion = .intern := by
          have hplan : plan = Semantik.plan := (List.cons.inj hp).1
          subst hplan
          rfl
        exact FuehrtSchrittAus.sperren_erhalt haus (fun l a hsp => by rw [heq] at hsp; cases hsp) l
    | leiteLeitung =>
        refine ⟨Wirkungsklasse.kostenZeile_halten_ohneSperrwort .leiteLeitung hber, ?_⟩
        intro ι E f F hklasse hemb t c s u w plan spur nach hideal haus l
        obtain ⟨k', o, tr⟩ := F
        have hk' : k' = .leiteLeitung := hklasse
        subst hk'
        rcases hideal with ⟨hp, _⟩
        have heq : plan.aktion = .intern := by
          have hplan : plan = Semantik.plan := (List.cons.inj hp).1
          subst hplan
          rfl
        exact FuehrtSchrittAus.sperren_erhalt haus (fun l a hsp => by rw [heq] at hsp; cases hsp) l

/-- Joint satisfiability of the cost statement: the static rows declare cost one, and the
    `lokal` class meets them. -/
theorem klassenKosten_erfuellbar :
    ∃ (z : Wirkungsklasse → KlassenKostenzeile) (k : Wirkungsklasse),
      (z k).kosten = 1 ∧ KlassenKostenAussage z k := by
  exact ⟨Wirkungsklasse.kostenZeile, .lokal, rfl, klassenKosten .lokal⟩

/-- Sharpness of the cost statement: a declared cost of zero is violated by a real step. The
    `lokal` form steps the private plan in the empty fragment's unit; its single plan costs one
    tick against the declared zero. -/
theorem klassenKosten_nichtTrivial :
    ∃ (z : Wirkungsklasse → KlassenKostenzeile) (k : Wirkungsklasse),
      (z k).kosten = 0 ∧ ¬ KlassenKostenAussage z k := by
  refine ⟨fun _ => ⟨0, none⟩, .lokal, rfl, ?_⟩
  intro aussage
  obtain ⟨kostenLeg, _⟩ := aussage
  have hemb : (⟨.lokal, fun _ => Operand.keiner, fun r _ _ => r⟩ : Schrittform).Eingebettet
      (Regeleinheit .x86_64
        (⟨.lokal, fun _ => Operand.keiner, fun r _ _ => r⟩ : Schrittform).regel) () :=
    ⟨rfl, rfl, rfl⟩
  have step : (⟨.lokal, fun _ => Operand.keiner, fun r _ _ => r⟩ : Schrittform).ideal
      eintritt Leerzustand () [Semantik.plan]
      (Schrittform.nach ⟨.lokal, fun _ => Operand.keiner, fun r _ _ => r⟩ eintritt Leerzustand 0) :=
    ⟨rfl, rfl⟩
  have bound := kostenLeg _ _ _ _ rfl hemb _ _ _ _ _ step
  have h10 : (1 : Nat) ≤ 0 := bound
  exact (by decide : ¬ ((1 : Nat) ≤ 0)) h10

end Gabbro.Core.Ast.Semantik
