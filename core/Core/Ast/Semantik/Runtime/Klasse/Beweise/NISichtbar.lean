/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/NISichtbar.lean
  Subject:   WHAT THE FLOW PREMISES OF THE NON-READING CLASSES ACTUALLY GIVE (MK-03). The public-state
             comparison is symmetric and transitive, and two steps of the SAME form from public-equal
             states end in public-equal states with the same plan view and the same public output.
             This is exactly the pinned step-level duty `KlassenSchrittNIAussage`, proved as
             `klassenSchrittNI`; no head premise is needed because both sides take the same form.

             The file also shows why the flow-rule premise is not vacuous: a form whose transfer copies
             a secret frame counter into the public projection, with the checker's flow rule removed,
             satisfies the other premises of the step statement and breaks its conclusion
             (`klassenSchrittNI_nichtTrivial`). The earlier run-level statement asked the same flow
             premises to determine the head of a second run, which they do not; that statement and its
             head countermodel are gone from the model.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung
open Gabbro.Core.Speicher (Modus)

/-! ### What follows from the flow premises -/

/-- The public state comparison is symmetric: every component is an equality of a projection. -/
theorem Beobachtung.QuellzustandGleich.symm
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {v u : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h : Beobachtung.QuellzustandGleich E v u) :
    Beobachtung.QuellzustandGleich E u v := by
  refine ⟨?_, ?_, ?_, h.2.2.2.1.symm, h.2.2.2.2.1.symm, ?_⟩
  · intro c p hp
    exact (h.1 c p hp).symm
  · intro c
    exact (h.2.1 c).symm
  · intro x
    exact (h.2.2.1 x).symm
  · intro c
    exact (h.2.2.2.2.2 c).symm

/-- The public state comparison is transitive. -/
theorem Beobachtung.QuellzustandGleich.trans
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {v u n : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h₁ : Beobachtung.QuellzustandGleich E v u) (h₂ : Beobachtung.QuellzustandGleich E u n) :
    Beobachtung.QuellzustandGleich E v n := by
  refine ⟨?_, ?_, ?_, h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1, ?_⟩
  · intro c p hp
    exact (h₁.1 c p hp).trans (h₂.1 c p hp)
  · intro c
    exact (h₁.2.1 c).trans (h₂.2.1 c)
  · intro x
    exact (h₁.2.2.1 x).trans (h₂.2.2.1 x)
  · intro c
    exact (h₁.2.2.2.2.2 c).trans (h₂.2.2.2.2.2 c)

/-- Visibility of a form's operands, specialised to two public-equal states at one context. -/
theorem Schrittform.operand_gleich {ι : Type} {E : Klasseneinheit ι} {F : Schrittform}
    (sicht : F.Operandensicht E) {c : Kontext} {v₁ v₂ : Zustand}
    (gleich : Beobachtung.QuellzustandGleich E v₁ v₂) :
    F.operand (v₁.lokal c) = F.operand (v₂.lokal c) :=
  sicht c v₁ v₂ gleich

/-- **Two steps of the same form from public-equal states stay public-equal.** This is the whole
    content of `RegelFluss` for a pair of steps: for a public control form the rule states the
    agreement directly; for a private control form each step preserves the public state and has an
    empty plan/output view, and symmetry plus transitivity complete the claim. -/
theorem Beobachtung.RegelFluss.schrittpaar_gleich
    {ι : Type} {E : Klasseneinheit ι} {f : ι} (fl : Beobachtung.RegelFluss E f)
    {c : Kontext} {v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂}
    (gleich : Beobachtung.QuellzustandGleich E v₁ v₂)
    (s₁ : Beobachtung.FormSchritt E f c v₁ w₁ p₁ u₁)
    (s₂ : Beobachtung.FormSchritt E f c v₂ w₂ p₂ u₂) :
    Beobachtung.QuellzustandGleich E u₁ u₂ ∧ PlanSicht E p₁ = PlanSicht E p₂ ∧
      AusgabeSicht E c v₁ u₁ = AusgabeSicht E c v₂ u₂ := by
  by_cases pub : oeffentlich (E.fluss.kontrolle f) = true
  · exact fl.2 pub c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ gleich s₁ s₂
  · have pubf : oeffentlich (E.fluss.kontrolle f) = false := by
      cases hb : oeffentlich (E.fluss.kontrolle f) <;> simp_all
    have o₁ := (fl.1 c v₁ w₁ p₁ u₁ s₁).2 pubf
    have o₂ := (fl.1 c v₂ w₂ p₂ u₂ s₂).2 pubf
    have hquel : Beobachtung.QuellzustandGleich E u₁ u₂ :=
      Beobachtung.QuellzustandGleich.trans (v := u₁) (u := v₁) (n := u₂)
        (Beobachtung.QuellzustandGleich.symm (v := v₁) (u := u₁) o₁.1)
        (Beobachtung.QuellzustandGleich.trans (v := v₁) (u := v₂) (n := u₂) gleich o₂.1)
    exact ⟨hquel, o₁.2.1.trans o₂.2.1.symm, o₁.2.2.trans o₂.2.2.symm⟩

/-! ### The step-level class duty follows from the flow rule alone -/

/-- **The step-level class duty holds for every class.** Both sides take the same form by
    hypothesis, so `RegelFluss.schrittpaar_gleich` applies directly: the countermodel's missing
    head premise (`kopf_nicht_offenbar`) is not needed at the step level. The `liest` restriction
    and the operand visibility stay as scope: for the reading classes the flow rule premise itself
    is what cannot hold without the label binding of the read value (MK-13). -/
theorem klassenSchrittNI (k : Wirkungsklasse) : KlassenSchrittNIAussage k := by
  intro ι E f F _ _ _ fl _sicht c v₁ v₂ w p₁ p₂ u₁ u₂ gleich s₁ s₂
  exact Beobachtung.RegelFluss.schrittpaar_gleich fl gleich s₁ s₂

/-! ### The missing premise: the head of the second run is not determined -/

/-- A secret compartment, as in the other flow countermodels. -/
def NISichtbar.geheim : Beobachtung.Etikett := {0}

theorem NISichtbar.geheim_verborgen : oeffentlich NISichtbar.geheim = false := by
  apply decide_eq_false
  intro eq
  have mem : 0 ∈ NISichtbar.geheim := Finset.mem_singleton_self _
  rw [eq] at mem
  exact Finset.notMem_empty _ mem

/-- All locations and control labels are secret in the countermodel. -/
def NISichtbar.etikettOrt (_ : Zelle) : Beobachtung.Etikett := NISichtbar.geheim
def NISichtbar.etikettBoot (_ : Nat) : Beobachtung.Etikett := NISichtbar.geheim
def NISichtbar.lokalEtikett (_ : Kontext) : Beobachtung.LokaleEtiketten Rahmen :=
  Beobachtung.LokaleEtiketten.ganz NISichtbar.geheim
def NISichtbar.kontrollEtikett (_ : Bool) : Beobachtung.Etikett := NISichtbar.geheim

/-- A writing form that names no particular cell. -/
def NISichtbar.schreibform (m : Modus) : Schrittform :=
  ⟨.schreiben m, fun _ => Operand.keiner, fun r _ _ => r⟩

/-- A unit embedding the writing form at `true`. Its head function reads the discarded-answer
    counter, which is NOT part of the public state comparison: two publicly equal states carry
    different forms, while the flow and visibility premises for `true` are satisfied. -/
def NISichtbar.einheit (m : Modus) : Klasseneinheit Bool :=
  let F := NISichtbar.schreibform m
  { katalog := (Plattform.x86_64).katalog,
    bild := bild,
    einrichtung := einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher,
    system := ⟨(fun _ => F.regel),
      (fun s _c => if s.verworfen eintritt = 0 then some true else some false),
      (fun _ _ => False), (fun _ _ _ => False)⟩,
    startdaten := fun start =>
      startdaten Fragment.leer.eingang Fragment.leer.eintritte (start.assignment 0) .x86_64 [],
    startmedium := startmedium,
    laden := laden Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher .x86_64,
    lokalerBezug := Eq,
    stotterLaenge := fun _ => 0,
    quelltabellen := Fragment.leer.tabellen,
    etiketten := { ort := NISichtbar.etikettOrt, bootByte := NISichtbar.etikettBoot },
    fluss := { lokal := NISichtbar.lokalEtikett, kontrolle := NISichtbar.kontrollEtikett } }

/-- A start whose bytes are absent; it only supplies a machine state to place frames in. -/
def NISichtbar.start : AussenStart :=
  ⟨0, fun _ => some 0, [], fun _ => none, .leer⟩

/-- The state of the unit with the hidden discarded-answer counter set to `b`. -/
def NISichtbar.zustand (m : Modus) (b : Nat) : Zustand :=
  let v := (I.start (NISichtbar.einheit m) NISichtbar.start).2
  { v with verworfen := fun _ => b }

/-- Changing the hidden counter preserves the public state. -/
theorem NISichtbar.quellzustand_gleich (m : Modus) :
    Beobachtung.QuellzustandGleich (NISichtbar.einheit m)
      (NISichtbar.zustand m 0) (NISichtbar.zustand m 1) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro c p hp
    rfl
  · intro c
    rfl
  · intro x
    rfl
  · intro c
    rfl

/-- A step that changes only local data preserves the public state in the countermodel. -/
theorem NISichtbar.quellzustand_nur_lokal (m : Modus) (v u : Zustand)
    (hstatus : u.status = v.status) (hinitial : u.initial = v.initial)
    (hrechte : u.rechte = v.rechte) (hleihen : u.leihen = v.leihen)
    (hantwort : ∀ c, AntwortSicht (NISichtbar.einheit m) u c =
      AntwortSicht (NISichtbar.einheit m) v c) :
    Beobachtung.QuellzustandGleich (NISichtbar.einheit m) v u := by
  refine ⟨?_, ?_, ?_, hrechte.symm, hleihen.symm, ?_⟩
  · intro c p hp
    exfalso
    have hp' : oeffentlich NISichtbar.geheim = true := by
      simpa only [NISichtbar.einheit, NISichtbar.lokalEtikett,
        Beobachtung.LokaleEtiketten.ganz] using hp
    exact Bool.false_ne_true (NISichtbar.geheim_verborgen.symm.trans hp')
  · intro c
    rw [hstatus]
  · intro x
    rw [hinitial]
  · intro c
    exact (hantwort c).symm

/-- The flow rule of the embedded form holds: the step changes only hidden local data, and every
    label it could release is secret. -/
theorem NISichtbar.regelFluss (m : Modus) :
    Beobachtung.RegelFluss (NISichtbar.einheit m) true := by
  constructor
  · intro c v w p u step
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rfl
      · intro id quelle val mem
        exact (List.not_mem_nil mem).elim
    · intro pubf
      have ide : (NISichtbar.schreibform m).ideal c v w [p] u := by
        simpa only [NISichtbar.einheit, Schrittform.regel] using step.2
      unfold Schrittform.ideal Schrittform.zugriffsschritt at ide
      rcases ide with ⟨_, peq, ueq⟩ | ⟨_, val, _, peq, ueq⟩
      · have pEq : p = Semantik.plan := (List.cons.inj peq).1
        subst p
        subst ueq
        refine ⟨?_, ?_, ?_⟩
        · exact NISichtbar.quellzustand_nur_lokal m v _ rfl rfl rfl rfl (fun _ => rfl)
        · rfl
        · rfl
      · have pEq : p = (NISichtbar.schreibform m).plan (v.lokal c) val := (List.cons.inj peq).1
        subst p
        subst ueq
        refine ⟨?_, ?_, ?_⟩
        · exact NISichtbar.quellzustand_nur_lokal m v _ rfl rfl rfl rfl (fun _ => rfl)
        · change Beobachtung.PlanSicht (NISichtbar.einheit m)
            (Wirkungsklasse.plan (.schreiben m) Operand.keiner val) = ([], [], none)
          simp only [Beobachtung.PlanSicht, NISichtbar.einheit, NISichtbar.etikettOrt,
            Wirkungsklasse.plan, Operand.keiner, List.filter_nil]
          simp only [NISichtbar.geheim_verborgen, Bool.and_false, Bool.false_eq_true,
            if_false, List.filterMap_cons, List.filterMap_nil, List.nil_append]
        · rfl
  · intro pub
    exfalso
    have pubf : oeffentlich ((NISichtbar.einheit m).fluss.kontrolle true) = false := by
      simp only [NISichtbar.einheit, NISichtbar.kontrollEtikett]
      exact NISichtbar.geheim_verborgen
    exact Bool.false_ne_true (pubf.symm.trans pub)

/-! ### The flow-rule premise is not vacuous -/

/-- A local label that projects only counter 0. Counter 1 is secret because it is not in the projection. -/
def NISichtbar.lokalEtikettLeak (_ : Kontext) : Beobachtung.LokaleEtiketten Rahmen :=
  ⟨1, fun _ => ∅, fun r _ => { r with zaehler := fun _ => r.zaehler 0 }⟩

/-- A frame whose public counter is `p` and whose secret counter is `s`. -/
def NISichtbar.leakRahmen (p s : Nat) : Rahmen :=
  { Rahmen.start [] with zaehler := fun n => match n with | 0 => some p | m + 1 => some s }

/-- A form whose transfer copies the secret counter into the public projection. Its operand is constant,
    so the address-visibility premise of the step statement still holds; it is the flow rule that is
    missing. -/
def NISichtbar.leakForm : Schrittform :=
  ⟨.lokal, fun _ => Operand.keiner,
    fun r _ _ => { r with zaehler := fun n => match n with | 0 => r.zaehler 1 | m + 1 => r.zaehler (m + 1) }⟩

/-- The unit embedding the leaking form: a secret control label, and the class rule with no flow
    discipline imposed. -/
def NISichtbar.leakEinheit : Klasseneinheit Bool :=
  let F := NISichtbar.leakForm
  { katalog := (Plattform.x86_64).katalog,
    bild := bild,
    einrichtung := einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher,
    system := ⟨(fun _ => F.regel), (fun _ _ => some true), (fun _ _ => False), (fun _ _ _ => False)⟩,
    startdaten := fun start =>
      startdaten Fragment.leer.eingang Fragment.leer.eintritte (start.assignment 0) .x86_64 [],
    startmedium := startmedium,
    laden := laden Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher .x86_64,
    lokalerBezug := Eq,
    stotterLaenge := fun _ => 0,
    quelltabellen := Fragment.leer.tabellen,
    etiketten := { ort := NISichtbar.etikettOrt, bootByte := NISichtbar.etikettBoot },
    fluss := { lokal := NISichtbar.lokalEtikettLeak, kontrolle := fun _ => NISichtbar.geheim } }

/-- The state of the leaking unit with public counter `p` and secret counter `s` in every context. -/
def NISichtbar.leakZustand (p s : Nat) : Zustand :=
  let v := (I.start NISichtbar.leakEinheit NISichtbar.start).2
  { v with lokal := fun _ => NISichtbar.leakRahmen p s }

/-- Changing only the secret counter preserves the public state. -/
theorem NISichtbar.leak_quellzustand_gleich (p s₁ s₂ : Nat) :
    Beobachtung.QuellzustandGleich NISichtbar.leakEinheit
      (NISichtbar.leakZustand p s₁) (NISichtbar.leakZustand p s₂) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro c i _
    simp only [NISichtbar.leakEinheit, NISichtbar.lokalEtikettLeak,
      Beobachtung.LokaleEtiketten.gleich, NISichtbar.leakZustand, NISichtbar.leakRahmen,
      oeffentlich]
  · intro c
    rfl
  · intro x
    rfl
  · intro c
    rfl

/-- The leaking form has a step at the entry context: its class is private, so the step has the private
    plan and the transfer that copies the secret counter. -/
theorem NISichtbar.leak_formschritt (p s : Nat) :
    Beobachtung.FormSchritt NISichtbar.leakEinheit true eintritt
      (NISichtbar.leakZustand p s) () Semantik.plan
      (NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand p s) 0) := by
  refine ⟨?_, ?_⟩
  · rfl
  · change NISichtbar.leakForm.ideal eintritt (NISichtbar.leakZustand p s) () [Semantik.plan]
      (NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand p s) 0)
    exact ⟨rfl, rfl⟩

/-- After the leaking step the public counter is the secret one, so source and successor are not
    publicly equal when the counters differ. -/
theorem NISichtbar.leak_nach_nicht_gleich (p s : Nat) (hne : p ≠ s) :
    ¬ Beobachtung.QuellzustandGleich NISichtbar.leakEinheit (NISichtbar.leakZustand p s)
        (NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand p s) 0) := by
  intro h
  have hp := h.1 eintritt (⟨0, by decide⟩ : Fin 1) (by rfl)
  have hz := congrArg (fun r : Rahmen => r.zaehler 0) hp
  simp only [NISichtbar.leakEinheit, NISichtbar.lokalEtikettLeak, NISichtbar.leakZustand,
    NISichtbar.leakRahmen, NISichtbar.leakForm, Schrittform.nach, Function.update, dif_pos] at hz
  exact hne (Option.some.inj hz)

/-- Two leaking steps from public-equal states end in states that are not publicly equal. -/
theorem NISichtbar.leak_zwei_nach_nicht_gleich (p s₁ s₂ : Nat) (hne : s₁ ≠ s₂) :
    ¬ Beobachtung.QuellzustandGleich NISichtbar.leakEinheit
      (NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand p s₁) 0)
      (NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand p s₂) 0) := by
  intro h
  have hp := h.1 eintritt (⟨0, by decide⟩ : Fin 1) (by rfl)
  have hz := congrArg (fun r : Rahmen => r.zaehler 0) hp
  simp only [NISichtbar.leakEinheit, NISichtbar.lokalEtikettLeak, NISichtbar.leakZustand,
    NISichtbar.leakRahmen, NISichtbar.leakForm, Schrittform.nach, Function.update, dif_pos] at hz
  exact hne (Option.some.inj hz)

/-- The checker's flow rule is missing: with a secret control label it would have to preserve the public
    source state, but the leaking step changes the public counter. -/
theorem NISichtbar.leak_kein_regelfluss :
    ¬ Beobachtung.RegelFluss NISichtbar.leakEinheit true := by
  intro h
  have hsecret : oeffentlich (NISichtbar.leakEinheit.fluss.kontrolle true) = false := by
    simpa only [NISichtbar.leakEinheit] using NISichtbar.geheim_verborgen
  have hp := h.1 eintritt (NISichtbar.leakZustand 7 0) () Semantik.plan
    (NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand 7 0) 0) (NISichtbar.leak_formschritt 7 0)
  exact NISichtbar.leak_nach_nicht_gleich 7 0 (by decide) (hp.2 hsecret).1

/-- **The step-level class duty is informative.** A non-reading form whose transfer leaks a secret
    counter into the public projection, in a unit without the checker's flow rule, keeps every other
    premise of `KlassenSchrittNIAussage` and breaks its conclusion: two steps of the same form from
    publicly equal states end in states that are not publicly equal. -/
theorem klassenSchrittNI_nichtTrivial :
    ∃ (E : Klasseneinheit Bool) (f : Bool) (F : Schrittform),
      F.klasse = .lokal ∧ F.klasse.liest = false ∧ F.Eingebettet E f ∧ F.Operandensicht E ∧
      ¬ Beobachtung.RegelFluss E f ∧
      ∃ (c : Kontext) (v₁ v₂ : Zustand) (w : PUnit) (p₁ p₂ : Plan) (u₁ u₂ : Zustand),
        Beobachtung.QuellzustandGleich E v₁ v₂ ∧
        Beobachtung.FormSchritt E f c v₁ w p₁ u₁ ∧
        Beobachtung.FormSchritt E f c v₂ w p₂ u₂ ∧
        ¬ Beobachtung.QuellzustandGleich E u₁ u₂ := by
  refine ⟨NISichtbar.leakEinheit, true, NISichtbar.leakForm, rfl, rfl, ?_, ?_,
    NISichtbar.leak_kein_regelfluss, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · intro c v₁ v₂ _
    rfl
  · refine ⟨eintritt, NISichtbar.leakZustand 7 0, NISichtbar.leakZustand 7 1, (),
      Semantik.plan, Semantik.plan,
      NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand 7 0) 0,
      NISichtbar.leakForm.nach eintritt (NISichtbar.leakZustand 7 1) 0, ?_, ?_, ?_, ?_⟩
    · exact NISichtbar.leak_quellzustand_gleich 7 0 1
    · exact NISichtbar.leak_formschritt 7 0
    · exact NISichtbar.leak_formschritt 7 1
    · exact NISichtbar.leak_zwei_nach_nicht_gleich 7 0 1 (by decide)

end Gabbro.Core.Ast.Semantik
