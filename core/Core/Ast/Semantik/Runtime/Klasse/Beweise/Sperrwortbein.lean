/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Sperrwortbein.lean
  Subject:   THE LOCK-WORD LEG OF EVERY EFFECT CLASS (MK-05 follow-up). `KlassenSperrwortbeinAussage` is
             proved for all effect classes: only the lock class has `beruehrtSperrwort = true`, and for it the
             step records exactly the lock events of the owner change at the lock word. Every label in a
             `Speicherfolge` carries the location of a label in its input list (a lazily materialised initial
             write copies the location of the access that triggers it). The lock plan reads and writes no cell
             and the lock protocol records no outside event, so the input list is `sperrEreignisse` at
             `einrichtung.sperrOrt l` and every recorded label sits at that location. The step adds no effect
             and leaves the ledger and the rights alone, so `neu = []` closes the release leg. All other
             classes close through the contradictory premise `beruehrtSperrwort = true`.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Sicherheit
public import Core.Sicherheit.KatalogSchritt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Sicherheit
open Gabbro.Core.Speicher (Etikett)

/-- Every label appended by an initialisation sits at the location of the access that triggers it. -/
private theorem initialisierung_ort_eq {Ort Wert : Type} {anfang : Ort → Wert} {l : Etikett Ort Wert}
    {g g₀ : SpeicherGraph Ort Wert} {init : List (SpeicherAkteur Ort × Etikett Ort Wert)}
    (h : Initialisierung anfang l g init g₀) :
    ∀ a l', (a, l') ∈ init → l'.ort = l.ort := by
  cases h with
  | ohne _ => intro a l' mem; cases mem
  | erste _ _ _ =>
      intro a l' mem
      simp only [List.mem_singleton, Prod.mk.injEq] at mem
      rcases mem with ⟨_, rfl⟩
      rfl

/-- Every label a `Speicherfolge` records sits at the location of some label in its input list. -/
private theorem speicherfolge_ort_eq_mem {Ort Wert : Type}
    {anfang : Ort → Wert} {f : SpeicherAkteur Ort} {g g' : SpeicherGraph Ort Wert}
    {ls : List (Etikett Ort Wert)} {es : List (SpeicherAkteur Ort × Etikett Ort Wert)}
    (h : Speicherfolge anfang f g ls es g') :
    ∀ a l, (a, l) ∈ es → ∃ l0 ∈ ls, l.ort = l0.ort := by
  induction h with
  | nil _ => intro a l mem; cases mem
  | cons vor hs nach ih =>
      rename_i g0 g1 g2 label rest init es
      intro a l mem
      rcases List.mem_append.mp mem with memInit | memRest
      · refine ⟨label, ?_, initialisierung_ort_eq vor a l memInit⟩
        simp only [List.mem_cons]
        exact Or.inl trivial
      · rcases List.mem_cons.mp memRest with eq | memEs
        · rcases eq with ⟨rfl, rfl⟩
          refine ⟨label, ?_, rfl⟩
          simp only [List.mem_cons]
          exact Or.inl trivial
        · obtain ⟨l0', hl0', hEq⟩ := ih a l memEs
          refine ⟨l0', ?_, hEq⟩
          simp only [List.mem_cons]
          exact Or.inr hl0'

/-- Every lock event sits at the lock's location. -/
private theorem sperrE_ort {Ort Wert : Type} (o o' : Option Kontext) (ort : Ort) (v : Wert) :
    ∀ l ∈ sperrE o o' ort v, l.ort = ort := by
  intro l mem
  cases o with
  | none =>
      cases o' with
      | none =>
          simp only [sperrE, List.not_mem_nil] at mem
      | some _d =>
          simp only [sperrE, List.mem_singleton] at mem
          subst l
          rfl
  | some c =>
      cases o' with
      | none =>
          simp only [sperrE, List.mem_singleton] at mem
          subst l
          rfl
      | some d =>
          by_cases h : c = d
          · simp only [sperrE, h, ↓reduceIte, List.not_mem_nil] at mem
          · simp only [sperrE, h, ↓reduceIte, List.mem_singleton] at mem
            subst l
            rfl

private theorem sperrEreignisse_ort {Ort Wert : Type} (s s' : SperrZustand) (ort : Ort) (v : Wert) :
    ∀ l ∈ sperrEreignisse s s' ort v, l.ort = ort := by
  intro l mem
  exact sperrE_ort s.besitzer s'.besitzer ort v l mem

/-- A lock action records the lock events at the lock word, no outside event, and changes only the lock
    table of the form-interior state. -/
private theorem fuehrtAus_sperre {L Ort Wert Raum Lok Grund Bedingung : Type} [DecidableEq L]
    {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung} {t : Nat} {c : Kontext}
    {z u : Maschine.Zustand L Ort Wert Raum Lok Grund} {b : SperrAktion}
    {sperren : List (Etikett Ort Wert)} {aussen : List Ereignis}
    {v : Maschine.Zustand L Ort Wert Raum Lok Grund} (l : L)
    (h : FuehrtAus e t c z u (.sperre l b) sperren aussen v) :
    ∃ next : SperrZustand,
      sperren = sperrEreignisse (z.sperren l) next (e.sperrOrt l) (z.initial (e.sperrOrt l)) ∧
      aussen = [] ∧ v = {u with sperren := Function.update z.sperren l next} := by
  cases h with
  | sperre _ _ => exact ⟨_, rfl, rfl, rfl⟩

/-- **The lock-word leg, for every effect class** (`KlassenSperrwortbeinAussage`). Only the lock class has a
     true premise; there the recorded labels are the lock events at the lock word, and the step adds no
     effect and no release. -/
theorem klassenSperrwortbein (k : Wirkungsklasse) : KlassenSperrwortbeinAussage k := by
  cases k with
  | lokal => intro h; change false = true at h; cases h
  | ruf => intro h; change false = true at h; cases h
  | lesen m => intro h; change false = true at h; cases h
  | schreiben m => intro h; change false = true at h; cases h
  | rmw m => intro h; change false = true at h; cases h
  | zaun m => intro h; change false = true at h; cases h
  | frage => intro h; change false = true at h; cases h
  | verbrauche => intro h; change false = true at h; cases h
  | starte => intro h; change false = true at h; cases h
  | beende => intro h; change false = true at h; cases h
  | verbinde => intro h; change false = true at h; cases h
  | wechsle => intro h; change false = true at h; cases h
  | maskiere => intro h; change false = true at h; cases h
  | prioritaet => intro h; change false = true at h; cases h
  | sendeUnterbrechung => intro h; change false = true at h; cases h
  | leiteLeitung => intro h; change false = true at h; cases h
  | sperre a =>
      intro _ ι E f F hkF emb hw t c w vor zwischen nach plan spur kopf impl aus
      have implIdeal : F.ideal c vor w [plan] zwischen := by
        change (F.regel).impl c vor w [plan] zwischen
        rw [← emb.regel]
        exact impl
      obtain ⟨kF, o, ue⟩ := F
      change kF = .sperre a at hkF
      subst kF
      simp only [Schrittform.ideal, Schrittform.zugriffsschritt, Wirkungsklasse.befugt] at implIdeal
      rcases implIdeal with ⟨nichtBefugt, _, _⟩ | ⟨_, v, _, same, after⟩
      · exact (nichtBefugt trivial).elim
      · let lLock := (o (vor.lokal c)).sperre
        have planEq : plan = (⟨.sperre a, o, ue⟩ : Schrittform).plan (vor.lokal c) v :=
          (List.cons.inj same).1
        have hAkt : plan.aktion = .sperre lLock a := by
          rw [planEq]
          simp only [Schrittform.plan, Wirkungsklasse.plan, lLock]
        have hLesen : plan.lesen = [] := by
          rw [planEq]
          simp only [Schrittform.plan, Wirkungsklasse.plan]
        have hFuss : plan.fuss = [] := by
          rw [planEq]
          simp only [Schrittform.plan, Wirkungsklasse.plan]
        obtain ⟨_, _, sperren, vState, aktionF, folge, zustand⟩ := aus
        rw [hAkt] at aktionF
        obtain ⟨next, sperrenEq, aussenNil, vStateEq⟩ :=
          fuehrtAus_sperre (e := E.maschine.einrichtung) (l := lLock) aktionF
        rcases spur with ⟨events, outside⟩
        change outside = [] at aussenNil
        rw [hLesen, hFuss, sperrenEq, aussenNil] at folge
        simp only [schreibEreignisse, List.filter_nil, List.map_nil, List.nil_append,
          List.append_nil] at folge
        refine ⟨?_, ?_⟩
        · intro i actor l recorded nichtAussen
          have mem : (actor, l) ∈ events := List.mem_of_getElem? recorded
          obtain ⟨l0, hl0, hEq⟩ := speicherfolge_ort_eq_mem folge actor l mem
          have hl0Ort : l0.ort = E.maschine.einrichtung.sperrOrt lLock := by
            simpa only [sperrEreignisse] using sperrEreignisse_ort
              (vor.sperren lLock) next (E.maschine.einrichtung.sperrOrt lLock)
              (vor.initial (E.maschine.einrichtung.sperrOrt lLock)) l0 hl0
          exact ⟨lLock, hEq.trans hl0Ort⟩
        · refine ⟨[], wirkungsloser_schritt ?_ ?_ ?_⟩
          · intro crash
            simp only [Absturz, aussenNil, List.not_mem_nil] at crash
          · rw [zustand, vStateEq, after]
            simp only [Schrittform.zugriffNach, Schrittform.buchungNach]
          · rw [zustand, vStateEq, after]
            simp only [Schrittform.zugriffNach, Schrittform.nach]

end Gabbro.Core.Ast.Semantik
