/-
  File:      core/Core/Ziel/Korrektheit/Waechter/WaechterRahmen.lean
  Subject:   FRAME INVARIANT for the guard analysis over ideal runs.

  For a fragment whose code the static check never refuses for foreign access
  (`keinFremdzugriff`), every context frame satisfies the joined environments at
  every cut of every ideal run, and every lock is free at every cut.

  The induction is over time. Pauses keep the state. Answers and interrupt entries
  touch only ledgers, cores and statuses, never frames or locks. A crash resets to
  entry frames with no temporaries. A context step goes through the frame transfer
  of its head: frame-only heads through `auswerten_erfuellt`, refused questions
  through a halt, granted questions and consumptions through the identity transfer
  of the outside forms, whose answer slots the analysis poisons. Lock steps cannot
  occur: they need access instructions, which the analysis refuses. Call entries
  inside `auswerten_erfuellt` go through `eintrittArgumente_erfuellt`.

  Nothing here speaks about a checker; the abstraction over the checker verdict is
  `WaechterAbstrakt.lean`.
-/
module

public import Core.Ziel.Korrektheit.Waechter.WaechterErhalt
public import Core.Maschine.Start
public import Core.Maschine.Schritte
public import Core.Maschine.Unterbrechung
public import Core.Maschine.Absturz
public import Core.Maschine.Aussen
public import Core.Ast.Semantik.Runtime.Regeln
public import Core.Ast.Semantik.Runtime.Mehrkontext.System
public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast
open Gabbro.Core.Maschine
open Gabbro.Core.Aussenfrage
open Gabbro.Core.Katalog
open Gabbro.Core.Speicher
open Classical

/-- A frame with no temporaries and no saved continuations satisfies every joined
    environment: every lookup obligation is vacuous. -/
theorem rahmenLeer_erfuellt (code : List Befehl) (frame : Rahmen)
    (htemp : frame.temp = fun _ => none) (hfort : frame.fortsetzungen = []) :
    RahmenErfuellt code frame := by
  have hslot : ∀ slot, frame.temp slot = none := fun slot => by rw [htemp]
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    have hs := hslot slot
    simp only [hs, Option.bind_none] at hg
    cases hg
  · intro slot l hh hlook d hd cap t hdt
    have hs := hslot slot
    simp only [hs] at hd
    cases hd
  · intro k hk
    rw [hfort] at hk
    exact (List.not_mem_nil hk).elim

/-- The boot frame of every context satisfies every joined environment. -/
theorem bootRahmen_erfuellt (code : List Befehl) (scope : Scope)
    (eintritte : Kontext → Option Nat) (kern : Option Nat) (platform : Plattform)
    (regions : List Strecke) (c : Kontext) :
    RahmenErfuellt code ((startdaten scope eintritte kern platform regions).lokal c) := by
  apply rahmenLeer_erfuellt
  · rfl
  · rfl

/-- The ideal start cut carries empty frames on every context. -/
theorem startRahmen_erfuellt (p : Fragment) (platform : Plattform)
    (s : AussenStart) (c : Kontext) :
    RahmenErfuellt p.code (((Maschine.I.start (p.einheit platform) s).2).lokal c) := by
  have h : (((Maschine.I.start (p.einheit platform) s).2).lokal c) =
      ((startdaten p.eingang p.eintritte (s.assignment 0) platform s.regions).lokal c) := rfl
  rw [h]
  exact bootRahmen_erfuellt p.code p.eingang p.eintritte (s.assignment 0) platform s.regions c

/-- A crash reset carries empty frames: the declared clearing is the identity on entry data. -/
theorem absturzRahmen_erfuellt (p : Fragment) (platform : Plattform)
    (s : Ast.Semantik.Zustand) (t : Nat) (per : PersistZustand) (c : Kontext) :
    RahmenErfuellt p.code
      (((Maschine.Zustand.wiederanlauf s
        (p.einheit platform).einrichtung.wiederanlauf t per).lokal) c) := by
  have h : (((Maschine.Zustand.wiederanlauf s
      (p.einheit platform).einrichtung.wiederanlauf t per).lokal) c) =
      ((startdaten p.eingang p.eintritte (some 0)).lokal c) := rfl
  rw [h]
  exact bootRahmen_erfuellt p.code p.eingang p.eintritte (some 0) _ _ c

/-- The ideal start cut holds no lock. -/
theorem startSperren_frei (p : Fragment) (platform : Plattform)
    (s : AussenStart) (l : Nat) :
    (((((Maschine.I.start (p.einheit platform) s).2).sperren) l).besitzer) = none := rfl

/-- A crash reset holds no lock. -/
theorem absturzSperren_frei (p : Fragment) (platform : Plattform)
    (s : Ast.Semantik.Zustand) (t : Nat) (per : PersistZustand) (l : Nat) :
    ((((Maschine.Zustand.wiederanlauf s
      (p.einheit platform).einrichtung.wiederanlauf t per).sperren) l).besitzer) = none := rfl

/-- An outside form transfers its frame by advancing it: the evaluation at the
    instruction boundary keeps temporaries and continuations. -/
theorem aussenUebertrag_weiter (r : Rahmen) (live : Nat → Bool) (v : Int)
    (f : Aussenfrageform) :
    (Befehl.aussen f).form.uebertrag r live v = r.weiter := rfl

/-- Advancing a frame preserves the joined environments: only the position changes. -/
theorem weiter_erfuellt (code : List Befehl) (frame : Rahmen)
    (h : RahmenErfuellt code frame) :
    RahmenErfuellt code frame.weiter := by
  have htemp : frame.weiter.temp = frame.temp := rfl
  have hfort : frame.weiter.fortsetzungen = frame.fortsetzungen := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro slot lo hi hlook g hg
    rw [htemp] at hg
    exact h.1 slot lo hi hlook g hg
  · intro slot l hh hlook d hd cap t hdt
    rw [htemp] at hd
    exact h.2.1 slot l hh hlook d hd cap t hdt
  · intro k hk
    rw [hfort] at hk
    exact h.2.2 k hk

/-- Writing an unknown value to a poisoned slot preserves the joined environments:
    the poisoned lookup is vacuous and every other slot is untouched. -/
theorem schreibePoison_erfuellt (code : List Befehl) (frame : Rahmen) (slot : Nat)
    (V : Option Dynamisch) (h : RahmenErfuellt code frame)
    (hI : umgebungInt code slot = none) (hT : umgebungText code slot = none) :
    RahmenErfuellt code (frame.schreibe slot V) := by
  have htemp : (frame.schreibe slot V).temp = Function.update frame.temp slot V := rfl
  have hfort : (frame.schreibe slot V).fortsetzungen = frame.fortsetzungen := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro s2 lo hi hlook g hg
    rw [htemp] at hg
    by_cases heq : s2 = slot
    · subst heq
      simp only [Function.update_self] at hg
      rw [hI] at hlook
      cases hlook
    · rw [Function.update_of_ne heq] at hg
      exact h.1 s2 lo hi hlook g hg
  · intro s2 l hh hlook d hd cap t hdt
    rw [htemp] at hd
    by_cases heq : s2 = slot
    · subst heq
      simp only [Function.update_self] at hd
      rw [hT] at hlook
      cases hlook
    · rw [Function.update_of_ne heq] at hd
      exact h.2.1 s2 l hh hlook d hd cap t hdt
  · intro k hk
    rw [hfort] at hk
    exact h.2.2 k hk

/-- The common epilogue of a context step whose plan is internal: the frame transfer
    already preserves the invariant and the protocol step touches neither frames nor locks. -/
theorem kontextEpilog (p : Fragment) (platform : Plattform)
    (s u : Ast.Semantik.Zustand) (c : Kontext) (t : Nat)
    (plan : Plan) (sperren : List (Etikett Zelle Int)) (aussen : List Ereignis)
    (v s' : Ast.Semantik.Zustand)
    (huF : ∀ c', RahmenErfuellt p.code (u.lokal c'))
    (huS : u.sperren = s.sperren)
    (hs : ∀ l, (((s.sperren) l).besitzer) = none)
    (hplan : plan.aktion = .intern)
    (hfa : FuehrtAus (p.einheit platform).einrichtung t c s u plan.aktion sperren aussen v)
    (heq : s' = { v with graph := s'.graph }) :
    (∀ c', RahmenErfuellt p.code ((s'.lokal) c')) ∧
      (∀ l, (((s'.sperren) l).besitzer) = none) := by
  rw [hplan] at hfa
  cases hfa with
  | intern =>
      rw [heq]
      refine ⟨?_, ?_⟩
      · intro c'
        show RahmenErfuellt p.code (u.lokal c')
        exact huF c'
      · intro l
        show (((((u.sperren) l).besitzer)) = none)
        rw [huS]
        exact hs l

/-- A refused outside question halts only the acting frame. -/
theorem verweigertErhaelt (p : Fragment)
    (s : Ast.Semantik.Zustand) (c c' : Kontext)
    (F : Schrittform) (hR : ∀ c'', RahmenErfuellt p.code ((s.lokal) c'')) :
    RahmenErfuellt p.code (((F.verweigert c s).lokal) c') := by
  show RahmenErfuellt p.code
    (((Function.update s.lokal c ((s.lokal c).halt .ungueltigerBereich))) c')
  by_cases heq : c' = c
  · rw [heq]
    rw [Function.update_self]
    exact halt_erfuellt p.code (s.lokal c) _ (hR c)
  · rw [Function.update_of_ne heq]
    exact hR c'

/-- The joint invariant over an ideal run of an accepted fragment: every context frame
    satisfies the joined environments, and every lock is free. -/
theorem invariantAlle (p : Fragment) (platform : Plattform)
    (hfre : p.code.all keinFremdzugriff = true)
    (ρ : Maschine.I.Lauf (p.einheit platform))     (hρ : Maschine.I.Laeufe _ ρ) (t : Nat) :
    (∀ c, RahmenErfuellt p.code (((ρ.zeit.zustand t).lokal) c)) ∧
      (∀ l, ((((ρ.zeit.zustand t).sperren) l).besitzer) = none) := by
  induction t with
  | zero =>
      rw [hρ.2.2.2.1]
      refine ⟨?_, ?_⟩
      · intro c
        exact startRahmen_erfuellt p platform ρ.start c
      · intro l
        exact startSperren_frei p platform ρ.start l
  | succ t ih =>
      obtain ⟨ihR, ihS⟩ := ih
      cases ρ.zeit.takt t with
      | wartet label eq _ =>
          have heq := (ρ.zeit.wartet label).1
          rw [heq]
          exact ⟨ihR, ihS⟩
      | schritt label step =>
          cases step with
          | kontext hkb hber hreg haus =>
              rename_i u plan spur c w
              set s := ρ.zeit.zustand t with hs_def
              obtain ⟨b, head, ideal⟩ := hreg
              have hmem : b ∈ p.code := kopf_mem head
              have hfb : keinFremdzugriff b = true := (List.all_eq_true.mp hfre) b hmem
              obtain ⟨_, _, _, v, hfa, _, heq⟩ := haus
              have ideal' : b.ideal c s w [plan] u := ideal
              rcases Classical.em b.Privat with hpriv | hnpriv
              · obtain ⟨same, after⟩ := (b.ideal_privat hpriv c s w [plan] u).1 ideal'
                cases same
                have huF : ∀ c', RahmenErfuellt p.code (u.lokal c') := by
                  intro c'
                  rw [after]
                  show RahmenErfuellt p.code
                    (((Function.update s.lokal c
                      (b.auswerten (s.lokal c) (Ast.Semantik.Zustand.regionLive s)))) c')
                  by_cases heq2 : c' = c
                  · rw [heq2]
                    rw [Function.update_self]
                    exact auswerten_erfuellt p.code (s.lokal c) (Ast.Semantik.Zustand.regionLive s) b hmem hfre (ihR c)
                  · rw [Function.update_of_ne heq2]
                    exact ihR c'
                have huS : u.sperren = s.sperren := by rw [after]; rfl
                have hplan : Semantik.plan.aktion = .intern := rfl
                exact kontextEpilog p platform s u c t _ _ _ v _ huF huS ihS hplan hfa heq
              · have h1 : ∀ form, b ≠ .zugriff form := by
                  intro form heq2
                  rw [heq2] at hfb
                  simp only [keinFremdzugriff] at hfb
                  cases hfb
                have h2 : ∀ form, b ≠ .faden form := by
                  intro form heq2
                  rw [heq2] at hfb
                  simp only [keinFremdzugriff] at hfb
                  cases hfb
                have h3 : ∃ form, b = .aussen form := by
                  by_contra hc
                  push_neg at hc
                  exact hnpriv (Befehl.privat_von_kein_zugriff h1 h2 hc)
                obtain ⟨form, rfl⟩ := h3
                cases form with
                | frage ziel operation args =>
                    simp only [Befehl.ideal, Befehl.form, Schrittform.ideal,
                      AussenfrageformKlasse] at ideal'
                    rcases ideal' with ⟨_, same, refuse⟩ | ⟨_, vv, _, same, granted⟩
                    · have hpe : plan = Semantik.plan := (List.cons.inj same).1
                      have hU : u =
                          (Befehl.aussen (.frage ziel operation args)).form.verweigert
                            c s := refuse
                      have huF : ∀ c', RahmenErfuellt p.code (u.lokal c') := by
                        intro c'
                        rw [hU]
                        exact verweigertErhaelt p s c c' _ ihR
                      have huS : u.sperren = s.sperren := by rw [hU]; rfl
                      have hplan : plan.aktion = .intern := by
                        rw [hpe]
                        rfl
                      exact kontextEpilog p platform s u c t plan _ _ v _ huF huS ihS hplan hfa heq
                    · have hpe : plan =
                          (Befehl.aussen
                            (.frage ziel operation args)).form.plan
                            (s.lokal c) vv := (List.cons.inj same).1
                      have hU : u = (Befehl.aussen
                          (.frage ziel operation args)).form.zugriffNach c s vv := granted
                      have hue : (Befehl.aussen
                          (.frage ziel operation args)).form.uebertrag
                          (s.lokal c) (Ast.Semantik.Zustand.regionLive s) vv =
                          (s.lokal c).weiter :=
                        aussenUebertrag_weiter _ _ _ _
                      have huF : ∀ c', RahmenErfuellt p.code (u.lokal c') := by
                        intro c'
                        by_cases heq2 : c' = c
                        · rw [heq2]
                          have hact : (u.lokal) c = ((s.lokal c).weiter) := by
                            rw [hU]
                            show (((Function.update s.lokal c
                              ((Befehl.aussen
                                (.frage ziel operation args)).form.uebertrag
                                (s.lokal c) (Ast.Semantik.Zustand.regionLive s) vv))) c) =
                              ((s.lokal c).weiter)
                            rw [hue, Function.update_self]
                          rw [hact]
                          exact weiter_erfuellt p.code (s.lokal c) (ihR c)
                        · have hother : (u.lokal) c' = (s.lokal) c' := by
                            rw [hU]
                            show (((Function.update s.lokal c
                              ((Befehl.aussen
                                (.frage ziel operation args)).form.uebertrag
                                (s.lokal c) (Ast.Semantik.Zustand.regionLive s) vv))) c') =
                              (s.lokal) c'
                            rw [hue, Function.update_of_ne heq2]
                          rw [hother]
                          exact ihR c'
                      have huS : u.sperren = s.sperren := by rw [hU]; rfl
                      have hplan : plan.aktion = .intern := by
                        rw [hpe]
                        rfl
                      exact kontextEpilog p platform s u c t plan _ _ v _ huF huS ihS hplan hfa heq
                | verbrauche ziel =>
                    simp only [Befehl.ideal, Befehl.form, Schrittform.ideal,
                      AussenfrageformKlasse] at ideal'
                    obtain ⟨same, after⟩ := ideal'
                    have hpe : plan = Semantik.plan := (List.cons.inj same).1
                    have hU : u = (Befehl.aussen
                      (.verbrauche ziel)).form.verbraucheNach c s := after
                    have hpoisI : umgebungInt p.code ziel = none :=
                      umgebungInt_unbekannt _ _
                        (aussenVerbrauche_poisonInt _ _ hmem)
                    have hpoisT : umgebungText p.code ziel = none :=
                      umgebungText_unbekannt _ _
                        (aussenVerbrauche_poisonText _ _ hmem)
                    cases hna : s.naechsteAntwort c with
                    | none =>
                        have hUn : u = (Befehl.aussen
                            (.verbrauche ziel)).form.nach c s 0 := by
                          rw [hU]
                          conv_lhs => simp only [Schrittform.verbraucheNach, hna]
                        have huF : ∀ c', RahmenErfuellt p.code (u.lokal c') := by
                          intro c'
                          by_cases heq2 : c' = c
                          · rw [heq2]
                            have hact : (u.lokal) c = ((s.lokal c).weiter) := by
                              rw [hUn]
                              show (((Function.update s.lokal c
                                ((Befehl.aussen
                                  (.verbrauche ziel)).form.uebertrag
                                  (s.lokal c) (Ast.Semantik.Zustand.regionLive s) 0))) c) =
                                ((s.lokal c).weiter)
                              rw [aussenUebertrag_weiter, Function.update_self]
                            rw [hact]
                            exact weiter_erfuellt p.code (s.lokal c) (ihR c)
                          · have hother : (u.lokal) c' = (s.lokal) c' := by
                              rw [hUn]
                              show (((Function.update s.lokal c
                                ((Befehl.aussen
                                  (.verbrauche ziel)).form.uebertrag
                                  (s.lokal c) (Ast.Semantik.Zustand.regionLive s) 0))) c') =
                                (s.lokal) c'
                              rw [aussenUebertrag_weiter, Function.update_of_ne heq2]
                            rw [hother]
                            exact ihR c'
                        have huS : u.sperren = s.sperren := by
                          rw [hUn]
                          rfl
                        have hplan : plan.aktion = .intern := by
                          rw [hpe]
                          rfl
                        exact kontextEpilog p platform s u c t plan _ _ v _
                          huF huS ihS hplan hfa heq
                    | some a =>
                        cases hr : a.reply.result with
                        | ok _ok =>
                            have huF : ∀ c', RahmenErfuellt p.code (u.lokal c') := by
                              intro c'
                              by_cases heq2 : c' = c
                              · rw [heq2]
                                have hact : (u.lokal) c =
                                    ((s.lokal c).schreibe
                                      ((Befehl.aussen
                                        (.verbrauche ziel)).form.operand
                                        (s.lokal c)).ziel
                                      (some ⟨.bool, true⟩)) := by
                                  rw [hU]
                                  conv_lhs => simp only [Schrittform.verbraucheNach,
                                    hna, hr, verbraucheSchreibe, Zustand.verbrauche,
                                    Befehl.operand, Function.update_self]
                                rw [hact]
                                exact schreibePoison_erfuellt p.code (s.lokal c) ziel _
                                  (ihR c) hpoisI hpoisT
                              · have hother : (u.lokal) c' = (s.lokal) c' := by
                                  rw [hU]
                                  exact Schrittform.verbraucheNach_andere _ c s c' heq2
                                rw [hother]
                                exact ihR c'
                            have huS : u.sperren = s.sperren := by
                              rw [hU]
                              simp only [Schrittform.verbraucheNach, hna, hr,
                                Zustand.verbrauche]
                            have hplan : plan.aktion = .intern := by
                              rw [hpe]
                              rfl
                            exact kontextEpilog p platform s u c t plan _ _ v _
                              huF huS ihS hplan hfa heq
                        | error e =>
                            have huF : ∀ c', RahmenErfuellt p.code (u.lokal c') := by
                              intro c'
                              by_cases heq2 : c' = c
                              · rw [heq2]
                                have hact : (u.lokal) c = ((s.lokal c).weiter) := by
                                  rw [hU]
                                  conv_lhs => simp only [Schrittform.verbraucheNach,
                                    hna, hr, Zustand.verbrauche]
                                  show (((Function.update s.lokal c
                                    (((s.lokal c).weiter)))) c) = ((s.lokal c).weiter)
                                  rw [Function.update_self]
                                rw [hact]
                                exact weiter_erfuellt p.code (s.lokal c) (ihR c)
                              · have hother : (u.lokal) c' = (s.lokal) c' := by
                                  rw [hU]
                                  exact Schrittform.verbraucheNach_andere _ c s c' heq2
                                rw [hother]
                                exact ihR c'
                            have huS : u.sperren = s.sperren := by
                              rw [hU]
                              simp only [Schrittform.verbraucheNach, hna, hr,
                                Zustand.verbrauche]
                            have hplan : plan.aktion = .intern := by
                              rw [hpe]
                              rfl
                            exact kontextEpilog p platform s u c t plan _ _ v _
                              huF huS ihS hplan hfa heq
          | antwort _ h =>
              obtain ⟨_, _, _, heqst⟩ := h
              rw [heqst]
              refine ⟨?_, ?_⟩
              · intro c
                show RahmenErfuellt p.code (((ρ.zeit.zustand t).lokal) c)
                exact ihR c
              · intro l
                show (((((ρ.zeit.zustand t).sperren) l).besitzer) = none)
                exact ihS l
          | interrupt _ h =>
              obtain ⟨_, _, _, _, _, _, _, _, _, _, heqst⟩ := h
              rw [heqst]
              refine ⟨?_, ?_⟩
              · intro c
                show RahmenErfuellt p.code (((ρ.zeit.zustand t).lokal) c)
                exact ihR c
              · intro l
                show ((((((ρ.zeit.zustand t).sperren) l).besitzer) = none))
                exact ihS l
          | absturz h =>
              obtain ⟨_, hst⟩ := AbsturzSchritt.genau h
              rw [hst]
              refine ⟨?_, ?_⟩
              · intro c
                exact absturzRahmen_erfuellt p platform _ _ _ c
              · intro l
                exact absturzSperren_frei p platform _ _ _ l

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
