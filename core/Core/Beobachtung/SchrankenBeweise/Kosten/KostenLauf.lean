module

public import Core.Beobachtung.SchrankenBeweise.Kosten.KostenRahmen
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

def KostenGrenzen.ZustandGut (g : KostenGrenzen) (s : Zustand) : Prop :=
  ∀ c, g.RahmenGut (s.lokal c)

variable {g : KostenGrenzen} {s u : Zustand} {b : Befehl} {c : Kontext}

private theorem update_rahmen {frames : Kontext → Rahmen} {r : Rahmen}
    (ok : ∀ d, g.RahmenGut (frames d)) (new : g.RahmenGut r) :
    ∀ d, g.RahmenGut (Function.update frames c r d) := by
  intro d
  by_cases h : d = c
  · subst d
    simpa only [Function.update_self] using new
  · simpa only [Function.update_of_ne h] using ok d

private theorem nach_gut (ok : g.ZustandGut s) (install : g.Einrichtung b (s.lokal c)) (v : Int) :
    g.ZustandGut (b.form.nach c s v) :=
  update_rahmen ok (KostenGrenzen.uebertrag (ok c) install s.regionLive v)

private theorem verbrauche_gut (ok : g.ZustandGut s) (install : g.Einrichtung b (s.lokal c)) :
    g.ZustandGut (b.form.verbraucheNach c s) := by
  unfold Schrittform.verbraucheNach
  split
  · exact nach_gut ok install 0
  · split
    · split
      · unfold verbraucheSchreibe
        split <;> exact update_rahmen ok (ok c)
      · exact update_rahmen ok (ok c)
    · exact update_rahmen ok (ok c)

private theorem faeden_gut (ok : g.ZustandGut s) (install : g.Einrichtung b (s.lokal c)) :
    g.ZustandGut (b.form.faedenNach c s) := by
  have transfer : ∀ v, g.RahmenGut (b.form.uebertrag (s.lokal c) s.regionLive v) :=
    KostenGrenzen.uebertrag (ok c) install s.regionLive
  have child : g.RahmenGut { (b.form.operand (s.lokal c)).faden.anfang with fortsetzungen := [] } := by
    cases b <;> try exact g.start []
    case zugriff z => cases z <;> exact g.start []
    case aussen z => cases z <;> exact g.start []
    case faden z =>
      cases z <;> exact g.start []
  unfold Schrittform.faedenNach
  dsimp only
  split
  all_goals try exact nach_gut ok install 0
  · apply update_rahmen (update_rahmen ok (transfer _)) child
  · exact update_rahmen ok (transfer _)
  · split
    · exact update_rahmen ok (transfer _)
    · exact update_rahmen ok (ok c)
    · exact ok
    · exact ok

private theorem ideal_gut (ok : g.ZustandGut s) (install : g.Einrichtung b (s.lokal c))
    (step : b.ideal c s w plans u) : g.ZustandGut u := by
  change b.form.ideal c s w plans u at step
  unfold Schrittform.ideal at step
  split at step
  all_goals first
  | (obtain ⟨_, rfl⟩ := step; exact nach_gut ok install 0)
  | (obtain ⟨_, rfl⟩ := step; exact verbrauche_gut ok install)
  | (rcases step with ⟨_, _, rfl⟩ | ⟨_, v, _, _, rfl⟩
     · exact update_rahmen ok (ok c)
     · exact nach_gut ok install v)
  | (rcases step with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
     · exact update_rahmen ok (ok c)
     · exact faeden_gut ok install)

private theorem kopf_position {code : List Befehl} (head : kopf code s c = some b) :
    (s.lokal c).Aktiv ∧ code[(s.lokal c).pc]? = some b := by
  unfold kopf at head
  cases hstatus : s.status c <;> rw [hstatus] at head
  case ruht => cases head
  case beendet => cases head
  case laeuft =>
    cases hreturn : (s.lokal c).rueckgabe <;> rw [hreturn] at head
    case some => cases head
    case none =>
      cases hstop : (s.lokal c).stopp <;> rw [hstop] at head
      case some => cases head
      case none => exact ⟨⟨hstop, hreturn⟩, head⟩

theorem KostenGrenzen.startdaten (g : KostenGrenzen) (scope : Scope)
    (entries : Kontext → Option Nat) (core : Option Nat) (P : Plattform) (regions : List Strecke)
    (d : Kontext) : g.RahmenGut ((startdaten scope entries core P regions).lokal d) :=
  g.start scope

/-- At every observed cut, all active and saved frames obey the cost limits if the
    three installing instructions have valid operands and site metadata. -/
theorem KostenGrenzen.lauf (p : Fragment) (P : Plattform) (bounds : Beobachtung.Schrankendaten Nat Rahmen)
    {ρ : Lauf { p.einheit P with schranken := bounds }} {h : Annahme.Umgebung}
    (run : Laeufe { p.einheit P with schranken := bounds } h ρ)
    (installs : ∀ t s c b, ρ.zeit.zustand t = some s → g.ZustandGut s →
      (s.lokal c).Aktiv → p.code[(s.lokal c).pc]? = some b → g.Einrichtung b (s.lokal c))
    (t : Nat) (cut : ρ.zeit.zustand t = some s) : g.ZustandGut s := by
  induction t generalizing s with
  | zero =>
    have loaded := run.2.2.2
    rw [cut] at loaded
    change some s = laden p.eingang p.eintritte p.speicher P ρ.start (h.lade _) at loaded
    unfold laden at loaded
    split at loaded
    · cases loaded
      exact g.startdaten _ _ _ _ _
    · cases loaded
  | succ t ih =>
    have tick := ρ.zeit.takt t
    rw [cut] at tick
    cases before : ρ.zeit.zustand t with
    | none =>
      rw [before] at tick
      cases tick with
      | wartet _ same _ => cases same
      | schritt _ step => cases step
    | some prev =>
      rw [before] at tick
      have ok := ih before
      cases tick with
      | wartet _ same _ => cases same; exact ok
      | schritt _ step =>
        cases step with
        | schritt step =>
          cases step with
          | kontext _ _ rule effect =>
            obtain ⟨b, head, instruction⟩ := rule
            obtain ⟨active, lookup⟩ := kopf_position head
            have good := ideal_gut ok (installs t _ _ _ before ok active lookup) instruction
            obtain ⟨_, _, _, _, protocol, _, rfl⟩ := effect
            cases protocol <;> exact good
          | antwort _ answer =>
            obtain ⟨_, _, _, rfl⟩ := answer
            exact ok
          | interrupt _ interrupt =>
            obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := interrupt
            exact ok
          | absturz crash =>
            obtain ⟨_, _, _, _, rfl⟩ := crash
            exact g.startdaten _ _ _ _ _

end Gabbro.Core.Ast.Semantik
