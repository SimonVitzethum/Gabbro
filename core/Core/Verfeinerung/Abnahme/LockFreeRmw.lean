/-
  File:      core/Core/Verfeinerung/Abnahme/LockFreeRmw.lean
  Subject:   A SECOND, non-vacuous refutation of `LockFreeFamilienAussage`: the lost-value
             implementation of a real MK-04 rmw instruction (`Befehl.zugriff` with
             `Zugriffsform.tausche`). The concrete machine represents the error: the false rule
             commits an rmw event at a state where the instruction's guarded ideal rule -- its
             specification -- refuses the access, binding `0` independently of the value the event
             records. The family statement excludes that error through its simulation leg
             (`RegelSimulation`), hence through `LockFreeFamilienAussage.1`, whatever abstraction
             or specification the family declares. The existing `nichtTrivial`, which changes only
             the declared start abstraction, is not reused here.
-/
module

public import Core.Verfeinerung.Abnahme.LockFree
public import Core.Ast.Semantik.Runtime.Atom.Aussagen
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Maschine.Speicherfolge

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog
open Gabbro.Core.Ast.Semantik

/-- The unit, state and plan types of the witness. -/
abbrev RmwZeugeEinheit := Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Unit
abbrev RmwZeugeZustand := Zustand Nat Zelle Int Nat Rahmen PUnit
abbrev RmwZeugePlan := SchrittPlan Nat Zelle Int PUnit
abbrev RmwZeugeRegel := Regel RmwZeugeZustand RmwZeugePlan PUnit

/-- A real atomic update instruction of MK-04: `tausche` of region 0, cell 0. -/
def rmwZeugeBefehl : Befehl := .zugriff (.tausche 0 0 0 0 (Ast.Ty.int 0 0) .sc)

/-- Its step form: one rmw event that reads and writes the cell. -/
def rmwZeugeForm : Schrittform := rmwZeugeBefehl.form

/-- The false implementation: the rule fires the rmw and binds `0`, whatever the memory returned.
    Its ideal side is the guarded instruction rule, which refuses an access without authority. -/
def rmwZeugeRegelWert : RmwZeugeRegel := Schrittform.verloren rmwZeugeForm

/-- The unit whose only form is that false rmw instruction. -/
def rmwZeugeEinheitWert : RmwZeugeEinheit := Regeleinheit .x86_64 rmwZeugeRegelWert

/-- The frame of the empty start holds no temporary, so the instruction names the outside cell. -/
theorem rmwZeuge_operand_aussen :
    (rmwZeugeForm.operand (Leerzustand.lokal eintritt)) =
      ⟨.aussen, 0, 0, none, .tausche⟩ := by
  rfl

/-- The plan of the real instruction at that frame: one rmw event reading `gelesen`, writing `0`. -/
theorem rmwZeuge_plan (gelesen : Int) :
    rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen =
      ⟨.intern, [⟨.rmw, .aussen, .sc, gelesen, 0⟩], [],
        (fun _ => false), (fun _ => .na), (fun _ => 0)⟩ := by
  rfl

/-- No context holds a handle at the outside cell, so the guarded rule refuses. -/
theorem rmwZeuge_keinRecht :
    ¬ rmwZeugeForm.klasse.befugt (rmwZeugeForm.operand (Leerzustand.lokal eintritt))
        Leerzustand eintritt := by
  rw [rmwZeuge_operand_aussen]
  simp only [Wirkungsklasse.befugt, Zustand.befugt, Zustand.griff]
  rintro ⟨⟨_, _, griff, _⟩, _⟩
  cases griff

/-- The model represents the error: a concrete rmw step with a non-empty memory trace, whose
    implementation binds `0` while the recorded event reads another value, and whose ideal rule
    refuses the access at the same state. -/
theorem rmwZeugeKonfiguration :
    ∃ (gelesen : Int) (plan : RmwZeugePlan) (spur : SchrittSpur Zelle Int)
      (u s' : RmwZeugeZustand),
    plan = rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen ∧
      u = Schrittform.zugriffNach rmwZeugeForm eintritt Leerzustand 0 ∧
      rmwZeugeRegelWert.impl eintritt Leerzustand () [plan] u ∧
      FuehrtSchrittAus rmwZeugeEinheitWert.einrichtung 0 eintritt Leerzustand u plan spur s' ∧
      spur.speicher ≠ [] ∧
      spur.aussen = [] ∧
      ¬ rmwZeugeRegelWert.ideal eintritt Leerzustand () [plan] u := by
  obtain ⟨gelesen, es, graph, folge⟩ := speicherzug_existiert
    (anfang := Leerzustand.initial) (f := .kontext eintritt)
    (g := Leerzustand.graph) Speicher.Zustand.leer_konsistent
    Speicher.Zustand.leer_vollstaendig (a := .rmw) (x := .aussen) (m := .sc) (v := 0)
  let plan : RmwZeugePlan :=
    ⟨.intern, [⟨.rmw, .aussen, .sc, gelesen, 0⟩], [],
      (fun _ => false), (fun _ => .na), (fun _ => 0)⟩
  let spur : SchrittSpur Zelle Int := ⟨es, []⟩
  have planLesen : plan.lesen =
      [⟨.rmw, .aussen, .sc, gelesen, (0 : Int)⟩] := by
    rfl
  let u := Schrittform.zugriffNach rmwZeugeForm eintritt Leerzustand 0
  let s' : RmwZeugeZustand := { u with graph := graph }
  have rahmen : Zustandsrahmen Leerzustand u :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have liest : ∀ l ∈ plan.lesen, l.art.liest := by
    intro l mem
    change l ∈ [⟨.rmw, .aussen, .sc, gelesen, 0⟩] at mem
    rcases List.mem_singleton.mp mem with rfl
    simp only [Gabbro.Core.Speicher.Art.liest]
  have spurGefuellt : spur.speicher ≠ [] := by
    cases folge with
    | cons _ _ _ =>
      intro leer
      have letzte := (List.append_eq_nil_iff.mp leer).2
      cases letzte
  have aus : FuehrtSchrittAus rmwZeugeEinheitWert.einrichtung 0 eintritt Leerzustand u plan spur s' := by
    refine ⟨rahmen, liest, [], u, .intern, ?_, rfl⟩
    simpa only [plan, SchrittSpur.speicher, spur, SchrittPlan.lesen, SchrittPlan.fuss,
      SchrittPlan.schreibt, SchrittPlan.modus, SchrittPlan.wert, schreibEreignisse,
      List.filter_nil, List.map_nil, List.nil_append, List.append_nil] using folge
  have impl : rmwZeugeRegelWert.impl eintritt Leerzustand () [plan] u := by
    refine ⟨gelesen, ?_, rfl⟩
    change [plan] = [rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen]
    rw [rmwZeuge_plan]
  have idealVerweigert : ¬ rmwZeugeRegelWert.ideal eintritt Leerzustand () [plan] u := by
    intro step
    change rmwZeugeForm.zugriffsschritt eintritt Leerzustand [plan] u at step
    rcases step with ⟨_, planPrivat, _⟩ | ⟨befugt, _, _, _⟩
    · have planGleich : plan = Gabbro.Core.Ast.Semantik.plan :=
        (List.cons.inj planPrivat).1
      have lesenLeer : plan.lesen = [] := by
        rw [planGleich]
        rfl
      rw [planLesen] at lesenLeer
      cases lesenLeer
    · exact rmwZeuge_keinRecht befugt
  exact ⟨gelesen, plan, spur, u, s', rmwZeuge_plan gelesen, rfl, impl, aus,
    spurGefuellt, rfl, idealVerweigert⟩

/-- The family statement refuses that error: the false rmw rule cannot satisfy its simulation leg. -/
theorem rmwZeuge_nichtRegelSimulation : ¬ RegelSimulation rmwZeugeEinheitWert () := by
  intro sim
  obtain ⟨gelesen, plan, spur, u, s', planEq, uEq, impl, exec, spurNe, aussenLeer, idealNe⟩ :=
    rmwZeugeKonfiguration
  subst plan
  subst u
  let hw : HwLauf := Umgebung.referenzLauf Plattform.x86_64.katalog 1
    (fun _ _ => ⟨(fun _ => ⟨0, false, false, [], fun _ => 0⟩),
      (fun _ _ => none), (fun _ _ => none)⟩)
  have crash : (hw.angebot 0).crash = false := by
    simp only [hw, Umgebung.referenzLauf]
  have ready : KannSchreiten hw 0 eintritt Leerzustand := by
    refine ⟨0, ?_, ?_, ?_⟩
    · change some (0 % 1) = some 0
      exact congrArg some (Nat.mod_one _)
    · change (Leerzustand.kerne 0).laeuft = some eintritt
      rfl
    · change Leerzustand.status eintritt = .laeuft
      simp only [Leerzustand, startdaten, Zustand.start, ite_self, ite_true]
  have bezug : Zustandsbezug rmwZeugeEinheitWert Leerzustand Leerzustand :=
    ⟨ProtokollBezug.refl _, rfl⟩
  have simuliert := sim.schritt (hw := hw) (t := 0) (c := eintritt) (w := ())
    (s := Leerzustand) (u := Schrittform.zugriffNach rmwZeugeForm eintritt Leerzustand 0)
    (s' := s') (i := Leerzustand)
    (plan := rmwZeugeForm.plan (Leerzustand.lokal eintritt) gelesen) (spur := spur)
    bezug crash ready rfl impl exec
  have planBeiIdeal (p : RmwZeugePlan) (v : RmwZeugeZustand)
      (step : System.ISchritt rmwZeugeEinheitWert.system eintritt Leerzustand () [p] v) :
      p = Gabbro.Core.Ast.Semantik.plan := by
    rcases step with ⟨i, _, idealRegel⟩
    cases i
    change rmwZeugeForm.zugriffsschritt eintritt Leerzustand [p] v at idealRegel
    rcases idealRegel with ⟨_, privat, _⟩ | ⟨befugt, _, _, _⟩
    · exact (List.cons.inj privat).1
    · exact (rmwZeuge_keinRecht befugt).elim
  rcases simuliert with ⟨i', idealSchritt, _⟩ | ⟨leer, _, _, _, _⟩
  · cases idealSchritt with
    | kontext _ _ rule ausIdeal =>
      have planPrivat := planBeiIdeal _ _ rule
      simp only [FuehrtSchrittAus] at ausIdeal
      rw [planPrivat, aussenLeer] at ausIdeal
      rcases ausIdeal with ⟨_, _, _, _, aus, folge, _⟩
      cases aus
      simp only [Gabbro.Core.Ast.Semantik.plan, schreibEreignisse, List.filter_nil,
        List.map_nil, List.nil_append, List.append_nil] at folge
      generalize hg : i'.graph = endGraph at folge
      generalize ht : spur.speicher = trace at folge
      have leerTrace : trace = [] := by
        cases folge
        rfl
      exact spurNe (ht.trans leerTrace)
  · exact spurNe (congrArg SchrittSpur.speicher leer)

/-- The non-triviality is a statement about the family, not about a changed declaration of its
    abstraction: a family with the false rmw rule as a member owes its simulation and cannot pay it. -/
theorem LockFreeFamilienAussage.nichtTrivialRmw :
    ∃ U : LockFreeEinheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit PUnit,
      ¬ LockFreeFamilienAussage U := by
  let U : LockFreeEinheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit PUnit :=
    ⟨rmwZeugeEinheitWert, PUnit, PUnit, PUnit, PUnit, fun _ => True,
      ⟨fun _ => none, rfl, fun _ _ => rfl⟩, fun _ => (), (), fun _ _ _ _ => True⟩
  refine ⟨U, ?_⟩
  intro aussage
  have sim : RegelSimulation U.einheit () := aussage.1 () trivial
  exact rmwZeuge_nichtRegelSimulation (by simpa only [U] using sim)

end Gabbro.Core.Maschine.I
