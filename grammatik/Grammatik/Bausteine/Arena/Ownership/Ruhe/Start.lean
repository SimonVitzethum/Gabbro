import Grammatik.Bausteine.Arena.Ownership.Ruhe.Lift
import Grammatik.Bausteine.Arena.Ownership.Machine.Reach
import Grammatik.Zielsatz.Atomar.AtomarZiel

/-! **What the ownership leg of `GabbroZiel` needs, from the goal's premises.**
The thread facts the rely needs (`ThreadFacts`) come from the checker's facts
(a) and the admissible start; what the start owes every arena (`StartOwn`)
comes from the checker's `BesitzStart` and the runtime (d). Nothing is added
to the user's obligation and nothing is assumed of RAM or hardware. The leg
itself is `ZielFX.besitz`, proved in `zielFX_aus`. -/

namespace Gabbro.Grammatik.ArenaOwnership.Ruhe

open Source Body Machine Zielsatz

variable {D : Deklaration}

/-! ## 1. The thread facts from the checker and the runtime -/

def threadFacts_of [DecidableEq D.Fn] {P : Programm D} {S : SperrInv D} {A : FreiForm D} {fs ws : List D.Fn}
    {B : List (ArenaIface D)} {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hA : AkzeptiertSpecX P S fs ws B) (hZ : StartZulaessig P S fs ws sp init) (hp : ArenaPlain A) :
    ThreadFacts P A fs init := by
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => by
    rcases hZ.wurzel t with h | h
    · exact (hA.wurzeln _ h).1
    · exact h.1
  refine ⟨kVon P fs init, fun t => hA.abg _, fun t => reachB_wurzel P fs _, startExklusiv_ohne_haelt init hLeer, ?_⟩
  intro g hg hB
  have hAt : ¬ AtomarAusgenommen (.inr g : D.Tab ⊕ D.Glob) := by
    rcases hg with rfl | rfl
    · exact plain_kopf hp
    · exact plain_zaehl hp
  exact schreibGetrenntK_of hZ hA.einzeln hB hAt (hA.renn _ hB hAt)

/-! ## 2. The ownership start -/

theorem umTyp_valR {τ : Ty} {a b : Int} (h : τ = .int a b) (h' : tyR τ = .int a b) (v : Wert D τ) :
    (Wert.umTyp (D := D.mitRuhe) h' (show Wert D.mitRuhe (tyR τ) from valR τ v)).n = (Wert.umTyp h v).n := by
  subst h; rfl

theorem arenaLeer_lift {A : FreiForm D} {sp0 : Speicher D} (h : ArenaLeer A sp0) :
    (liftA A).stand ((speicherR sp0).welt []) = 0 ∧
      (liftA A).kopfSt ((speicherR sp0).welt []) = D.mitRuhe.count (liftA A).tab := by
  refine ⟨?_, ?_⟩
  · have := umTyp_valR A.hz (liftA A).hz (sp0.globs A.zaehl)
    exact this.trans h.1
  · have := umTyp_valR A.hkopf (liftA A).hkopf (sp0.globs A.kopf)
    exact this.trans h.2

theorem freiOk_leer {A : FreiForm D} {σ : World D} (hs : A.stand σ = 0) (hk : A.kopfSt σ = D.count A.tab) :
    A.FreiOk σ ∧ ∀ i, ¬ A.Lebt σ i := by
  refine ⟨⟨[], by rw [hk]; exact .nil, List.nodup_nil, fun _ h => by cases h⟩, fun i hi => ?_⟩
  have h1 := hi.2.1; have h0 := hi.1; rw [hs] at h1; omega

theorem requires_plain {A : FreiForm D} {f : D.Fn} (I : Flow.Interface A f)
    (h : (modeList I.parameters).all Option.isNone = true) (frame : Frame) (ρ : Env D (D.params f)) :
    (I.contract A).requires frame State.empty ρ := by
  have hnone : ∀ u : Nat, ((modeList I.parameters)[u]?).getD none = none := by
    intro u
    cases hu : (modeList I.parameters)[u]? with
    | none => rfl
    | some m =>
      have := List.all_eq_true.mp h m (List.mem_of_getElem? hu)
      simpa using this
  refine ⟨fun _ => none, ⟨(Flow.parameterContext_length _).1, fun x o hx => ?_⟩, ⟨fun o m hm => ?_, ?_⟩, ?_⟩
  · rw [parameterContext_reference] at hx
    have hm := modeList_at I.parameters x
    have := hnone x.unten
    rw [hm] at this
    simp only [Option.getD_some] at this
    rw [this] at hx
    cases hx
  · rw [parameterContext_rights, hnone] at hm; cases hm
  · intro i j p q hi; rw [parameterContext_rights, hnone] at hi; cases hi
  · intro slot cell hc; cases hc

/-- **The start owes the arena what `StartOwn` asks**, from the declared start memory and starts. -/
theorem startOwn_of [DecidableEq D.Fn] {E : Einheit D} {A : FreiForm D} {I : Interfaces A}
    {sp : Speicher D.mitRuhe} {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hL : Laufzeit E sp init) (hleer : ArenaLeer A E.sp0)
    (hstart : ∀ r ∈ E.starts ++ E.gestartet, (modeList (I r.1).parameters).all Option.isNone = true) :
    StartOwn (liftA A) (liftI I) sp init := by
  obtain ⟨hs, hk⟩ := arenaLeer_lift hleer
  rw [← hL.lader] at hs hk
  obtain ⟨hfo, hno⟩ := freiOk_leer hs hk
  refine ⟨hfo, hno, fun t => ?_⟩
  rcases hL.start t with h | ⟨a, ha, h⟩
  · rw [h]; exact requires_plain (liftI I none) rfl _ _
  · rw [h]
    apply requires_plain (liftI I (some a.1))
    show (modeList (modesR (I a.1).parameters)).all Option.isNone = true
    rw [modeList_modesR]; exact hstart a ha

/-- **Every arena of the unit, lifted, owes its start**, from the checker's `BesitzStart` and (d). -/
theorem startOwn_arenen [DecidableEq D.Fn] {E : Einheit D} {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hL : Laufzeit E sp init) (hB : BesitzStart E) :
    ∀ a ∈ E.arenen.map (·.mitRuhe), StartOwn a.A a.I sp init := by
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  exact startOwn_of hL (hB.leer a ha) (hB.start a ha)

#print axioms threadFacts_of
#print axioms startOwn_arenen

end Gabbro.Grammatik.ArenaOwnership.Ruhe
