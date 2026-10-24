import Grammatik.Bausteine.Arena.Ownership.Ruhe.Lift
import Grammatik.Bausteine.Arena.Ownership.Machine.Reach
import Grammatik.Zielsatz.Atomar.BeweisAtomar

/-! **The ownership leg on the goal's own runs.** Under the goal statement's
premises -- the checker accepts the unit (a), the start obligations of the
user (b), the hardware (c), the runtime (d) -- and the ownership acceptance
of an arena (its executable check, plain allocator words, an empty arena in
the declared start memory, start routines handed no allocation), ownership
holds on every thread machine over GX that `GabbroZiel` speaks about. The
thread facts the rely needs are derived from (a) and (d); nothing is added
to the user's obligation and nothing is assumed of RAM or hardware. -/

namespace Gabbro.Grammatik.ArenaOwnership.Ruhe

open Source Body Machine Zielsatz

variable {D : Deklaration}

/-! ## 1. The thread facts from the checker and the runtime -/

def threadFacts_of [DecidableEq D.Fn] {P : Programm D} {S : SperrInv D} {A : FreiForm D} {fs ws : List D.Fn}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hA : AkzeptiertSpecX P S fs ws) (hZ : StartZulaessig P S fs ws sp init) (hp : ArenaPlain A) :
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

/-! ## 2. The ownership acceptance of the start -/

/-- **The declared start memory holds an empty arena**: nothing used, the list empty. -/
def ArenaLeer (A : FreiForm D) (sp0 : Speicher D) : Prop :=
  A.stand (sp0.welt []) = 0 ∧ A.kopfSt (sp0.welt []) = D.count A.tab

instance (A : FreiForm D) (sp0 : Speicher D) : Decidable (ArenaLeer A sp0) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **No start routine is handed an allocation**: every parameter of a declared start is plain. -/
def StartPlain {A : FreiForm D} (I : Interfaces A) (E : Einheit D) : Prop :=
  ∀ a ∈ E.starts ++ E.gestartet, (modeList (I a.1).parameters).all Option.isNone = true

instance {A : FreiForm D} (I : Interfaces A) (E : Einheit D) : Decidable (StartPlain I E) :=
  inferInstanceAs (Decidable (∀ a ∈ _, _))

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
    (hL : Laufzeit E sp init) (hleer : ArenaLeer A E.sp0) (hstart : StartPlain I E) :
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

/-! ## 3. The leg -/

/-- **Ownership on the goal's runs.** Every machine of every thread-machine run over GX from the
    runtime's start -- the runs `GabbroZiel` speaks about -- satisfies the ownership invariant of
    the arena, lifted to the program with its idle root. -/
theorem ownership_goal_gx (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) (hL : Laufzeit E sp init)
    (a : ArenaIface D) (hacc : checkProgram E.P a.A a.I fs.1 = true) (hp : ArenaPlain a.A)
    (hleer : ArenaLeer a.A E.sp0) (hstart : StartPlain a.I E)
    (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe)
    (hK : FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (FadenStart E.P.mitRuhe sp init lebt0) K) :
    OwnInv (liftA a.A) (liftI a.I) K.m := by
  have hA0 := C.korrekt E fs ls cs hC
  have hA := akzeptiertSpecX_mitRuhe E.P fs.2 hA0
  have hZ := startZulaessig_aus E fs.1 hN.start hL
  have hp' : ArenaPlain (liftA a.A) := hp
  exact ownInv_reachGX (hardware_mitRuhe hH).1 (checked_mitRuhe (checkProgram_sound fs.2 hacc))
    (fsRuhe_voll fs.2) (threadFacts_of hA hZ hp') (startOwn_of hL hleer hstart) hp'
    (fun c hc => hc.1.1) (fadenErreichbarX_GX hK)

#print axioms ownership_goal_gx

end Gabbro.Grammatik.ArenaOwnership.Ruhe
