/-
  File:      Grammatik/Zielsatz/AtomarPflicht.lean
  Subject:   THE USER'S OBLIGATION (b) WITH THE ATOMIC RELY, and its embedding (Opus lane O25b,
             2026-09-26, OFFEN O25). Standalone: `Spec.lean` does not import this file; what is
             defined here is the (b) a Spec diff for O25 would name.

  THE SHARED ATOMICS OF A UNIT (`GeteiltA P ws c`): an `atomic` global with no guard lock that is
  NOT thread-local among the declared starts -- some start's call graph reads it in a footprint
  while a different start occurrence may write it (`GetrenntR`, the enumeration-free twin of the
  checker's `Getrennt`, over the call closure `Erreicht`). Exactly these are the carriers another
  thread may change between two reads with nothing in the program ordering it; a thread-local
  atomic is read like a plain carrier (its own writes only), a guarded one under its lock.

  THE OBLIGATION (`KoerperGutSA`, `InvGutSA`, `InvGutGrundA`, `LogikPflichtA`): `LogikPflicht`
  with every body run by `execEndHA` (Speichermodell/AtomarSem.lean) against EVERY atomic
  environment in `HavocA (GeteiltA P ws)`: at every read of a shared atomic the user's proof
  meets every value -- the rely. Nothing else changes: the same handlers, oracles, lock moves.

  THE EMBEDDING, both directions:
  * `logikPflicht_of_A` -- the new obligation implies the old one on EVERY unit (the identity
    environment is in the class): no program loses a theorem it had;
  * `logikPflichtA_of_frei` -- on a unit none of whose bodies reads a shared atomic, the old
    obligation implies the new one: there the rely is no burden;
  * `akzeptiert_liest_nicht_geteilt` -- every unit the goal's checker accepts (`AkzeptiertSpec`,
    i.e. with the footprint rule that refuses unguarded shared reads) is such a unit. So on every
    unit the goal statement covers today the two obligations are EQUIVALENT
    (`logikPflichtA_iff_akzeptiert`): moving (b) to `LogikPflichtA` drops no program and adds no
    duty where there was none.
-/
import Grammatik.Zielsatz.Spec
import Grammatik.Speichermodell.AtomarRec
import Grammatik.MitRuheStatisch

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The shared atomics -/

section Geteilt

variable [DecidableEq D.Fn]

/-- **The call closure of `w`** (enumeration-free): `w`, and every function a function of the
    closure calls (`ruftB`). -/
inductive Erreicht (P : Programm D) (w : D.Fn) : D.Fn → Prop
  | wurzel : Erreicht P w w
  | ruf {f g : D.Fn} : Erreicht P w f → ruftB P f g = true → Erreicht P w g

/-- **Thread-local among the starts `ws`, over the call closure** (the twin of `Getrennt`,
    Spec.lean, without a member list). -/
def GetrenntR (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → ∀ f g, Erreicht P w₁ f →
    c ∈ fussOrteG P f → Erreicht P w₂ g → TraegerSchreibt g c = false

/-- **A shared atomic of the unit**: `atomic`, unguarded, and not thread-local. -/
def GeteiltA (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  AtomarAusgenommen c ∧ (∀ L, ¬ Bewacht c L) ∧ ¬ GetrenntR P ws c

/-- The computed graph contains the closure. -/
theorem reachB_of_erreicht {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {w : D.Fn} (hA : AbgK P fs (reachB P fs w)) {f : D.Fn} (h : Erreicht P w f) :
    reachB P fs w f = true := by
  induction h with
  | wurzel => exact reachB_wurzel P fs w
  | ruf _ hr ih => exact abgK_ruft P hvoll hA ih hr

/-- The closure contains the computed graph. -/
theorem erreicht_of_erreichB {P : Programm D} {fs : List D.Fn} {w : D.Fn} :
    ∀ (n : Nat) {f : D.Fn}, erreichB P fs w n f = true → Erreicht P w f
  | 0, f, h => by
      have e : f = w := of_decide_eq_true h
      subst e; exact .wurzel
  | n + 1, f, h => by
      simp only [erreichB, erreichSchritt, Bool.or_eq_true, List.any_eq_true,
        Bool.and_eq_true] at h
      rcases h with h | ⟨g, _, hg, hr⟩
      · exact erreicht_of_erreichB n h
      · exact .ruf (erreicht_of_erreichB n hg) hr

theorem erreicht_of_reachB {P : Programm D} {fs : List D.Fn} {w f : D.Fn}
    (h : reachB P fs w f = true) : Erreicht P w f :=
  erreicht_of_erreichB _ h

/-- **Over closed graphs the two locality notions agree.** -/
theorem getrenntR_iff {P : Programm D} {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA : ∀ w, AbgK P fs (reachB P fs w)) (c : D.Tab ⊕ D.Glob) :
    GetrenntR P ws c ↔ Getrennt P fs ws c := by
  constructor
  · intro h w₁ h₁ w₂ h₂ hne f g hf hc hg
    exact h w₁ h₁ w₂ h₂ hne f g (erreicht_of_reachB hf) hc (erreicht_of_reachB hg)
  · intro h w₁ h₁ w₂ h₂ hne f g hf hc hg
    exact h w₁ h₁ w₂ h₂ hne f g (reachB_of_erreicht hvoll (hA w₁) hf) hc
      (reachB_of_erreicht hvoll (hA w₂) hg)

end Geteilt

/-! ## 2. The obligation with the atomic rely -/

/-- **The logic of the bodies with the atomic rely over `T`.** -/
def LogikPflichtA (P : Programm D) (S : SperrInv D) (Q : AxEns D) (T : D.Tab ⊕ D.Glob → Prop) :
    Prop :=
  (∀ (passes : Nat) (f : D.Fn),
    KoerperGutSA P passes Q S T f ∧ InvGutSA P passes Q S T f ∧ InvGutGrundA P passes Q S T f) ∧
  SperrInvLokal S ∧ AxEnsLokal Q

/-- **The user's own logic with the atomic rely**: the rely over the unit's shared atomics. -/
structure NutzerPflichtA [DecidableEq D.Fn] (E : Einheit D) : Prop where
  logik : LogikPflichtA E.P E.S E.Q (GeteiltA E.P E.ws)
  start : StartPflicht E

/-! ## 3. The embedding -/

section Einbettung

variable {P : Programm D} {S : SperrInv D} {Q : AxEns D} {T : D.Tab ⊕ D.Glob → Prop}
  {passes : Nat} {f : D.Fn}

/-- **The new obligation implies the old**, for every body: the identity environment is in the
    class and runs `execStmtH` (visibility local, `RegLokal`). -/
theorem koerperGutS_of_A (h : KoerperGutSA P passes Q S T f) : KoerperGutS P passes Q S f := by
  refine ⟨fun O' hr hl hq U hU R hR hOV σ ρ hreq => ?_, fun O' hr hl hq U hU R hR hOL σ ρ hreq => ?_⟩
  · have h1 := h.1 O' hr hl hq U hU idA (havocA_id T) R hR hOV σ ρ hreq
    rw [execEndHA_id P S O' U passes R hl.2, execEndHA_id P S O' U passes (torRuf P R) hl.2] at h1
    exact h1
  · have h1 := h.2 O' hr hl hq U hU idA (havocA_id T) R hR hOL σ ρ hreq
    rw [execEndHA_id P S O' U passes R hl.2] at h1
    exact h1

theorem invGutS_of_A (h : InvGutSA P passes Q S T f) : InvGutS P passes Q S f := by
  intro O' hr hl hq U hU R hR hOV σ ρ hreq σ' v he
  refine h O' hr hl hq U hU idA (havocA_id T) R hR hOV σ ρ hreq σ' v ?_
  rw [execEndHA_id P S O' U passes R hl.2]
  exact he

theorem invGutGrund_of_A (h : InvGutGrundA P passes Q S T f) : InvGutGrund P passes Q S f := by
  intro O' hr hl hq U hU R hR hOV σ ρ hreq σ' r he
  refine h O' hr hl hq U hU idA (havocA_id T) R hR hOV σ ρ hreq σ' r ?_
  rw [execEndHA_id P S O' U passes R hl.2]
  exact he

/-- **(b) with the rely implies (b)**, on every unit. -/
theorem logikPflicht_of_A (h : LogikPflichtA P S Q T) : LogikPflicht P S Q :=
  ⟨fun pa f => ⟨koerperGutS_of_A (h.1 pa f).1, invGutS_of_A (h.1 pa f).2.1,
    invGutGrund_of_A (h.1 pa f).2.2⟩, h.2.1, h.2.2⟩

/-- A body none of whose reads is in `T`. -/
def LiestNicht (P : Programm D) (T : D.Tab ⊕ D.Glob → Prop) (f : D.Fn) : Prop :=
  ∀ c ∈ endblockOrteP P (P.rumpf f), ¬ T c

theorem koerperGutSA_of_frei (hf : LiestNicht P T f) (h : KoerperGutS P passes Q S f) :
    KoerperGutSA P passes Q S T f := by
  refine ⟨fun O' hr hl hq U hU A hA R hR hOV σ ρ hreq => ?_,
    fun O' hr hl hq U hU A hA R hR hOL σ ρ hreq => ?_⟩
  · rw [Endblock.execHA_frei P S O' U A passes R hA hl.2 _ hf,
      Endblock.execHA_frei P S O' U A passes (torRuf P R) hA hl.2 _ hf]
    exact h.1 O' hr hl hq U hU R hR hOV σ ρ hreq
  · rw [Endblock.execHA_frei P S O' U A passes R hA hl.2 _ hf]
    exact h.2 O' hr hl hq U hU R hR hOL σ ρ hreq

theorem invGutSA_of_frei (hf : LiestNicht P T f) (h : InvGutS P passes Q S f) :
    InvGutSA P passes Q S T f := by
  intro O' hr hl hq U hU A hA R hR hOV σ ρ hreq σ' v he
  rw [Endblock.execHA_frei P S O' U A passes R hA hl.2 _ hf] at he
  exact h O' hr hl hq U hU R hR hOV σ ρ hreq σ' v he

theorem invGutGrundA_of_frei (hf : LiestNicht P T f) (h : InvGutGrund P passes Q S f) :
    InvGutGrundA P passes Q S T f := by
  intro O' hr hl hq U hU A hA R hR hOV σ ρ hreq σ' r he
  rw [Endblock.execHA_frei P S O' U A passes R hA hl.2 _ hf] at he
  exact h O' hr hl hq U hU R hR hOV σ ρ hreq σ' r he

/-- **(b) implies (b) with the rely, on a unit whose bodies read no carrier of `T`.** -/
theorem logikPflichtA_of_frei (hf : ∀ f, LiestNicht P T f) (h : LogikPflicht P S Q) :
    LogikPflichtA P S Q T :=
  ⟨fun pa f => ⟨koerperGutSA_of_frei (hf f) (h.1 pa f).1, invGutSA_of_frei (hf f) (h.1 pa f).2.1,
    invGutGrundA_of_frei (hf f) (h.1 pa f).2.2⟩, h.2.1, h.2.2⟩

end Einbettung

section Akzeptiert

variable [DecidableEq D.Fn]

/-- **Every unit the goal's checker accepts reads no shared atomic**: an unguarded footprint
    carrier of an accepted unit is thread-local (`fuss`), and so not shared. -/
theorem akzeptiert_liest_nicht_geteilt {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec P S fs ws) (f : D.Fn) :
    LiestNicht P (GeteiltA P ws) f := by
  intro c hc ⟨_, hB, hG⟩
  have hc' : c ∈ fussOrte P f := fuss_rumpf P f hc
  rcases (hA.fuss f).1 c hc' with h | ⟨L, hL, _⟩
  · simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨L, hL, _⟩ := sigB_ok h
      exact hB L hL
    · have hG' : Getrennt P fs ws c :=
        @of_decide_eq_true _ (Classical.propDecidable _) h
      exact hG ((getrenntR_iff hvoll hA.abg c).mpr hG')
  · exact hB L hL

/-- **On every accepted unit the two obligations are EQUIVALENT.** -/
theorem logikPflichtA_iff_akzeptiert {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec P S fs ws) :
    LogikPflichtA P S Q (GeteiltA P ws) ↔ LogikPflicht P S Q :=
  ⟨logikPflicht_of_A, logikPflichtA_of_frei (akzeptiert_liest_nicht_geteilt hvoll hA)⟩

/-- `NutzerPflichtA` implies `NutzerPflicht` on every unit, and on an accepted unit the converse. -/
theorem nutzerPflicht_of_A {E : Einheit D} (h : NutzerPflichtA E) : NutzerPflicht E :=
  ⟨logikPflicht_of_A h.logik, h.start⟩

theorem nutzerPflichtA_of_akzeptiert {E : Einheit D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA : AkzeptiertSpec E.P E.S fs E.ws) (h : NutzerPflicht E) : NutzerPflichtA E :=
  ⟨(logikPflichtA_iff_akzeptiert hvoll hA).mpr h.logik, h.start⟩

end Akzeptiert

#print axioms Gabbro.Grammatik.Zielsatz.getrenntR_iff
#print axioms Gabbro.Grammatik.Zielsatz.logikPflicht_of_A
#print axioms Gabbro.Grammatik.Zielsatz.logikPflichtA_of_frei
#print axioms Gabbro.Grammatik.Zielsatz.akzeptiert_liest_nicht_geteilt
#print axioms Gabbro.Grammatik.Zielsatz.logikPflichtA_iff_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.nutzerPflichtA_of_akzeptiert

end Gabbro.Grammatik.Zielsatz
