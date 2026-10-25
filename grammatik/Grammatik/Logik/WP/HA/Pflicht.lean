import Grammatik.Logik.WP.HA.Kern
import Grammatik.Zielsatz.Kern.Spec

/-!
# GabbroV over machine G: the user's obligation as weakest preconditions

The premise (b) of the goal theorem, `NutzerPflichtA E`, is the user's logic. Per function it asks three things of the
body over `execEndHA`, for every oracle, lock move, atomic environment and call meaning in their classes: a return
meets `ensures` and the owed invariants, a reason exit meets the owed invariants, and the body ends in no `logik` stop
(no precondition stop under the gated call meaning; no stop at all under a call meaning without `logik`).
`PflichtWP` states exactly that through `wpEA`; `nutzerPflichtA_aus` assembles `NutzerPflichtA` from it and the start
obligation. So a certificate's conditional goal theorem (`gP_gabbro (hN : NutzerPflichtA gE) …`) becomes
unconditional by proofs in the calculus of `HA/Kern.lean`.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

/-- What a body owes at its exits: a return meets `ensures` and the owed invariants, a reason exit the owed
    invariants. -/
def RueckPost (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    EndAusgang (vertragVon D f) false (D.params f) → Prop := fun eo =>
  (∀ σ' v, eo = .zurueck σ' v → EnsAmRueck P f σ σ' ρ v ∧ InvAmRueck P f σ') ∧
  (∀ σ' r, eo = .why σ' r → InvAmRueck P f σ')

/-- **The obligation of one function, as weakest preconditions.** -/
def PflichtWP (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop)
    (f : D.Fn) : Prop :=
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        wpEA (V := vertragVon D f) S O' U A passes R (P.rumpf f) (RueckPost P f σ ρ) σ ρ ∧
        wpEA (V := vertragVon D f) S O' U A passes (torRuf P R) (P.rumpf f)
          (fun eo => ∀ g, eo ≠ .logik (.vorbedingung g)) σ ρ) ∧
  (∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneLogik R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        wpEA (V := vertragVon D f) S O' U A passes R (P.rumpf f) (fun eo => ∀ e, eo ≠ .logik e) σ ρ)

/-- **The three body obligations of the goal theorem follow from `PflichtWP`** (and conversely: they say the same). -/
theorem pflichten_aus_wp {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {T : D.Tab ⊕ D.Glob → Prop}
    {f : D.Fn} (h : PflichtWP P passes Q S T f) :
    KoerperGutSA P passes Q S T f ∧ InvGutSA P passes Q S T f ∧ InvGutGrundA P passes Q S T f := by
  refine ⟨⟨fun O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq => ?_, fun O' h1 h2 h3 U hU A hA R hR hOL σ ρ hreq => ?_⟩,
    fun O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq => ?_, fun O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq => ?_⟩
  · obtain ⟨hpost, hvor⟩ := h.1 O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq
    exact ⟨fun σ' v hrun => (hpost.1 σ' v hrun).1, fun g => hvor g⟩
  · exact h.2 O' h1 h2 h3 U hU A hA R hR hOL σ ρ hreq
  · exact fun σ' v hrun => ((h.1 O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq).1.1 σ' v hrun).2
  · exact fun σ' r hrun => (h.1 O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq).1.2 σ' r hrun

/-- **The user's logic of the goal theorem, from weakest preconditions.** -/
theorem logikPflichtA_aus {P : Programm D} {Q : AxEns D} {S : SperrInv D} {T : D.Tab ⊕ D.Glob → Prop}
    (h : ∀ passes f, PflichtWP P passes Q S T f) (hS : SperrInvLokal S) (hQ : AxEnsLokal Q) :
    LogikPflichtA P S Q T :=
  ⟨fun passes f => pflichten_aus_wp (h passes f), hS, hQ⟩

/-- **Premise (b) of the goal theorem, from weakest preconditions and the start obligation.** -/
theorem nutzerPflichtA_aus [DecidableEq D.Fn] (E : Zielsatz.Einheit D)
    (h : ∀ passes f, PflichtWP E.P passes E.Q E.S (GeteiltA E.P E.ws) f) (hS : SperrInvLokal E.S)
    (hQ : AxEnsLokal E.Q) (hStart : StartPflicht E) : Zielsatz.NutzerPflichtA E :=
  ⟨logikPflichtA_aus h hS hQ, hStart⟩

/-- **Conversely**: the three body obligations give `PflichtWP` -- the calculus loses nothing. -/
theorem wp_aus_pflichten {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {T : D.Tab ⊕ D.Glob → Prop}
    {f : D.Fn} (h : KoerperGutSA P passes Q S T f ∧ InvGutSA P passes Q S T f ∧ InvGutGrundA P passes Q S T f) :
    PflichtWP P passes Q S T f := by
  obtain ⟨⟨hk1, hk2⟩, hi, hg⟩ := h
  refine ⟨fun O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq => ⟨⟨?_, ?_⟩, ?_⟩,
    fun O' h1 h2 h3 U hU A hA R hR hOL σ ρ hreq => hk2 O' h1 h2 h3 U hU A hA R hR hOL σ ρ hreq⟩
  · intro σ' v hrun
    exact ⟨(hk1 O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq).1 σ' v hrun, hi O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq σ' v hrun⟩
  · intro σ' r hrun
    exact hg O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq σ' r hrun
  · exact (hk1 O' h1 h2 h3 U hU A hA R hR hOV σ ρ hreq).2

/-- **Completeness at the level of the goal theorem**: premise (b) holds EXACTLY when the body obligations hold as
    weakest preconditions, the lock invariants and axiom ensures are local, and the start obligation holds. Every true
    user logic of a certificate is provable in the calculus. -/
theorem nutzerPflichtA_iff [DecidableEq D.Fn] (E : Zielsatz.Einheit D) :
    Zielsatz.NutzerPflichtA E ↔
      (∀ passes f, PflichtWP E.P passes E.Q E.S (GeteiltA E.P E.ws) f) ∧ SperrInvLokal E.S ∧ AxEnsLokal E.Q ∧
        StartPflicht E := by
  constructor
  · intro h
    exact ⟨fun passes f => wp_aus_pflichten (h.logik.1 passes f), h.logik.2.1, h.logik.2.2, h.start⟩
  · intro ⟨h, hS, hQ, hStart⟩
    exact nutzerPflichtA_aus E h hS hQ hStart

end Gabbro.Grammatik.WP
