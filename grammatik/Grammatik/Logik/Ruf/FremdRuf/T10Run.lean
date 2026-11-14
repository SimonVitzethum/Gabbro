/- C08: the call-site duty over reachable machine runs. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T10
public import Grammatik.Speichermodell.Maschine.GXMaschine
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.Fremd

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- A recorded key occurs at a reachable foreign-call head, on a memory the
    atomic rely may present. This does not assert anything about the answer.

    U5: use GX reachability with the unit's actual shared-atomic rely, rather
    than a chosen `SegLauf` or GA's strictly larger set of presented memories.
    `laufG_erreichbar`/`gx_aus_g_lauf` cover G; `fadenErreichbarX_GX` forgets
    spawn/join steps, and the closure underlying `SegLaufX` is exactly GX.
    Unlike `RennfreiBisGA`, a pre may depend on a thread-local atomic, so GA
    would impose duties at extra, unreachable calls. The extra
    presented memory is essential: GX evaluates arguments there, not in the
    stored memory. Spawn/join leave the G state unchanged. Thus the same
    predicate can be quantified in `NutzerPflicht` and `NutzerPflichtA`.
    Histories from one run (and their frame/thread restrictions) provide this
    reachability fact for each key; no arbitrary answer or uncalled arguments
    acquire a precondition obligation. -/
def CallSiteErreichbar (P : Programm D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) (key : ForeignCallKey D) : Prop :=
  ∃ (M : RufMaschineG D) (sp : Speicher D) (t : Faden),
    RufErreichbarGX P O passes Tg M0 M ∧
    (∀ c, ¬ Tg c → TraegerGleich sp M.speicher c) ∧
    (mitSpeicher M sp).foreignCallKey t = some key

/-- The pre at every reachable software-call head, including calls whose
    decoder fails or whose binding has no normal answer. -/
def CallSitePflichtLauf (P : Programm D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)),
    CallSiteErreichbar P O passes Tg M0 ⟨a, σ, ρ⟩ →
    D.axHerkunft a = some AxOrigin.software → AxVor P.axVertrag a σ ρ

/-- The unit duty, ready to become user premise (b): every budget and every
    declared runtime start, over the actual idle-root extension used by the
    goal theorem. The binding's conditional contract and the hardware part
    are the rely: quantifying over arbitrary, contract-breaking bindings would
    incorrectly forbid using an earlier call's proved post at a later call.
    No unconditional software ensures is assumed. `H` is the binding's
    boundary history, not the replay history of axiom answers. This module
    does not yet add the duty to the goal statement. -/
def CallSitePflicht [DecidableEq D.Fn] (E : Einheit D) : Prop :=
  ∀ (O : Orakel D) (H : List (BoundaryRecord D)),
    HardwareAnnahmenHw O E.Q → ForeignPflicht E O H →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
    Laufzeit E sp init →
    CallSitePflichtLauf E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init)

/-- Project the run duty to the replay history. The integration proof supplies
    occurrence of each recorded key; T10 separately requires `PasstA` at the
    stored key and `SchluesselHerkunft`. No extra question is added to a key.
    `HA'` can be a frame's or thread's restriction of the recorded history. -/
theorem callSitePflichtFremd_of_run {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop} {M0 : RufMaschineG D}
    (h : CallSitePflichtLauf P O passes Tg M0)
    {HA HA' : List (AxEintrag D)}
    (hrecord : ∀ e ∈ HA, CallSiteErreichbar P O passes Tg M0 ⟨e.1, e.2.1, e.2.2.1⟩)
    (hsub : ∀ e ∈ HA', e ∈ HA) : CallSitePflichtFremd P.axVertrag HA' := by
  apply callSitePflichtFremd_mono (HA := HA)
  · intro a σ ρ x hmem hsw
    exact h a σ ρ (hrecord _ hmem) hsw
  · exact hsub

/-- Specialization to the unit's declared runtime, including its idle root. -/
theorem CallSitePflicht.fremd [DecidableEq D.Fn] {E : Einheit D} (h : CallSitePflicht E)
    {O : Orakel D} {H : List (BoundaryRecord D)}
    (hh : HardwareAnnahmenHw O E.Q) (hf : ForeignPflicht E O H)
    (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hl : Laufzeit E sp init) {HA : List (AxEintrag D.mitRuhe)}
    (hrecord : ∀ e ∈ HA, CallSiteErreichbar E.P.mitRuhe O.mitRuhe passes
      (GeteiltV (D := D) E.P E.ws) (RufStartG E.P.mitRuhe sp init) ⟨e.1, e.2.1, e.2.2.1⟩) :
    CallSitePflichtFremd E.P.mitRuhe.axVertrag HA :=
  callSitePflichtFremd_of_run (h O H hh hf passes sp init hl) hrecord (fun _ hm => hm)

/-- A software-free declaration owes no foreign pre, even with a nonempty
    hardware history. For the empty history this specializes to T10's nil case. -/
theorem callSitePflichtLauf_ohne {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop} {M0 : RufMaschineG D}
    (h : ∀ a : D.Ax, D.axHerkunft a ≠ some AxOrigin.software) :
    CallSitePflichtLauf P O passes Tg M0 :=
  fun a _ _ _ hsw => absurd hsw (h a)

/-- Software-free units owe no call-site precondition, on G or GX. -/
theorem callSitePflicht_ohne [DecidableEq D.Fn] (E : Einheit D)
    (h : ∀ a : D.Ax, D.axHerkunft a ≠ some AxOrigin.software) : CallSitePflicht E := by
  intro O H hh hf passes sp init hl
  exact callSitePflichtLauf_ohne h

/-- The key of any call in an indexed G run is in the duty's domain. -/
theorem callSiteErreichbar_of_laufG {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop}
    {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hr : LaufG P O passes M0 ms fs n) {i : Nat} (hi : i ≤ n)
    {t : Faden} {key : ForeignCallKey D} (hk : (ms i).foreignCallKey t = some key) :
    CallSiteErreichbar P O passes Tg M0 key := by
  refine ⟨ms i, (ms i).speicher, t, gx_aus_g_lauf (laufG_erreichbar hr i hi),
    fun c _ => traegerGleich_refl _ c, ?_⟩
  rw [mitSpeicher_selbst]
  exact hk

/-- GX supplies both reachability and the presented memory at the call site. -/
theorem callSiteErreichbar_of_gx {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} {Tg : D.Tab ⊕ D.Glob → Prop}
    (hr : RufErreichbarGX P O passes Tg M0 M) {sp : Speicher D}
    (hp : ∀ c, ¬ Tg c → TraegerGleich sp M.speicher c)
    {t : Faden} {key : ForeignCallKey D}
    (hk : (mitSpeicher M sp).foreignCallKey t = some key) :
    CallSiteErreichbar P O passes Tg M0 key :=
  ⟨M, sp, t, hr, hp, hk⟩


/-! ## The actual binding in the conditional class (C08 R3b) -/

/-- **(2) The actual software binding inhabits the body duties' class.** At a question
    world `σ0.fragt (.inl a)` whose pre holds, a software item's answer meets its post
    (`ForeignVertrag`, the pre read through `axVor_fragt`) and so its summary
    (`PostDeckt`); every other item meets its summary unconditionally (`AxVertragOHw`).
    Worlds without the question are never asked, and the class asks nothing there. -/
theorem axVertragOP_of_binding {E : Einheit D} {O : Orakel D} (hf : ForeignVertrag E O)
    (hp : PostDeckt E) (hh : AxVertragOHw E.Q O) : AxVertragOP (PreQ E.P) E.Q O := by
  intro a σ0 ρ v hpre hv
  by_cases hsw : D.axHerkunft a = some AxOrigin.software
  · rw [preQ_sw E.P hsw] at hpre
    have hvor : AxVor E.P.axVertrag a σ0 ρ := (axVor_fragt E.P.axVertrag a σ0 ρ).mpr hpre
    exact hp a hsw σ0 ρ _ v (hf.1 a hsw σ0 ρ hvor v hv)
  · exact hh a hsw (σ0.fragt (.inl a)) ρ v hv

/-- **The run asks only where the duties hold.** Under the call-site duty, every question
    of a reachable head is a question world whose interface pre holds (software) or one
    with no pre (hardware), so the class gives the answer fact at every reachable question:
    the oracle rely the replay records. -/
theorem antwortQLauf_of_callSite {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}
    {Tg : D.Tab ⊕ D.Glob → Prop} {M0 : RufMaschineG D} (hQ : AxVertragOP (PreQ P) Q O)
    (hCS : CallSitePflichtLauf P O passes Tg M0) : AntwortQLauf P O passes Q Tg M0 := by
  intro M hr σ hσ t a σ1 ρ hk v hv
  refine hQ a σ1 ρ v ?_ hv
  by_cases hsw : D.axHerkunft a = some AxOrigin.software
  · rw [preQ_sw P hsw]
    exact hCS a (σ1.fragt (.inl a)) ρ ⟨M, σ, t, hr, hσ, hk⟩ hsw
  · exact preQ_hw P hsw _ ρ

/-- The call-site duty and the binding give the replay's whole oracle rely. -/
theorem relyQ_of_callSite {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}
    {Tg : D.Tab ⊕ D.Glob → Prop} {M0 : RufMaschineG D} (hQ : AxVertragOP (PreQ P) Q O)
    (hCS : CallSitePflichtLauf P O passes Tg M0) : RelyQ P O passes Q Tg M0 :=
  ⟨hQ, antwortQLauf_of_callSite hQ hCS⟩
end Gabbro.Grammatik
