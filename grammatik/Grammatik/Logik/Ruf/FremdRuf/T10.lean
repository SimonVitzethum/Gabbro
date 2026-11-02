/- Part 10 of `FremdRuf` (C08): the call-site duty and its replay transport.

   `ForeignPflicht.vertrag` (T5) concludes the contract post under its pre, and
   `axVertragOSwF_of_foreign` (T8) derives the software replay duty from an
   UNCONDITIONAL pre (every software call meets `AxVor` in every world). The
   design asks for the conditional form instead: the pre proved at each call
   (`CallSitePflicht`), transported through the recorded-world replay to G/GX.

   Recorded axiom answers (`AxEintrag`) are keyed by the question-recorded world
   (the replay oracle `orakelAus` answers the record at its key; `AxVertragOSwF`
   queries `O.wirkt` at `σ.fragt (.inl a)`). So the call-site duty is stated over
   the recorded history: every software record satisfies `AxVor` at its key
   world and original arguments. `AxVor` mentions no oracle, so the duty is
   identical in G and GX; the transport below turns it, together with the proved
   `ForeignPflicht` and the machine linkage, into the software leg of
   `VertragANeu` (the recorded-post premise `orakelAus_vertrag_neu` consumes)
   and into the declared ensures at each recorded answer. The run-level fact
   that G/GX/spawn/link record the same keys is a premise (`hlink`), proved by
   the lead at integration over the machine steps. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T8

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- **The call-site duty for software foreign items (C08):** every recorded
    software call meets the interface pre at its key world and original
    arguments. Keys are question-recorded worlds, as the replay oracle uses
    them; `AxVor` is oracle-independent, so the duty is identical in G and GX. -/
def CallSitePflichtFremd (ax : ∀ a : D.Ax, CallContract D (D.asignatur a))
    (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA →
      D.axHerkunft a = some AxOrigin.software → AxVor ax a σ ρ

/-- The empty history meets the duty. -/
theorem callSitePflichtFremd_nil (ax : ∀ a : D.Ax, CallContract D (D.asignatur a)) :
    CallSitePflichtFremd ax [] :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

/-- The duty is monotone in the history: a recorded prefix (or any recorded
    subset, as G/GX/spawn/link share the same keys) inherits it. -/
theorem callSitePflichtFremd_mono {ax : ∀ a : D.Ax, CallContract D (D.asignatur a)}
    {HA HA' : List (AxEintrag D)} (h : CallSitePflichtFremd ax HA)
    (hsub : ∀ e ∈ HA', e ∈ HA) : CallSitePflichtFremd ax HA' :=
  fun _ _ _ _ hmem hsw => h _ _ _ _ (hsub _ hmem) hsw

/-- **Replay transport (software leg):** from the proved `ForeignPflicht`, the
    call-site pre at each recorded software key and the machine linkage (the
    machine answers the record at its question-recorded key), every recorded
    software answer with a decoded value meets the contract post at the recorded
    answer world. This is the software leg of `VertragANeu`, hence the premise
    `orakelAus_vertrag_neu` replays to the machine oracle. -/
theorem vertragANeu_sw_of_foreign {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} {HA : List (AxEintrag D)}
    (hf : ForeignPflicht E O H) (hpre : CallSitePflichtFremd E.P.axVertrag HA)
    (hlink : ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
      (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → D.axHerkunft a = some AxOrigin.software →
        O.wirkt a (σ.fragt (.inl a)) ρ = x)
    {a : D.Ax} {σ : World D} {ρ : Env D (D.aparams a)} {x : World D × Int}
    (hmem : (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA)
    (hsw : D.axHerkunft a = some AxOrigin.software)
    {v : ErgVal D (D.aerg a)} (hv : einpassenErg O.zeiger (D.aerg a) x.2 = some v) :
    AxNach E.P.axVertrag a σ ρ x.1 v := by
  have hpre' := hpre a σ ρ x hmem hsw
  have hlink' := hlink a σ ρ x hmem hsw
  have h2 : einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ.fragt (.inl a)) ρ).2 = some v := by
    rw [hlink']
    exact hv
  have hcon := hf.vertrag a hsw σ ρ hpre' v h2
  rw [hlink'] at hcon
  exact hcon

/-- **Declared ensures at each recorded software answer:** when the contract
    post implies the declared `Q`, the wiring above gives `Q` at the recorded
    answer world -- the per-record form of `axVertragOSwF_of_foreign`, with the
    unconditional pre replaced by the call-site duty. -/
theorem qAmDatensatz_of_foreign {E : Einheit D} {O : Orakel D}
    {H : List (BoundaryRecord D)} {HA : List (AxEintrag D)}
    (hf : ForeignPflicht E O H) (hpre : CallSitePflichtFremd E.P.axVertrag HA)
    (hlink : ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
      (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → D.axHerkunft a = some AxOrigin.software →
        O.wirkt a (σ.fragt (.inl a)) ρ = x)
    (hdeckt : ∀ (a : D.Ax), D.axHerkunft a = some AxOrigin.software →
      ∀ (σ0 : World D) (ρ : Env D (D.aparams a)) (σ1 : World D) (v : ErgVal D (D.aerg a)),
        AxNach E.P.axVertrag a σ0 ρ σ1 v → E.Q a σ1 v = true)
    {a : D.Ax} {σ : World D} {ρ : Env D (D.aparams a)} {x : World D × Int}
    (hmem : (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA)
    (hsw : D.axHerkunft a = some AxOrigin.software)
    {v : ErgVal D (D.aerg a)} (hv : einpassenErg O.zeiger (D.aerg a) x.2 = some v) :
    E.Q a x.1 v = true :=
  hdeckt a hsw σ ρ x.1 v (vertragANeu_sw_of_foreign hf hpre hlink hmem hsw hv)

end Gabbro.Grammatik
