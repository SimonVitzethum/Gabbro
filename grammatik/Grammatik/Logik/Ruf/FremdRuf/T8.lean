/- Part 8 of `FremdRuf` (C08): the software/hardware split of the foreign premise.

   The goal theorem's premise (c) carries `AxVertragO Q O`: every answer of every
   foreign item meets the declared `ensures` `Q`. Since C08 an item has a declared
   provenance (`D.axHerkunft`): a SOFTWARE item (an OS service, a provider, a syscall
   binding) is user logic whose implementation proves its `ensures`; only a named
   HARDWARE item (or one whose provenance is still unresolved -- the reading of every
   unit written before provenance existed) remains an assumption about the machine.

   This file splits the one premise into its two parts, with no change of strength:

   * `AxVertragOHw Q O`  -- the items not declared software: hardware, named in (c);
   * `AxVertragOSw Q O`  -- the items declared software: premise (b), about the actual
                            binding `O`, proved by the user's implementation;
   * `axVertragO_of_split` -- the two together are `AxVertragO Q O`, so every proof
     that consumes the whole premise consumes the pair;
   * `HardwareAnnahmenHw` -- (c) narrowed to the hardware part (frame, register
     locality, hardware ensures);
   * `hardwareAnnahmen_of_split` -- the narrowed (c) plus the software duty is the old (c).

   `AxVertragOSwF` is the same duty in the form a recorded foreign call replays it
   (the answer world is the entry world with the question recorded), and
   `axVertragOSwF_of_foreign` derives it from the proved contract of `ForeignPflicht`
   when the contract's pre holds at every software call and its post implies `Q`.
   The general conditional form (pre proved only at the call site, `CallSitePflicht`)
   replaces the unconditional premise in the replay proofs with the C06 transport. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T6

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- **The hardware part of the foreign ensures**: every item not declared software meets
    `Q` (unresolved provenance reads as hardware, the meaning before C08). -/
def AxVertragOHw (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax), D.axHerkunft a ≠ some AxOrigin.software →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
      einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = some v →
        Q a (O.wirkt a σ ρ).1 v = true

/-- **The software part of the foreign ensures** (premise (b), about the actual binding
    `O`): every item declared software meets `Q`. Discharged by the proved
    implementation of the binding, never a hardware assumption. -/
def AxVertragOSw (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax), D.axHerkunft a = some AxOrigin.software →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
      einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = some v →
        Q a (O.wirkt a σ ρ).1 v = true

/-- The two parts are the whole premise. -/
theorem axVertragO_of_split {Q : AxEns D} {O : Orakel D} (hh : AxVertragOHw Q O)
    (hs : AxVertragOSw Q O) : AxVertragO Q O := by
  intro a σ ρ v hv
  by_cases hsw : D.axHerkunft a = some AxOrigin.software
  · exact hs a hsw σ ρ v hv
  · exact hh a hsw σ ρ v hv

theorem axVertragOHw_of_O {Q : AxEns D} {O : Orakel D} (h : AxVertragO Q O) :
    AxVertragOHw Q O :=
  fun a _ σ ρ v hv => h a σ ρ v hv

theorem axVertragOSw_of_O {Q : AxEns D} {O : Orakel D} (h : AxVertragO Q O) :
    AxVertragOSw Q O :=
  fun a _ σ ρ v hv => h a σ ρ v hv

/-- Every item is software-free (the unit of before): the software part is empty. -/
theorem axVertragOSw_ohne {Q : AxEns D} {O : Orakel D}
    (h : ∀ a : D.Ax, D.axHerkunft a ≠ some AxOrigin.software) : AxVertragOSw Q O :=
  fun a ha => absurd ha (h a)

/-- **(c) narrowed to the hardware**: the frame, the register locality and the hardware
    items' declared ensures. -/
def HardwareAnnahmenHw (O : Orakel D) (Q : AxEns D) : Prop :=
  GutO O ∧ RegLokal O ∧ AxVertragOHw Q O

/-- The narrowed hardware premise together with the software duty is the old premise. -/
theorem hardwareAnnahmen_of_split {O : Orakel D} {Q : AxEns D} (hh : HardwareAnnahmenHw O Q)
    (hs : AxVertragOSw Q O) : HardwareAnnahmen O Q :=
  ⟨hh.1, hh.2.1, axVertragO_of_split hh.2.2 hs⟩

/-- The old premise contains the narrowed one. -/
theorem hardwareAnnahmenHw_of {O : Orakel D} {Q : AxEns D} (h : HardwareAnnahmen O Q) :
    HardwareAnnahmenHw O Q :=
  ⟨h.1, h.2.1, axVertragOHw_of_O h.2.2⟩

/-- **The software duty in replay form**: at every entry world and original arguments,
    the answer of the binding in the world with the question recorded meets `Q`. -/
def AxVertragOSwF (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax), D.axHerkunft a = some AxOrigin.software →
    ∀ (σ0 : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
      einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ0.fragt (.inl a)) ρ).2 = some v →
        Q a (O.wirkt a (σ0.fragt (.inl a)) ρ).1 v = true

/-- The full-world duty is the replay duty. -/
theorem axVertragOSwF_of_Sw {Q : AxEns D} {O : Orakel D} (h : AxVertragOSw Q O) :
    AxVertragOSwF Q O :=
  fun a ha σ0 ρ v hv => h a ha (σ0.fragt (.inl a)) ρ v hv

/-- **The software duty from the proved contract**: when the contract's pre holds at every
    software call and its post implies the declared `Q`, the software foreign obligation
    gives the replay duty. -/
theorem axVertragOSwF_of_foreign {E : Einheit D} {O : Orakel D} {H : List (BoundaryRecord D)}
    (hf : ForeignPflicht E O H)
    (hpre : ∀ a : D.Ax, D.axHerkunft a = some AxOrigin.software →
      ∀ (σ0 : World D) (ρ : Env D (D.aparams a)), AxVor E.P.axVertrag a σ0 ρ)
    (hdeckt : ∀ a : D.Ax, D.axHerkunft a = some AxOrigin.software →
      ∀ (σ0 : World D) (ρ : Env D (D.aparams a)) (σ1 : World D) (v : ErgVal D (D.aerg a)),
        AxNach E.P.axVertrag a σ0 ρ σ1 v → E.Q a σ1 v = true) :
    AxVertragOSwF E.Q O :=
  fun a ha σ0 ρ v hv =>
    hdeckt a ha σ0 ρ _ v (hf.vertrag a ha σ0 ρ (hpre a ha σ0 ρ) v hv)

end Gabbro.Grammatik
