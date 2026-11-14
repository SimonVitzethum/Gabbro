/-
  Semantic witnesses of the atomic-rely model: the stale read is covered by
  GX and cannot be a G step. No concrete-checker acceptance is asserted.
-/
module
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge
public import Grammatik.Zielsatz.Atomar.BeweisAtomar
@[expose] public section


namespace Gabbro.Grammatik.AtomarXZeuge

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge

local instance : DecidableEq nD.Ax := inferInstanceAs (DecidableEq Empty)


/-- `ZielX` at every machine GX reaches from configuration 1's start. -/
theorem n1_zielX [RootNativeFloat.Hardware] (sp : Speicher nD) (passes : Nat) (M : RufMaschineG nD)
    (hX : RufErreichbarGX nP nO passes (GeteiltV nP n1ws) (RufStartG nP sp init1) M) :
    ZielX nP SchwachZeuge.nS nO passes (GeteiltV nP n1ws) (RufStartG nP sp init1) M :=
  zielX_aus nP SchwachZeuge.nS (axWahr nD) nFs_voll (ls := []) (fun L => nomatch L) n1ws n1_specX
    (n1_logikA _) nO ⟨nO_gut, nO_lokal, axVertragO_wahr nO, inferInstance⟩ passes sp init1
    (AtomarZeuge.n1_start sp) M hX

/-- **NON-DEGENERATE: the stale read is a covered GX step, and no G step.** After `kern` wrote
    `konfig := 3` (the machine `W1.g`, reached by GX), W lets `hauptA` store the initial `konfig`
    (0) into `tabA[0]`; that step is a GX step over the admitted shared atomics, every leg of
    `ZielX` holds at the machine it reaches, and no G step of `hauptA` from the same machine
    stores 0 there. -/
theorem n1_stale_x [RootNativeFloat.Hardware] (ord : nD.Glob → Ordnung) :
    ∃ W1 W2 : RufMaschineW nD,
      RufErreichbarGX nP nO 0 (GeteiltV nP n1ws) (RufStartG nP sp0 init1) W1.g ∧
      RufSchrittGX nP nO 0 (GeteiltV nP n1ws) W1.g 0 W2.g ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (W2.g.speicher.slots NTab.tabA 0 ()).n = 0 ∧
      (∀ M', RufSchrittG nP nO 0 W1.g 0 M' → (M'.speicher.slots NTab.tabA 0 ()).n = 3) ∧
      ZielX nP SchwachZeuge.nS nO 0 (GeteiltV nP n1ws) (RufStartG nP sp0 init1) W2.g := by
  obtain ⟨W1, W2, hW1, hs, hg1, hk, hA, _⟩ := SchwachZeuge.w_nicht_sc ord
  have hX1 := (n1_ziel_atomar sp0 ord 0 W1 hW1).erreicht
  obtain ⟨σ, M'', wahl, neu, h⟩ := hs
  have hGX := ((n1_zielX sp0 0 W1.g hX1).schwach ord W1 W2 0 σ M'' wahl neu hW1 rfl h).1
  have hX2 : RufErreichbarGX nP nO 0 (GeteiltV nP n1ws) (RufStartG nP sp0 init1) W2.g :=
    .schritt _ _ _ hX1 hGX
  refine ⟨W1, W2, hX1, hGX, hk, hA, fun M' hs' => ?_, n1_zielX sp0 0 W2.g hX2⟩
  rw [hg1] at hs'
  exact SchwachZeuge.g_schritt_0 hs'

/-- **GX strictly contains G on the semantic flag fixture**: the stale step is a GX step and no G
    step. -/
theorem n1_gx_nicht_g [RootNativeFloat.Hardware] :
    ∃ M M' : RufMaschineG nD,
      RufErreichbarGX nP nO 0 (GeteiltV nP n1ws) (RufStartG nP sp0 init1) M ∧
      RufSchrittGX nP nO 0 (GeteiltV nP n1ws) M 0 M' ∧ ¬ RufSchrittG nP nO 0 M 0 M' := by
  obtain ⟨W1, W2, hX1, hGX, _, hA, hG, _⟩ := n1_stale_x (fun _ => Ordnung.entspannt)
  refine ⟨W1.g, W2.g, hX1, hGX, fun hs => ?_⟩
  have := hG _ hs
  omega

#print axioms n1_stale_x
#print axioms n1_gx_nicht_g

end Gabbro.Grammatik.AtomarXZeuge
