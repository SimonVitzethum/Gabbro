/-
  File:      Grammatik/Zielsatz/Atomar/Erfuellbarkeit.lean
  Subject:   SATISFIABILITY OF THE GOAL STATEMENT WITH THE ATOMIC RELY (stream E2; was the witness file of lane O25c).

  * `gabbro_ziel_atomar_erfuellbar` -- every premise of `gabbro_ziel` (call-site duties) holds jointly on
    configuration 1 of the noninterference fixture (`kern` stores the atomic `konfig`, `hauptA`/`hauptB` read
    it with no lock): the concrete checker `akzeptiertX_pruefer` accepts the unit, (b) with the rely holds, the
    software duties hold without a foreign item, (c) is the hardware part; the conclusion `ZielFX` follows on every
    reachable thread machine over GX.
  * `gabbro_ziel_atomar_schwach_erfuellbar` -- the premises are met by a run the SC statement does not contain:
    the stale read of W is a GX step and no G step, and `ZielX` holds at the machine it reaches.
  * `gx_echt_groesser` -- GX strictly contains G on an accepted program.
-/
module
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge
public import Grammatik.Zielsatz.Atomar.BeweisAtomar
@[expose] public section


namespace Gabbro.Grammatik.AtomarErfuellbarkeit

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge AtomarXZeuge

local instance : DecidableEq nD.Ax := inferInstanceAs (DecidableEq Empty)

/-- **The headline `GabbroZiel` (call-site duties) on configuration 1**: all its premises hold
    jointly; without a foreign item the software duties hold by `callSitePflicht_ohne`,
    `postDeckt_ohne` and `foreignVertrag_ohne`, and (c) is the hardware part of the full premise. -/
theorem gabbro_ziel_atomar_erfuellbar [RootNativeFloat.Hardware] (passes : Nat) (lebt0 : Faden → Bool)
    (K : FadenMaschine nD.mitRuhe)
    (hK : FadenErreichbarX n1E.P.mitRuhe nO.mitRuhe passes (GeteiltV (D := nD) n1E.P n1E.ws)
      (FadenStart n1E.P.mitRuhe (speicherR n1E.sp0) (initRuhe n1E.starts) lebt0) K) :
    ZielFX n1E.P.mitRuhe n1E.S.mitRuhe nO.mitRuhe passes (GeteiltV (D := nD) n1E.P n1E.ws)
      (RufStartG n1E.P.mitRuhe (speicherR n1E.sp0) (initRuhe n1E.starts)) [] K :=
  have hsw : ∀ a : nD.Ax, nD.axHerkunft a ≠ some AxOrigin.software := fun a => nomatch a
  gabbro_ziel akzeptiertX_pruefer nD n1E ⟨nFs, nFs_voll⟩ ⟨[], fun L => nomatch L⟩
    ⟨nCs, nCs_voll⟩
    n1E_akzeptiert
    n1E_nutzerPflichtA (callSitePflicht_ohne n1E hsw) (postDeckt_ohne n1E hsw) nO
    (foreignVertrag_ohne n1E nO hsw)
    (hardwareAnnahmenHw_of ⟨nO_gut, nO_lokal, axVertragO_wahr nO, inferInstance⟩)
    passes _ _ (laufzeit_voll n1E) lebt0 K hK

/-- `ZielX` at every machine GX reaches from configuration 1's start. -/
private theorem n1_zielX [RootNativeFloat.Hardware] (sp : Speicher nD) (passes : Nat) (M : RufMaschineG nD)
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
theorem gabbro_ziel_atomar_schwach_erfuellbar [RootNativeFloat.Hardware] (ord : nD.Glob → Ordnung) :
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

/-- **GX strictly contains G on an accepted program**: the stale step is a GX step and no G
    step. -/
theorem gx_echt_groesser [RootNativeFloat.Hardware] :
    ∃ M M' : RufMaschineG nD,
      RufErreichbarGX nP nO 0 (GeteiltV nP n1ws) (RufStartG nP sp0 init1) M ∧
      RufSchrittGX nP nO 0 (GeteiltV nP n1ws) M 0 M' ∧ ¬ RufSchrittG nP nO 0 M 0 M' := by
  obtain ⟨W1, W2, hX1, hGX, _, hA, hG, _⟩ := gabbro_ziel_atomar_schwach_erfuellbar (fun _ => Ordnung.entspannt)
  refine ⟨W1.g, W2.g, hX1, hGX, fun hs => ?_⟩
  have := hG _ hs
  omega

#print axioms gabbro_ziel_atomar_erfuellbar
#print axioms gabbro_ziel_atomar_schwach_erfuellbar
#print axioms gx_echt_groesser

end Gabbro.Grammatik.AtomarErfuellbarkeit