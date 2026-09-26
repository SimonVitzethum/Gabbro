/-
  File:      Grammatik/Zielsatz/AtomarGoalZeuge.lean
  Subject:   WITNESSES OF THE GOAL STATEMENT WITH THE ATOMIC RELY (Opus lane O25c, 2026-09-26):
             `gabbro_ziel` itself on the flag program, and the weak run it covers.

  * `n1E_gabbro` -- `GabbroZiel`'s conclusion on configuration 1 of the noninterference fixture
    (`kern` stores the atomic `konfig`, `hauptA`/`hauptB` read it with no lock): the concrete
    checker `akzeptiertX_pruefer` accepts the unit (the checker of before refuses it,
    `n1_alt_abgelehnt`), (b) with the rely holds (`n1E_nutzerPflichtA`), and `gabbro_ziel`
    gives `ZielFX` on every reachable thread machine over GX, from the runtime's full start.
  * `n1_stale_x` -- NON-DEGENERATE: the stale read of W (`w_nicht_sc`: after `kern` wrote
    `konfig := 3`, `hauptA` stores the INITIAL `konfig` into `tabA[0]`, where every G step of
    it stores 3, `g_schritt_0`) is a step of machine GX over the admitted shared atomics, it is
    NOT a step of G, and at the machine it reaches every leg of `ZielX` holds (`zielX_aus`). So
    the new conclusion speaks about runs the statement of before did not contain.
  * `n1_gx_nicht_g` -- the same step, as a sentence about the machines: GX strictly contains G on
    an accepted program.
-/
import Grammatik.Zielsatz.AtomarAkzeptiertZeuge
import Grammatik.Zielsatz.BeweisAtomar

namespace Gabbro.Grammatik.AtomarXZeuge

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge

/-- **`GabbroZiel` on configuration 1** (the flag): `ZielFX` on every reachable thread machine
    over GX of the runtime's full start -- every budget, every set of initially live threads. -/
theorem n1E_gabbro (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine nD.mitRuhe)
    (hK : FadenErreichbarX n1E.P.mitRuhe nO.mitRuhe passes (GeteiltV (D := nD) n1E.P n1E.ws)
      (FadenStart n1E.P.mitRuhe (speicherR n1E.sp0) (initRuhe n1E.starts) lebt0) K) :
    ZielFX n1E.P.mitRuhe n1E.S.mitRuhe nO.mitRuhe passes (GeteiltV (D := nD) n1E.P n1E.ws)
      (RufStartG n1E.P.mitRuhe (speicherR n1E.sp0) (initRuhe n1E.starts)) K :=
  gabbro_ziel akzeptiertX_pruefer nD n1E ⟨nFs, nFs_voll⟩ ⟨[], fun L => nomatch L⟩
    ⟨nCs, nCs_voll⟩
    (by show AkzeptiertX nP SchwachZeuge.nS nFs [] nCs n1ws = true; exact n1_akzeptiertX)
    n1E_nutzerPflichtA nO ⟨nO_gut, nO_lokal, axVertragO_wahr nO⟩ passes _ _ (laufzeit_voll n1E)
    lebt0 K hK

/-- The checker facts of configuration 1, as `AkzeptiertSpecX`. -/
theorem n1_specX : AkzeptiertSpecX nP SchwachZeuge.nS nFs n1ws :=
  akzeptiertSpecX_of nFs_voll (fun L => nomatch L) nCs_voll n1_akzeptiertX

/-- `ZielX` at every machine GX reaches from configuration 1's start. -/
theorem n1_zielX (sp : Speicher nD) (passes : Nat) (M : RufMaschineG nD)
    (hX : RufErreichbarGX nP nO passes (GeteiltV nP n1ws) (RufStartG nP sp init1) M) :
    ZielX nP SchwachZeuge.nS nO passes (GeteiltV nP n1ws) (RufStartG nP sp init1) M :=
  zielX_aus nP SchwachZeuge.nS (axWahr nD) nFs_voll (ls := []) (fun L => nomatch L) n1ws n1_specX
    (n1_logikA _) nO ⟨nO_gut, nO_lokal, axVertragO_wahr nO⟩ passes sp init1
    (AtomarZeuge.n1_start sp) M hX

/-- **NON-DEGENERATE: the stale read is a covered GX step, and no G step.** After `kern` wrote
    `konfig := 3` (the machine `W1.g`, reached by GX), W lets `hauptA` store the initial `konfig`
    (0) into `tabA[0]`; that step is a GX step over the admitted shared atomics, every leg of
    `ZielX` holds at the machine it reaches, and no G step of `hauptA` from the same machine
    stores 0 there. -/
theorem n1_stale_x (ord : nD.Glob → Ordnung) :
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
theorem n1_gx_nicht_g :
    ∃ M M' : RufMaschineG nD,
      RufErreichbarGX nP nO 0 (GeteiltV nP n1ws) (RufStartG nP sp0 init1) M ∧
      RufSchrittGX nP nO 0 (GeteiltV nP n1ws) M 0 M' ∧ ¬ RufSchrittG nP nO 0 M 0 M' := by
  obtain ⟨W1, W2, hX1, hGX, _, hA, hG, _⟩ := n1_stale_x (fun _ => Ordnung.entspannt)
  refine ⟨W1.g, W2.g, hX1, hGX, fun hs => ?_⟩
  have := hG _ hs
  omega

#print axioms n1E_gabbro
#print axioms n1_stale_x
#print axioms n1_gx_nicht_g

end Gabbro.Grammatik.AtomarXZeuge
