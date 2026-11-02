module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineD.Teil2Basis
import all Grammatik.Logik.Ruf.Maschine.RufMaschineD.Teil2Basis

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
public import Grammatik.Logik.Ruf.Maschine.RufMaschineD.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
/-- Step 1 as reachability: start, then one step. -/
theorem rufReach1D :
    RufErreichbarD rufPD rufOD 0 rufCallerMD rufM1D := by
  exact RufErreichbarD.schritt _ _ 0 RufErreichbarD.start rufSchritt1D

/-- The thread world after step 1 is the empty world: no reads, no writes. -/
theorem rufM1WeltD : rufM1D.weltVon 0 = rufWeltD := by rfl

/-- The machine after step 2: caller restored, return logged after the entry.
    Step 2 fires the `rueck` rule: the callee residue is `ret` of param+1;
    no reads, so the return world is the thread world and the value is 3.
    Every premise is used: `hpop`/`hhead`/`hfg`/`hrho`/`hs0` select the head
    frame, `hΛ` the lock state, `hs1`/`hv`/`hneu` feed the constructor. -/
def rufM2D : RufMaschineD rufD :=
  ⟨(rufWeltD.speicher),
   rufUpdateD rufM1D.faeden 0
     ⟨[], rufCallerD, rufWeltD.spur,
      [RufEreignisD.rueck rufIncD rufRhoD rufVD (rufCallerMD.weltVon 0) rufWeltD] ++
        (rufM1D.faeden 0).log⟩,
   rufM1D.lauf ++ rufEigenD 0 [],
   rufM1D.start⟩

theorem rufSchritt2D : RufSchrittD rufPD rufOD 0 rufM1D 0 rufM2D := by
  have hpop : (rufM1D.faeden 0).stapel = [rufCallerD] := rfl
  have hhead : (rufM1D.faeden 0).kopf.rest =
      ⟨false, rufD.params rufIncD,
        Signatur.anfang rufD (rufD.signatur rufIncD),
        .ret rufRetED (by decide : (Signatur.anfang rufD (rufD.signatur rufIncD)).Perm
          (vertragVon rufD rufIncD).ende)⟩ :=
    rfl
  have hfg : (rufM1D.faeden 0).kopf.f = rufIncD := rfl
  have hrho : (rufM1D.faeden 0).kopf.rho = hfg ▸ rufRhoD := rfl
  have hs0 : (rufM1D.faeden 0).kopf.s0 = rufCallerMD.weltVon 0 := rfl
  have hΛ : HeldGenau (Signatur.anfang rufD (rufD.signatur rufIncD))
      (offen (rufM1D.faeden 0).spur) :=
    rufHeldLeerD _
  have hs1 : rufWeltD = (rufM1D.weltVon 0).lese
      (Signatur.anfang rufD (rufD.signatur rufIncD)) (ErgExpr.orte rufRetED) := by
    rw [rufRetOrteLeerD, rufM1WeltD]
    rfl
  have hv : rufVD = hfg ▸ evalErg rufWeltD rufRetED rufWeltD rufRhoD :=
    rfl
  have hneu : (rufWeltD.spur) = [] ++ (rufM1D.faeden 0).spur := rfl
  exact RufSchrittD.rueck rufM1D 0 rufCallerD [] hpop _ _ _ _ _ hhead _ hfg
    rufRhoD hrho _ hs0 hΛ _ hs1 _ hv _ hneu
/-- Step 2 as reachability: two steps from the caller machine. -/
theorem rufReach2D : RufErreichbarD rufPD rufOD 0 rufCallerMD rufM2D := by
  exact RufErreichbarD.schritt _ _ 0 rufReach1D rufSchritt2D

/-- The witness log of thread 0 after both steps: entry then return. -/
theorem rufM2LogD : (rufM2D.faeden 0).log =
    [RufEreignisD.rueck rufIncD rufRhoD rufVD (rufCallerMD.weltVon 0) rufWeltD,
     RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)] := by
  rfl

/-- The witness run satisfies the place-contracts: the entry carries param 2
    (requires holds by `ruf_req_am_ortD`) and the return carries result 3
    (ensures holds by `ruf_ens_am_ortD`). Both disjuncts are used: the entry
    case by `ReqAmEintritt`, the return case by `EnsAmRueck`; `hmem` selects
    the log event. -/
theorem rufM2vertragD : VertragAmOrtMaschineD rufPD rufM2D := by
  intro f ev hmem
  have hlog : ev ∈ [RufEreignisD.rueck rufIncD rufRhoD rufVD
      (rufCallerMD.weltVon 0) rufWeltD,
      RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)] := by
    cases Decidable.em (f = 0) with
    | inl h0 =>
        subst h0
        rw [rufM2LogD] at hmem
        exact hmem
    | inr hne =>
        have hnil : (rufM2D.faeden f).log = [] := by
          show ((rufUpdateD rufM1D.faeden 0 _ f).log) = []
          rw [rufUpdateD_noteq _ _ _ hne]
          show ((rufUpdateD rufCallerMD.faeden 0 _ f).log) = []
          rw [rufUpdateD_noteq _ _ _ hne]
          rfl
        rw [hnil] at hmem
        simp only [List.not_mem_nil] at hmem
  rw [List.mem_cons, List.mem_singleton] at hlog
  rcases hlog with hlog | hlog
  · cases hlog
    refine ⟨?_, ?_⟩
    · intro g rho s0 hev
      simp only [reduceCtorEq] at hev
    · intro g rho v s0 s1 hev
      simp only [RufEreignisD.rueck.injEq] at hev
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hev
      show EnsAmRueck rufPD rufIncD (rufCallerMD.weltVon 0) rufWeltD rufRhoD rufVD
      have : rufCallerMD.weltVon 0 = rufWeltD := rfl
      rw [this]
      exact ruf_ens_am_ortD
  · cases hlog
    refine ⟨?_, ?_⟩
    · intro g rho s0 hev
      simp only [RufEreignisD.eintritt.injEq] at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      show ReqAmEintritt rufPD rufIncD (rufCallerMD.weltVon 0) rufRhoD
      have : rufCallerMD.weltVon 0 = rufWeltD := rfl
      rw [this]
      exact ruf_req_am_ortD
    · intro g rho v s0 s1 hev
      simp only [reduceCtorEq] at hev



/-! ## 10. Single-thread adequacy (memory half, `rueck` inversion) -/

/-- Adequacy, memory half: a `rueck` step from a `ret` residue moves machine
    memory to exactly the read world's memory
    (`(weltVon).lese Λ e.orte`). Stated directly on the `rueck` constructor
    (not by inversion over all steps: `nimmt`/`gibt` keep memory, so a
    step-general statement would be false). The proof reads the
    constructor's own equations: `M'` memory IS `s1.speicher` by the
    constructor, and `s1` IS the read world by `hs1`. Both `hs1` and the
    constructor equation are used. -/
theorem ruf_adäquat_speicher_rueck (M : RufMaschineD rufD) (f : Faden)
    (caller : RufRahmenD rufD) (rest : List (RufRahmenD rufD))
    (_ : (M.faeden f).stapel = caller :: rest)
    (Γ : Ctx) (Λ : List (Res rufD))
    (e : ErgExpr rufD Γ Λ (vertragVon rufD (M.faeden f).kopf.f).erg)
    (hperm : Λ.Perm (vertragVon rufD (M.faeden f).kopf.f).ende)
    (ρ : Env rufD Γ)
    (_ : (M.faeden f).kopf.rest = ⟨false, Γ, Λ, .ret e hperm⟩)
    (g : rufD.Fn) (hfg : (M.faeden f).kopf.f = g)
    (rho : Env rufD (rufD.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
    (s0 : World rufD) (hs0 : (M.faeden f).kopf.s0 = s0)
    (_ : HeldGenau Λ (offen (M.faeden f).spur))
    (s1 : World rufD)
    (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
    (v : ErgVal rufD (rufD.erg g))
    (hv : v = hfg ▸ evalErg s1 e s1 ρ)
    (neu : List (Ereignis rufD))
    (_ : s1.spur = neu ++ (M.faeden f).spur)
    (M' : RufMaschineD rufD)
    (hs : M' =
      ⟨s1.speicher,
       rufUpdateD M.faeden f
         ⟨rest, caller, s1.spur,
          (RufEreignisD.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
       M.lauf ++ rufEigenD f neu,
       M.start⟩) :
    M'.speicher = ((M.weltVon f).lese Λ e.orte).speicher ∧
      v = hfg ▸ evalErg ((M.weltVon f).lese Λ e.orte) e
        ((M.weltVon f).lese Λ e.orte) ρ ∧
      (M.faeden f).kopf.rho = hfg ▸ rho ∧ (M.faeden f).kopf.s0 = s0 := by
  subst hs
  rw [hs1]
  refine ⟨rfl, ?_, hrho, hs0⟩
  rw [hs1] at hv
  exact hv

/-! ## CUTS -/

/-! ## CUTS:
  - `rufOffenD` is an unused auxiliary (stack-shape projection, never wired
    into a theorem); kept as documentation of the open-call shape.
  - Single-thread adequacy is NOT proved: the `rueck` rule changed during
    construction (`neu : List (Ereignis D)` + `hneu`), and the adequacy
    statement above was drafted against an older shape and reduced to `True`.
    What holds instead, proved: `rufM1WeltD` (empty thread world after the
    call step) and the definitional return facts `rufRetOrteLeerD`,
    `rufRetWertD` (value 3 = 2 + 1 by `rfl`).
  - Multi-step `RufErreichbarD` preservation of `RufLogPasstD` (log invariant
    along generated runs) is open: TARGET A is proved for well-formed logs
    (`rufLogPasstD_gedeckt`), but the bridge from `RufSchrittD` preservation
    to `RufErreichbarD` is not wired.
  - `blatt` never advances the residue (by design, partial machine): only
    `ruf`/`rueck` move frames; straight-line bodies other than single `ret`
    do not reduce. Full continuation threading (`ite` arms, loop resumption)
    stays open, as in the PC machine remainder.
  - Memory moves on writes through `execStmt` by construction (the `blatt`
    rule carries `hstep` with `keinRuf`); no separate moves-lemma is proved
    in this file (see `schreibt_wirkt_*`, `gen_write_glob_moves` in
    Maschine.lean for the shared-memory facts this design reuses).
-/

#print axioms Gabbro.Grammatik.rufLogPasstD_gedeckt
#print axioms Gabbro.Grammatik.rufLogPasstD_eintritt_mem
#print axioms Gabbro.Grammatik.rufLogPasstD_mem_eintritt
#print axioms Gabbro.Grammatik.rufM2vertragD
#print axioms Gabbro.Grammatik.rufSchritt1D
#print axioms Gabbro.Grammatik.rufSchritt2D
#print axioms Gabbro.Grammatik.rufReach2D
#print axioms Gabbro.Grammatik.ruf_adäquat_speicher_rueck

end Gabbro.Grammatik
