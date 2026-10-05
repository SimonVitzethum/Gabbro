/-
  File:      Grammatik/X86/PipelineLoadedAll.lean
  Subject:   Loaded-image correctness for the spill, call, table, float
              and work pipeline fragments (lane 1199).

  Follow-up of lanes 1161, 1165, 1189, 1191, 1159: their theorems run
  on constructed decodings or model code regions, not on the loaded
  image with relocations. Here each fragment family gets its
  `pipeline_correct_loaded`-shaped theorem over the checked mapping:
  the start state is the existing loader's state (`PipelineImage`
  `startZustand` over `ladung`, i.e. `geladen`), fetch runs through
  actual memory (`LoadedExecution`), W^X sits in the per-byte `CodeAt`
  (executable and not writable), and the relocation leg reuses the
  accepted `PipelineLink` patch frame plus re-decode. The block-level
  families (spill, work) share the one loaded-premise pattern
  (`imageOk`/`weltOk` projected to `CodeAt`/`LayoutSep`/`WorldRep`);
  chunk-level families (tables, calls) run from loaded memory with
  decided checks; floats honestly refuse the byte image (their
  correctness lives over `FpZustand`, never over bytes).

  Reused unchanged: `Pipeline` (`CodeAt`, `validate`,
  `pipeline_correct`, `lauf_zu_laufBytes`), `PipelineImage`
  (`startZustand`, `ladung`, `imageOk`, `weltOk`,
  `imageOk_codeAt/layoutSep/worldRep`, `codeAt_lauf`),
  `LoadedExecution` (`bildZustand`, `holeFetchAux_geladen`,
  `bildStore_schritt_speichert`), `PipelineLink`
  (`linkPatch_rahmen`, `verknuepft_rel32_schliesst`,
  witness patch/decode), `PipeSpill`, `PipelineCalls`,
  `PipelineCallsExec`, `PipelineTables`, `PipelineFloat`,
  `PipelineWork`, `PipelineWitnesses`. No second IR, no second
  source interpreter, no optimiser edit, no reserved file.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineImage
import Grammatik.X86.LoadedExecution
import Grammatik.X86.PipelineLink
import Grammatik.X86.PipelineRegAlloc
import Grammatik.X86.PipelineSpill
import Grammatik.X86.PipelineCalls
import Grammatik.X86.PipelineCallsExec
import Grammatik.X86.PipelineTables
import Grammatik.X86.PipelineFloat
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineImageWitnesses

namespace Gabbro.Grammatik.X86.PipelineLoadedAll

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipeSpill
open Gabbro.Grammatik.X86.PipelineCalls
open Gabbro.Grammatik.X86.PipelineCallsExec
open Gabbro.Grammatik.X86.PipelineTables
open Gabbro.Grammatik.X86.PipelineFloat
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineImageWitnesses
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.PipeRegAlloc

variable {D : Deklaration}

/-- Loaded code, the one generic predicate every family below runs
    from: the loaded mapping holds the bytes at the code base,
    executable and not writable (W^X, per byte). -/
def fragmentBytesGeladen (bild : Bild) (c : PipeCfg) (bytes : List Byte) : Prop :=
  CodeAt (ladung bild) (natAdresse c.codeBase) bytes

/-! ## 1. Spill family: validated bytes plus a validated spill plan,
    over the loaded image.

    The loaded premises (`validate`, `imageOk`, `weltOk`) project to
    the code premises (`CodeAt`, `LayoutSep`, `WorldRep`) of the
    accepted `spill_haelt_bedeutung`; the fetched run starts at the
    loader's state. Every premise is consumed. -/

/-- SPILL CORRECTNESS OVER THE LOADED IMAGE: the fetched byte run
    from the loader's state reaches the code end with world and
    environment represented, and no spill slot touches a source
    table, another spill slot, or a declared table extent. -/
theorem spill_correct_loaded {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (p : Profil) (bild : Bild) (c : PipeCfg)
    (ps : List (Platz D)) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (r : Rahmen) (slots : List Nat) (daten : List Nat)
    (hval : validate c (layoutVon ps) certs src bytes = true)
    (himg : imageOk p bild c ps es certs src bytes = true)
    (σ : World D) (hwelt : weltOk bild ps σ = true)
    (reg : Register → Wort) (fl : Flags) (ρ : Env D Γ)
    (hE : EnvRepr ρ reg (abbOf c))
    (hplan : spillPlanOk r slots c.codeBase bytes.length daten = true)
    (hrahmen : PipeRahmenGetrennt r (layoutVon ps))
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    (∃ n s', laufBytes n (startZustand bild c reg fl) = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf c)) ∧
    SpillVonTabellenGetrennt r slots (layoutVon ps) ∧
    (∀ i j, i ∈ slots → j ∈ slots → i ≠ j →
      Disjunkt (spillSlot r i) (spillSlot r j)) ∧
    (∀ a ∈ daten, ∀ q ∈ slots,
      a + 8 ≤ r.schlitzNat q ∨ r.schlitzNat q + 8 ≤ a) := by
  have hsep := imageOk_layoutSep p bild c ps es certs src bytes himg
  have hcode := imageOk_codeAt p bild c ps es certs src bytes himg
  have hW := imageOk_worldRep p bild c ps es certs src bytes himg σ hwelt
  have hrip : (startZustand bild c reg fl).rip = natAdresse c.codeBase := rfl
  exact spill_haelt_bedeutung c (layoutVon ps) certs src bytes r slots daten
    hval hsep hplan hrahmen O passes R σ ρ (startZustand bild c reg fl)
    hcode hrip hW hE σ' ρ' hsrc

/-- The witness spill frame holds no byte of the placement layout:
    the accepted frame-separation over `pwL` transported along the
    proved layout agreement. -/
theorem piSpillRahmen : PipeRahmenGetrennt spillR0 (layoutVon piPs) := by
  intro t k f a hloc
  cases t
  cases f
  rw [pi_layout_gleich k] at hloc
  exact spillR0_getrennt _ _ _ _ hloc

/-- JOINT WITNESS for `spill_correct_loaded`: every premise holds
    jointly on the pipeline witness program (validator, image and
    world checks by computation, entry registers, the witness spill
    plan, the transported frame separation, the REAL source run that
    changes rows 7 -> 35 and 9 -> 6); the theorem then gives the
    fetched loaded run plus slot privacy. -/
theorem spill_correct_loaded_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      validate pwCfg (layoutVon piPs) pwCerts pwSrc pwBytes = true ∧
      imageOk .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes = true ∧
      weltOk piBild piPs pwSigma = true ∧
      EnvRepr pwEnv30 (pwReg 30) (abbOf pwCfg) ∧
      spillPlanOk spillR0 spillP0 pwCfg.codeBase pwBytes.length spillD0 = true ∧
      PipeRahmenGetrennt spillR0 (layoutVon piPs) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6 ∧
      (∃ n s', laufBytes n (startZustand piBild pwCfg (pwReg 30) witnessFlags) =
          .weiter s' ∧
        s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧
        EnvRepr ρ' s'.register (abbOf pwCfg)) ∧
      SpillVonTabellenGetrennt spillR0 spillP0 (layoutVon piPs) ∧
      (∀ i j, i ∈ spillP0 → j ∈ spillP0 → i ≠ j →
        Disjunkt (spillSlot spillR0 i) (spillSlot spillR0 j)) ∧
      (∀ a ∈ spillD0, ∀ q ∈ spillP0,
        a + 8 ≤ spillR0.schlitzNat q ∨ spillR0.schlitzNat q + 8 ≤ a) := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  obtain ⟨hv0, hv1⟩ := pw_quelle_vorher
  obtain ⟨⟨n, s', hrun, hrip', hW, hE⟩, hpriv, hsep2, hdat⟩ :=
    spill_correct_loaded .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes spillR0
      spillP0 spillD0 pi_validate pi_imageOk pwSigma pi_weltOk (pwReg 30) witnessFlags
      pwEnv30 pi_envRepr30 spill_probe_pos piSpillRahmen pwO 0 pwR σ' ρ' hsrc
  exact ⟨σ', ρ', pi_validate, pi_imageOk, pi_weltOk, pi_envRepr30, spill_probe_pos,
    piSpillRahmen, hsrc, hv0, h0, hv1, h1,
    ⟨n, s', hrun, hrip', hW, hE⟩, hpriv, hsep2, hdat⟩

/- CUTS (skeleton):
   Only the shared loaded-code predicate so far. Per-family
   correctness, refusals, probes and witnesses follow in pieces.
-/

#print axioms fragmentBytesGeladen

end Gabbro.Grammatik.X86.PipelineLoadedAll
