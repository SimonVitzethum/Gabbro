/-
  File:      Grammatik/X86/PipelineImageWitnesses.lean
  Subject:   Joint non-degenerate witnesses and poison probes for
             `PipelineImage.lean`: the pipeline witness program of
             `PipelineWitnesses.lean` taken through image construction,
             the decided image check (by computation), the existing loader,
             and the fetched byte run to the defined stop -- in the success
             case and in the refusal case through the exit stub, with
             memory changes. A second program refuses with reason 1, so the
             exit register carries a nonzero reason. Since the exit stride
             (section 7) a program with TWO reasons one apart is imaged and
             both refusals run; the GENERAL completeness of the builder
             (`kompiliert_geladen`, `bildFuerP_ok`) and the entry
             (`pipeline_correct_entry`, `bildFuerP_eintritt`) are
             instantiated jointly (sections 7-9). Section 10 takes the
             WIDENED fragment (a depth-3 value, a deep check, an `ite`
             whose branches both store) through compile, validate, image,
             entry and the loaded run for BOTH branch outcomes, with poison
             probes for the new refusals.

  Reused: `PipelineWitnesses` (declaration, contract, program, certificate,
  configuration, candidate bytes, world, environments) and everything of
  `PipelineImage.lean` and `PipelineEntry.lean`. Nothing here is on the
  trust path (witness only).
-/
import Grammatik.X86.PipelineImage
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineEntry

namespace Gabbro.Grammatik.X86.PipelineImageWitnesses

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipelineEntry

set_option maxRecDepth 100000

/-! ## 1. Placements, table layout, image -/

/-- The two placed slots: row 0 at 8192, row 1 at 8200 (the addresses of
    the pipeline witness layout, now as a finite, checkable list). -/
def piPs : List (Platz pwD) := [⟨(), 0, (), 8192⟩, ⟨(), 1, (), 8200⟩]

/-- The table layout: one extent of 16 bytes at 8192, aligned to 8. -/
def piEs : List TabLayout := [{ tab := 0, basis := 8192, len := 16, ausr := 8 }]

/-- The placement layout agrees with the pipeline witness layout. -/
theorem pi_layout_gleich (k : Int) :
    (layoutVon piPs).loc () k () = pwL.loc () k () := by
  by_cases h0 : k = 0
  · subst h0; rfl
  · by_cases h1 : k = 1
    · subst h1; rfl
    · simp [layoutVon, piPs, pwL, Platz.trifft, h0, h1]
      exact ⟨fun h => absurd h.symm h0, fun h => absurd h.symm h1⟩

/-- The code validator accepts the candidate over the placement layout. -/
theorem pi_validate : validate pwCfg (layoutVon piPs) pwCerts pwSrc pwBytes = true := by
  decide

/-- The reachable reasons of the optimised witness block: only reason 0. -/
theorem pi_gruende : grundListe (optimise pwCerts pwSrc) = [0] := by decide

/-- THE IMAGE, built from the pipeline output and the initial world. -/
def piBild : Bild := bildFuer pwCfg pwCerts pwSrc pwBytes piPs pwSigma piEs

/-- The image has three sections: code, one stub, one data extent. -/
theorem pi_bild_form :
    piBild.abschnitte.length = 3 ∧ piBild.datei.length = 82 + 10 + 16 := by decide

/-- THE IMAGE CHECK ACCEPTS, by computation. -/
theorem pi_imageOk : imageOk .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes = true := by
  decide

/-- The loaded image represents the initial world, by computation. -/
theorem pi_weltOk : weltOk piBild piPs pwSigma = true := by decide

/-! ## 2. The loaded start states and the fetched runs, by computation -/

def piStart (x : Int) : Zustand := startZustand piBild pwCfg (pwReg x) witnessFlags

theorem pi_start_lesen :
    (piStart 30).speicher.bytes (natAdresse 8192) = natByte 7 ∧
      (piStart 30).speicher.bytes (natAdresse 8200) = natByte 9 ∧
      read64 (piStart 30).speicher (natAdresse 8192) = some (BitVec.ofNat 64 7) := by
  decide

/-- `x = 30`: twelve fetched steps reach the end of the code with the
    slots 35 and 6, and the thirteenth step STOPS. -/
theorem pi_lauf30 :
    ausgangRip (laufBytes 12 (piStart 30)) = some (natAdresse 4178) ∧
      ausgangByte (natAdresse 8192) (laufBytes 12 (piStart 30)) = some (natByte 35) ∧
      ausgangByte (natAdresse 8200) (laufBytes 12 (piStart 30)) = some (natByte 6) ∧
      ausgangRip (laufBytes 13 (piStart 30)) = none := by
  decide

/-- `x = 70`: nine steps reach the exit 12288 (row 0 already 75, `rax`
    still holds 70), the tenth runs the stub (`rax = 0`, stop address
    12298), the eleventh STOPS. -/
theorem pi_lauf70 :
    ausgangRip (laufBytes 9 (piStart 70)) = some (natAdresse 12288) ∧
      ausgangReg .rax (laufBytes 9 (piStart 70)) = some (intWort 70) ∧
      ausgangRip (laufBytes 10 (piStart 70)) = some (natAdresse 12298) ∧
      ausgangReg .rax (laufBytes 10 (piStart 70)) = some (intWort 0) ∧
      ausgangByte (natAdresse 8192) (laufBytes 10 (piStart 70)) = some (natByte 75) ∧
      ausgangByte (natAdresse 8200) (laufBytes 10 (piStart 70)) = some (natByte 9) ∧
      ausgangRip (laufBytes 11 (piStart 70)) = none := by
  decide

/-! ## 3. Joint witnesses of the closing theorems -/

theorem pi_envRepr30 : EnvRepr pwEnv30 (pwReg 30) (abbOf pwCfg) := pw_envRepr30

theorem pi_envRepr70 : EnvRepr pwEnv70 (pwReg 70) (abbOf pwCfg) := pw_envRepr70

/-- A represented placed slot reads back its source number. -/
theorem pi_lesen (m : Speicher) (σ : World pwD) (k : Int) (a : Nat)
    (hW : WorldRep (layoutVon piPs) m σ) (hloc : (layoutVon piPs).loc () k () = some a) (n : Int)
    (hn : (σ.slots () k ()).n = n) :
    read64 m (natAdresse a) = some (BitVec.ofNat 64 n.toNat) := by
  obtain ⟨-, -, -, hrep⟩ := hW () k () a hloc
  have := hrep 0 1000 pwHT
  unfold RepSlot zahlWort at this
  rw [this]
  show some (BitVec.ofNat 64 (σ.slots () k ()).n.toNat) = _
  rw [hn]

/-- JOINT WITNESS for `pipeline_correct_loaded`: every premise holds
    jointly (validator, image check and world check by computation, entry
    registers, the REAL source run that changes rows 7 -> 35 and 9 -> 6);
    the theorem then gives a fetched run from the LOADED image that stops
    at the code end with the memory reading 35 and 6. -/
theorem pipeline_correct_loaded_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      validate pwCfg (layoutVon piPs) pwCerts pwSrc pwBytes = true ∧
      imageOk .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes = true ∧
      weltOk piBild piPs pwSigma = true ∧
      EnvRepr pwEnv30 (pwReg 30) (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6 ∧
      ∃ n s', laufBytes n (piStart 30) = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pwCfg) ∧
        byteschritt s' = .verweigert ∧ laufBytes (n + 1) (piStart 30) = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 35) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 6) := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  obtain ⟨n, s', hrun, hrip, hW, hE, hstop, hend⟩ := pipeline_correct_loaded .p48 piBild pwCfg
    piPs piEs pwCerts pwSrc pwBytes pi_validate pi_imageOk pwSigma pi_weltOk (pwReg 30)
    witnessFlags pwEnv30 pi_envRepr30 pwO 0 pwR σ' ρ' hsrc
  refine ⟨σ', ρ', pi_validate, pi_imageOk, pi_weltOk, pi_envRepr30, hsrc, rfl, h0, rfl, h1,
    n, s', hrun, hrip, hW, hE, hstop, hend, ?_, ?_⟩
  · exact pi_lesen _ σ' 0 8192 hW rfl 35 h0
  · exact pi_lesen _ σ' 1 8200 hW rfl 6 h1

/-- JOINT WITNESS for `pipeline_refuses_loaded`: with `x = 70` the check
    fails AFTER the first store; the fetched run from the loaded image
    reaches the exit, runs the CHECKED stub, and stops at 12298 with
    `rax = 0` (it held 70 at the exit), row 0 changed to 75, row 1 kept. -/
theorem pipeline_refuses_loaded_zeuge :
    ∃ (σ' : World pwD),
      validate pwCfg (layoutVon piPs) pwCerts pwSrc pwBytes = true ∧
      imageOk .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes = true ∧
      weltOk piBild piPs pwSigma = true ∧
      EnvRepr pwEnv70 (pwReg 70) (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' ⟨0, by decide⟩ ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 75 ∧
      ∃ n s1 s', laufBytes n (piStart 70) = .weiter s1 ∧
        s1.rip = natAdresse (pwCfg.exitBase + 0) ∧
        byteschritt s1 = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.exitBase + 0 + 10) ∧
        s'.register exitReg = intWort 0 ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧
        laufBytes (n + 1) (piStart 70) = .weiter s' ∧
        byteschritt s' = .verweigert ∧ laufBytes (n + 2) (piStart 70) = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 75) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 9) := by
  obtain ⟨σ', hsrc, h0, h1⟩ := pw_quelle70
  obtain ⟨n, s1, s', hrun, hrip, hbs, hrip', hreg, hW, hrun1, hstop, hend⟩ :=
    pipeline_refuses_loaded .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_validate
      pi_imageOk pwSigma pi_weltOk (pwReg 70) witnessFlags pwEnv70 pi_envRepr70 pwO 0 pwR σ'
      ⟨0, by decide⟩ hsrc
  refine ⟨σ', pi_validate, pi_imageOk, pi_weltOk, pi_envRepr70, hsrc, rfl, h0,
    n, s1, s', hrun, hrip, hbs, hrip', hreg, hW, hrun1, hstop, hend, ?_, ?_⟩
  · exact pi_lesen _ σ' 0 8192 hW rfl 75 h0
  · exact pi_lesen _ σ' 1 8200 hW rfl 9 h1

/-- JOINT WITNESS for `pipeline_loaded_ausgang`: both outcome kinds from
    the same loaded image. -/
theorem pipeline_loaded_ausgang_zeuge :
    (∃ n s', laufBytes n (piStart 30) = .weiter s' ∧ byteschritt s' = .verweigert ∧
      ((s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
          ∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
            WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pwCfg)) ∨
        (∃ σ' r, execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .grund σ' r ∧
          s'.rip = natAdresse (exitAdr pwCfg r.val + 10) ∧
          s'.register exitReg = intWort r.val ∧
          WorldRep (layoutVon piPs) s'.speicher σ'))) ∧
    (∃ n s', laufBytes n (piStart 70) = .weiter s' ∧ byteschritt s' = .verweigert ∧
      ((s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
          ∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .ok σ' ρ' ∧
            WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pwCfg)) ∨
        (∃ σ' r, execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' r ∧
          s'.rip = natAdresse (exitAdr pwCfg r.val + 10) ∧
          s'.register exitReg = intWort r.val ∧
          WorldRep (layoutVon piPs) s'.speicher σ'))) :=
  ⟨pipeline_loaded_ausgang .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_validate
      pi_imageOk pwSigma pi_weltOk (pwReg 30) witnessFlags pwEnv30 pi_envRepr30 pwO 0 pwR,
    pipeline_loaded_ausgang .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_validate
      pi_imageOk pwSigma pi_weltOk (pwReg 70) witnessFlags pwEnv70 pi_envRepr70 pwO 0 pwR⟩

/-! ## 4. A refusal with a NONZERO reason -/

/-- The witness contract with two reasons. -/
def pw2V : Vertrag pwD := { pwV with gruende := 2 }

theorem pw2Hw : pw2V.schreibt () = true := rfl
theorem pw2HΛ : ([] : List (Res pwD)).Perm pw2V.ende := List.Perm.refl _

/-- `T[0].f = x + 5; check x < 50 else reason 1; T[1].f = 2 * 3;` -/
def pw2Src : Block pwD pw2V false pwCtx [] [] :=
  .cons (.assignSlot () () pwIdx0 pwWert0 pw2Hw pwHL)
    (.pruefung pwCheck (.retGrund ⟨1, by decide⟩ pw2HΛ)
      (.cons (.assignSlot () () pwIdx1 pwWert1 pw2Hw pwHL) .nil))

/-- The candidate: the same code, the jump now targets exit 12289. -/
def pw2Bytes : List Byte :=
  encodeAll
  [ .movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 8192), .store64 .rbx .rax (BitVec.ofNat 32 0),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (BitVec.ofNat 32 8138),
    .movImm64 .rax (intWort 6), .movImm64 .rbx (natAdresse 8200),
    .store64 .rbx .rax (BitVec.ofNat 32 0) ]

theorem pw2_validate : validate pwCfg (layoutVon piPs) pwCerts pw2Src pw2Bytes = true := by
  decide

theorem pw2_gruende : grundListe (optimise pwCerts pw2Src) = [1] := by decide

def pw2Bild : Bild := bildFuer pwCfg pwCerts pw2Src pw2Bytes piPs pwSigma piEs

theorem pw2_imageOk :
    imageOk .p48 pw2Bild pwCfg piPs piEs pwCerts pw2Src pw2Bytes = true := by decide

theorem pw2_weltOk : weltOk pw2Bild piPs pwSigma = true := by decide

def pw2Start : Zustand := startZustand pw2Bild pwCfg (pwReg 70) witnessFlags

theorem pw2_quelle70 : ∃ σ', execBlock pwO 0 pwR pw2Src pwSigma pwEnv70 =
    .grund σ' ⟨1, by decide⟩ ∧ (σ'.slots () 0 ()).n = 75 :=
  ⟨_, rfl, rfl⟩

/-- JOINT WITNESS with reason 1: the stub at 12289 loads `rax = 1`, the
    run stops at 12299, row 0 changed to 75. -/
theorem pipeline_refuses_loaded_zeuge_grund1 :
    ∃ (σ' : World pwD),
      execBlock pwO 0 pwR pw2Src pwSigma pwEnv70 = .grund σ' ⟨1, by decide⟩ ∧
      ∃ n s1 s', laufBytes n pw2Start = .weiter s1 ∧
        s1.rip = natAdresse (pwCfg.exitBase + 1) ∧
        byteschritt s1 = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.exitBase + 1 + 10) ∧
        s'.register exitReg = intWort 1 ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧
        byteschritt s' = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 75) := by
  obtain ⟨σ', hsrc, h0⟩ := pw2_quelle70
  obtain ⟨n, s1, s', hrun, hrip, hbs, hrip', hreg, hW, -, hstop, -⟩ :=
    pipeline_refuses_loaded .p48 pw2Bild pwCfg piPs piEs pwCerts pw2Src pw2Bytes pw2_validate
      pw2_imageOk pwSigma pw2_weltOk (pwReg 70) witnessFlags pwEnv70 pi_envRepr70 pwO 0 pwR σ'
      ⟨1, by decide⟩ hsrc
  exact ⟨σ', hsrc, n, s1, s', hrun, hrip, hbs, hrip', hreg, hW, hstop,
    pi_lesen _ σ' 0 8192 hW rfl 75 h0⟩

/-- The same by computation: ten steps, `rax = 1`, the eleventh stops. -/
theorem pw2_lauf70 :
    ausgangRip (laufBytes 9 pw2Start) = some (natAdresse 12289) ∧
      ausgangRip (laufBytes 10 pw2Start) = some (natAdresse 12299) ∧
      ausgangReg .rax (laufBytes 10 pw2Start) = some (intWort 1) ∧
      ausgangRip (laufBytes 11 pw2Start) = none := by
  decide

/-! ## 5. Joint witnesses of the generic helper theorems -/

theorem sepB_zeuge : sepB piPs = true ∧ LayoutSep (layoutVon piPs) :=
  ⟨by decide, sepB_sound piPs (by decide)⟩

theorem worldRep_von_zeuge :
    platzOkB (ladung piBild) piPs = true ∧ weltB (ladung piBild) piPs pwSigma = true ∧
      WorldRep (layoutVon piPs) (ladung piBild) pwSigma :=
  ⟨by decide, by decide, worldRep_von _ piPs pwSigma (by decide) (by decide)⟩

theorem codeAtB_zeuge :
    codeAtB (ladung piBild) (natAdresse 12288) (stubBytes 0) = true ∧
      CodeAt (ladung piBild) (natAdresse 12288) (stubBytes 0) ∧
      CodeAt (ladung piBild) (natAdresse pwCfg.codeBase) pwBytes :=
  ⟨by decide, codeAtB_sound _ _ _ (by decide),
    imageOk_codeAt .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_imageOk⟩

theorem layoutVon_zeuge :
    (layoutVon piPs).loc () 1 () = some 8200 ∧
      (∃ p ∈ piPs, p.trifft () 1 () = true ∧ p.a = 8200) ∧
      (∃ a, (layoutVon piPs).loc () 0 () = some a) ∧
      (∃ ht : (⟨(), 0, (), 8192⟩ : Platz pwD).t = (), (⟨(), 0, (), 8192⟩ : Platz pwD).k = 0 ∧
        cast (congrArg pwD.Feld ht) (⟨(), 0, (), 8192⟩ : Platz pwD).f = ()) :=
  ⟨rfl, layoutVon_loc piPs () 1 () 8200 rfl,
    layoutVon_some piPs () 0 () ⟨(), 0, (), 8192⟩ List.mem_cons_self (by decide),
    trifft_inv (⟨(), 0, (), 8192⟩ : Platz pwD) () 0 () (by decide)⟩

theorem imageOk_folgen_zeuge :
    (valX86 .p48 piBild = true ∧ wohlgeformt .p48 piBild = true ∧
      pwCfg.codeBase ∈ piBild.eintraege) ∧
    (((⟨(), 0, (), 8192⟩ : Platz pwD).a + 8 ≤ pwCfg.codeBase ∨
        pwCfg.codeBase + pwBytes.length ≤ (⟨(), 0, (), 8192⟩ : Platz pwD).a) ∧
      ∀ g ∈ grundListe (optimise pwCerts pwSrc),
        (⟨(), 0, (), 8192⟩ : Platz pwD).a + 8 ≤ exitAdr pwCfg g ∨
          exitAdr pwCfg g + 10 ≤ (⟨(), 0, (), 8192⟩ : Platz pwD).a) ∧
    LayoutSep (layoutVon piPs) ∧ WorldRep (layoutVon piPs) (ladung piBild) pwSigma :=
  ⟨imageOk_valX86 .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_imageOk,
    imageOk_daten_getrennt .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_imageOk _
      List.mem_cons_self,
    imageOk_layoutSep .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_imageOk,
    imageOk_worldRep .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes pi_imageOk pwSigma
      pi_weltOk⟩

theorem grund_mem_zeuge :
    ∃ σ', execBlock pwO 0 pwR (optimise pwCerts pwSrc) pwSigma pwEnv70 = .grund σ' ⟨0, by decide⟩ ∧
      (0 : Nat) ∈ grundListe (optimise pwCerts pwSrc) := by
  obtain ⟨σ', hsrc, -, -⟩ := pw_quelle70
  have hx : execBlock pwO 0 pwR (optimise pwCerts pwSrc) pwSigma pwEnv70 = .grund σ' ⟨0, by decide⟩ := by
    rw [optimise_sound pwCerts pwSrc pwO 0 pwR pwSigma pwEnv70]; exact hsrc
  exact ⟨σ', hx, grund_mem pwCfg (layoutVon piPs) pwO 0 pwR _ 0 pwProg (by decide) pwSigma
    pwEnv70 σ' ⟨0, by decide⟩ hx⟩

/-- The frame of a memory-changing run: 9 steps from the loaded start
    change row 0 but keep every permission and the stub bytes. -/
theorem rahmen_zeuge :
    ∃ s', laufBytes 9 (piStart 70) = .weiter s' ∧ ByteRahmen (piStart 70).speicher s'.speicher ∧
      CodeAt s'.speicher (natAdresse 12288) (stubBytes 0) ∧
      s'.speicher.bytes (natAdresse 8192) ≠ (piStart 70).speicher.bytes (natAdresse 8192) := by
  have h9 : (match laufBytes 9 (piStart 70) with | .weiter _ => true | .verweigert => false) =
      true := by decide
  cases hb : laufBytes 9 (piStart 70) with
  | verweigert => rw [hb] at h9; cases h9
  | weiter s' =>
    have hbyte : ausgangByte (natAdresse 8192) (laufBytes 9 (piStart 70)) = some (natByte 75) := by
      decide
    rw [hb] at hbyte
    refine ⟨s', rfl, laufBytes_rahmen 9 _ s' hb,
      codeAt_lauf 9 _ s' hb _ _ (codeAtB_sound _ _ _ (by decide)), ?_⟩
    rw [Option.some.inj hbyte]
    decide

/-- One store step keeps the frame and changes a writable byte. -/
theorem schritt_rahmen_zeuge :
    ∃ s', schritt (kanon (.store64 .rbx .rax (BitVec.ofNat 32 0))) pwStoreZ = some s' ∧
      ByteRahmen pwStoreZ.speicher s'.speicher ∧
      s'.speicher.bytes (natAdresse 8192) ≠ pwStoreZ.speicher.bytes (natAdresse 8192) := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp pw_store_lauft
  have h35 : (match schritt (kanon (.store64 .rbx .rax (BitVec.ofNat 32 0))) pwStoreZ with
      | some s => some (s.speicher.bytes (natAdresse 8192)) | none => none) = some (natByte 35) := by
    decide
  rw [hs'] at h35
  refine ⟨s', hs', schritt_rahmen _ _ _ hs', ?_⟩
  rw [Option.some.inj h35]
  decide

theorem byteschritt_rahmen_zeuge :
    ∃ s', byteschritt (piStart 30) = .weiter s' ∧ ByteRahmen (piStart 30).speicher s'.speicher := by
  cases hb : byteschritt (piStart 30) with
  | verweigert =>
    have : ausgangRip (byteschritt (piStart 30)) = some (natAdresse 4099) := by decide
    rw [hb] at this; cases this
  | weiter s' => exact ⟨s', rfl, byteschritt_rahmen _ _ hb⟩

theorem byteschritt_stop_zeuge :
    (ladung piBild).ausfuehrbar (natAdresse 12298) = false ∧
      byteschritt { piStart 70 with rip := natAdresse 12298 } = .verweigert :=
  ⟨by decide, byteschritt_stop _ (by decide)⟩

theorem slotWort_zeuge :
    slotWort (pwD.typ () ()) (pwSigma.slots () 0 ()) =
      zahlWort (cast (congrArg (Wert pwD) pwHT) (pwSigma.slots () 0 ()) : Wert pwD (.int 0 1000)) ∧
    slotWort (pwD.typ () ()) (pwSigma.slots () 0 ()) = BitVec.ofNat 64 7 :=
  ⟨slotWort_cast _ pwHT, rfl⟩

theorem byteRahmen_write64_zeuge : ByteRahmen pwMem pwMem35 ∧ pwMem35.bytes (natAdresse 8192) ≠
    pwMem.bytes (natAdresse 8192) :=
  ⟨byteRahmen_write64 pw_write35, by decide⟩

theorem byteRahmen_trans_zeuge :
    ByteRahmen pwMem pwMem35 ∧ ByteRahmen pwMem35 pwMem35 ∧ ByteRahmen pwMem pwMem35 :=
  ⟨byteRahmen_write64 pw_write35, byteRahmen_refl _,
    byteRahmen_trans (byteRahmen_write64 pw_write35) (byteRahmen_refl _)⟩

/-! ## 6. Poison probes: every one is REFUSED -/

/-- OVERLAPPING DATA AND CODE: a table extent inside the code region (row
    0 placed at 4100). The image is built honestly for it -- the check
    refuses it. -/
def piPsUeberlapp : List (Platz pwD) := [⟨(), 0, (), 4100⟩, ⟨(), 1, (), 4108⟩]
def piEsUeberlapp : List TabLayout := [{ tab := 0, basis := 4096, len := 16, ausr := 8 }]

theorem gift_ueberlapp :
    imageOk .p48 (bildFuer pwCfg pwCerts pwSrc pwBytes piPsUeberlapp pwSigma piEsUeberlapp)
      pwCfg piPsUeberlapp piEsUeberlapp pwCerts pwSrc pwBytes = false := by
  decide

/-- WRITABLE CODE: the code section made writable (and so not W^X). -/
def piBildSchreibbar : Bild :=
  { piBild with abschnitte := match piBild.abschnitte with
      | s :: rest => { s with schreibbar := true } :: rest
      | [] => [] }

theorem gift_code_schreibbar :
    imageOk .p48 piBildSchreibbar pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-- WRITABLE BUT NOT EXECUTABLE CODE: passes W^X, refused because code
    must be executable and not writable. -/
def piBildDatenCode : Bild :=
  { piBild with abschnitte := match piBild.abschnitte with
      | s :: rest => { s with schreibbar := true, ausfuehrbar := false } :: rest
      | [] => [] }

theorem gift_code_als_daten :
    imageOk .p48 piBildDatenCode pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-- MISSING EXIT STUB: the image without any stub section. -/
def piBildOhneStub : Bild := baueBild pwCfg pwBytes [] piPs pwSigma piEs

theorem gift_ohne_stub :
    imageOk .p48 piBildOhneStub pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-- TAMPERED STUB BYTE: the immediate of the stub changed from 0 to 1 --
    still a valid instruction (decode coverage passes), but it would
    report the wrong reason. Refused. -/
def piBildStubFalsch : Bild :=
  { piBild with datei := piBild.datei.set (82 + 2) (natByte 1) }

theorem gift_stub_byte :
    valX86 .p48 piBildStubFalsch = true ∧
      imageOk .p48 piBildStubFalsch pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-- TAMPERED CODE BYTE in the image (the validated bytes are untouched). -/
def piBildCodeFalsch : Bild :=
  { piBild with datei := piBild.datei.set 1 (natByte 0) }

theorem gift_code_byte :
    imageOk .p48 piBildCodeFalsch pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-- A STUB FOR THE WRONG REASON: the image carries the stub of reason 1
    where reason 0 is reachable. -/
def piBildFalscherGrund : Bild := baueBild pwCfg pwBytes [1] piPs pwSigma piEs

theorem gift_falscher_grund :
    imageOk .p48 piBildFalscherGrund pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-- OVERLAPPING PLACEMENTS: row 1 at 8196 shares bytes with row 0. -/
def piPsSep : List (Platz pwD) := [⟨(), 0, (), 8192⟩, ⟨(), 1, (), 8196⟩]

theorem gift_platz_ueberlapp :
    sepB piPsSep = false ∧
      imageOk .p48 (bildFuer pwCfg pwCerts pwSrc pwBytes piPsSep pwSigma piEs) pwCfg piPsSep
        piEs pwCerts pwSrc pwBytes = false := by decide

/-- A PLACEMENT OUTSIDE EVERY TABLE EXTENT (no data section there). -/
def piPsAussen : List (Platz pwD) := [⟨(), 0, (), 8192⟩, ⟨(), 1, (), 16384⟩]

theorem gift_platz_aussen :
    imageOk .p48 (bildFuer pwCfg pwCerts pwSrc pwBytes piPsAussen pwSigma piEs) pwCfg
      piPsAussen piEs pwCerts pwSrc pwBytes = false := by decide

/-- WRONG INITIAL WORLD: the image holds 7 in row 0, the world says 8. -/
def pwSigma8 : World pwD where
  slots := fun t k f => by
    cases t; cases f
    exact if k = 0 then (⟨8, by decide, by decide⟩ : Zahl 0 1000)
      else if k = 1 then (⟨9, by decide, by decide⟩ : Zahl 0 1000)
      else (⟨0, by decide, by decide⟩ : Zahl 0 1000)
  globs := fun g => nomatch g
  spur := []

theorem gift_welt : weltOk piBild piPs pwSigma8 = false := by decide

/-- CODE RUNNING ON: an executable byte right after the code (the code
    section extended by one byte) -- no defined stop. -/
def piBildWeiter : Bild :=
  { piBild with
    datei := pwBytes ++ [natByte 195] ++ piBild.datei.drop 82
    abschnitte := match piBild.abschnitte with
      | s :: rest => { s with dateiLen := 83, memLen := 83 } ::
          rest.map fun t => { t with dateiOff := t.dateiOff + 1 }
      | [] => [] }

theorem gift_kein_stop :
    imageOk .p48 piBildWeiter pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-- The image of the OTHER candidate (reason-1 program) does not pass for
    the reason-0 program. -/
theorem gift_fremdes_bild :
    imageOk .p48 pw2Bild pwCfg piPs piEs pwCerts pwSrc pwBytes = false := by decide

/-! ## 7. The exit stride: two reasons one apart, BOTH imaged

    The same declaration and placements, a block with TWO checks whose
    reasons are `1` and `0`, and the configuration with exit stride `16`:
    the exits are `12304` (reason 1) and `12288` (reason 0). With the
    original stride `1` they are one byte apart and no image can hold both
    stubs (`gift_stride_eins`). -/

/-- The configuration with an exit stride of 16. -/
def pw3Cfg : PipeCfg := { pwCfg with exitStride := 16 }

/-- The check `x < 60`. -/
def pw3Check : Expr pwD pwCtx [] .bool := .lt (.var .hier) (.lit 60)

/-- `T[0].f = x + 5; check x < 60 else reason 1; check x < 50 else reason 0;
    T[1].f = 2 * 3;` -/
def pw3Src : Block pwD pw2V false pwCtx [] [] :=
  .cons (.assignSlot () () pwIdx0 pwWert0 pw2Hw pwHL)
    (.pruefung pw3Check (.retGrund ⟨1, by decide⟩ pw2HΛ)
      (.pruefung pwCheck (.retGrund ⟨0, by decide⟩ pw2HΛ)
        (.cons (.assignSlot () () pwIdx1 pwWert1 pw2Hw pwHL) .nil)))

/-- The fold certificate for the last assignment. -/
def pw3Certs : List (PassKind × BlockCert) :=
  [(.fold, .rest (.rest (.rest (.head (.assignSlotValue .foldInt)))))]

/-- The lowered program (computed by the compiler; the witness only names
    it) and its bytes. -/
def pw3Prog : List Befehl := (compileProg pw3Cfg (layoutVon piPs) pw3Certs pw3Src).getD []

def pw3Bytes : List Byte := encodeAll pw3Prog

theorem pw3_compile : compile pw3Cfg (layoutVon piPs) pw3Certs pw3Src = some pw3Bytes := by
  decide

theorem pw3_laenge : pw3Bytes.length = 104 := by decide

/-- Both reasons are reachable, one apart. -/
theorem pw3_gruende : grundListe (optimise pw3Certs pw3Src) = [1, 0] := by decide

/-- The decided layout side conditions hold (stride 16 ≥ 11). -/
theorem pw3_bauOk :
    bauOk .p48 pw3Cfg [] pw3Bytes (ohneDoppel (grundListe (optimise pw3Certs pw3Src))) piPs
      piEs = true := by
  decide

/-- JOINT WITNESS for `kompiliert_geladen`: the GENERAL completeness
    theorem, not a computation, gives validator, image check and world
    check for the compiler's output. -/
theorem kompiliert_geladen_zeuge :
    validate pw3Cfg (layoutVon piPs) pw3Certs pw3Src pw3Bytes = true ∧
      imageOk .p48 (bildFuer pw3Cfg pw3Certs pw3Src pw3Bytes piPs pwSigma piEs) pw3Cfg piPs piEs
        pw3Certs pw3Src pw3Bytes = true ∧
      weltOk (bildFuer pw3Cfg pw3Certs pw3Src pw3Bytes piPs pwSigma piEs) piPs pwSigma = true :=
  kompiliert_geladen .p48 pw3Cfg piPs piEs pw3Certs pw3Src pw3Bytes pwSigma pw3_compile pw3_bauOk

/-- The same image check, cross-checked by computation. -/
theorem pw3_imageOk_rechnung :
    imageOk .p48 (bildFuer pw3Cfg pw3Certs pw3Src pw3Bytes piPs pwSigma piEs) pw3Cfg piPs piEs
      pw3Certs pw3Src pw3Bytes = true := by
  decide

def pw3Bild : Bild := bildFuer pw3Cfg pw3Certs pw3Src pw3Bytes piPs pwSigma piEs

/-- The image has four sections: code, TWO stubs, one data extent. -/
theorem pw3_bild_form : pw3Bild.abschnitte.length = 4 ∧
    (pw3Bild.abschnitte.map Abschnitt.vaddr) = [4096, 12304, 12288, 8192] := by
  decide

def pw3Start (x : Int) : Zustand := startZustand pw3Bild pw3Cfg (pwReg x) witnessFlags

/-- The source runs: `x = 30` passes both checks, `x = 55` fails the
    second (reason 0), `x = 70` the first (reason 1). -/
theorem pw3_quelle30 : ∃ σ' ρ', execBlock pwO 0 pwR pw3Src pwSigma pwEnv30 = .ok σ' ρ' ∧
    (σ'.slots () 0 ()).n = 35 ∧ (σ'.slots () 1 ()).n = 6 :=
  ⟨_, _, rfl, rfl, rfl⟩

def pwEnv55 : Env pwD pwCtx := .cons (⟨55, by decide, by decide⟩ : Zahl 0 100) .nil

theorem pw3_quelle55 : ∃ σ', execBlock pwO 0 pwR pw3Src pwSigma pwEnv55 =
    .grund σ' ⟨0, by decide⟩ ∧ (σ'.slots () 0 ()).n = 60 :=
  ⟨_, rfl, rfl⟩

theorem pw3_quelle70 : ∃ σ', execBlock pwO 0 pwR pw3Src pwSigma pwEnv70 =
    .grund σ' ⟨1, by decide⟩ ∧ (σ'.slots () 0 ()).n = 75 :=
  ⟨_, rfl, rfl⟩

theorem pw_envRepr55 : EnvRepr pwEnv55 (pwReg 55) (abbOf pwCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

/-- The fetched runs from the loaded image, by computation: reason 1 stops
    at `12304 + 10`, reason 0 at `12288 + 10`, both with `rax` the reason. -/
theorem pw3_laeufe :
    ausgangRip (laufBytes 16 (pw3Start 30)) = some (natAdresse 4200) ∧
      ausgangRip (laufBytes 17 (pw3Start 30)) = none ∧
      ausgangRip (laufBytes 10 (pw3Start 70)) = some (natAdresse 12314) ∧
      ausgangReg .rax (laufBytes 10 (pw3Start 70)) = some (intWort 1) ∧
      ausgangRip (laufBytes 11 (pw3Start 70)) = none ∧
      ausgangRip (laufBytes 14 (pw3Start 55)) = some (natAdresse 12298) ∧
      ausgangReg .rax (laufBytes 14 (pw3Start 55)) = some (intWort 0) ∧
      ausgangRip (laufBytes 15 (pw3Start 55)) = none := by
  decide

/-- JOINT WITNESS for `pipeline_correct_compiled`: from the compiler
    output alone (no image premise), the run of the loaded built image
    changes rows 7 -> 35 and 9 -> 6 and stops at the code end. -/
theorem pipeline_correct_compiled_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx), execBlock pwO 0 pwR pw3Src pwSigma pwEnv30 = .ok σ' ρ' ∧
      ∃ n s', laufBytes n (pw3Start 30) = .weiter s' ∧
        s'.rip = natAdresse (pw3Cfg.codeBase + pw3Bytes.length) ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pw3Cfg) ∧
        byteschritt s' = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 35) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 6) := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw3_quelle30
  obtain ⟨n, s', hrun, hrip, hW, hE, hstop⟩ := pipeline_correct_compiled .p48 pw3Cfg piPs piEs
    pw3Certs pw3Src pw3Bytes pw3_compile pw3_bauOk pwSigma (pwReg 30) witnessFlags pwEnv30
    pi_envRepr30 pwO 0 pwR σ' ρ' hsrc
  exact ⟨σ', ρ', hsrc, n, s', hrun, hrip, hW, hE, hstop, pi_lesen _ σ' 0 8192 hW rfl 35 h0,
    pi_lesen _ σ' 1 8200 hW rfl 6 h1⟩

/-- JOINT WITNESS for `pipeline_refuses_compiled` with BOTH reasons of
    the same image: reason 1 (`x = 70`) ends at `12314` with `rax = 1`,
    reason 0 (`x = 55`) at `12298` with `rax = 0`; row 0 changed. -/
theorem pipeline_refuses_compiled_zeuge :
    (∃ σ', execBlock pwO 0 pwR pw3Src pwSigma pwEnv70 = .grund σ' ⟨1, by decide⟩ ∧
      ∃ n s', laufBytes n (pw3Start 70) = .weiter s' ∧
        s'.rip = natAdresse (exitAdr pw3Cfg 1 + 10) ∧ s'.register exitReg = intWort 1 ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ byteschritt s' = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 75)) ∧
    (∃ σ', execBlock pwO 0 pwR pw3Src pwSigma pwEnv55 = .grund σ' ⟨0, by decide⟩ ∧
      ∃ n s', laufBytes n (pw3Start 55) = .weiter s' ∧
        s'.rip = natAdresse (exitAdr pw3Cfg 0 + 10) ∧ s'.register exitReg = intWort 0 ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ byteschritt s' = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 60)) ∧
    exitAdr pw3Cfg 1 + 10 = 12314 ∧ exitAdr pw3Cfg 0 + 10 = 12298 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · obtain ⟨σ', hsrc, h0⟩ := pw3_quelle70
    obtain ⟨n, s', hrun, hrip, hreg, hW, hstop⟩ := pipeline_refuses_compiled .p48 pw3Cfg piPs
      piEs pw3Certs pw3Src pw3Bytes pw3_compile pw3_bauOk pwSigma (pwReg 70) witnessFlags pwEnv70
      pi_envRepr70 pwO 0 pwR σ' ⟨1, by decide⟩ hsrc
    exact ⟨σ', hsrc, n, s', hrun, hrip, hreg, hW, hstop, pi_lesen _ σ' 0 8192 hW rfl 75 h0⟩
  · obtain ⟨σ', hsrc, h0⟩ := pw3_quelle55
    obtain ⟨n, s', hrun, hrip, hreg, hW, hstop⟩ := pipeline_refuses_compiled .p48 pw3Cfg piPs
      piEs pw3Certs pw3Src pw3Bytes pw3_compile pw3_bauOk pwSigma (pwReg 55) witnessFlags pwEnv55
      pw_envRepr55 pwO 0 pwR σ' ⟨0, by decide⟩ hsrc
    exact ⟨σ', hsrc, n, s', hrun, hrip, hreg, hW, hstop, pi_lesen _ σ' 0 8192 hW rfl 60 h0⟩

/-- JOINT WITNESS for `bildFuer_ok` and `bildFuerP_ok` (empty entry
    sequence) on the two-reason program. -/
theorem bildFuer_ok_zeuge :
    (imageOk .p48 (bildFuer pw3Cfg pw3Certs pw3Src (encodeAll pw3Prog) piPs pwSigma piEs) pw3Cfg
        piPs piEs pw3Certs pw3Src (encodeAll pw3Prog) = true ∧
      weltOk (bildFuer pw3Cfg pw3Certs pw3Src (encodeAll pw3Prog) piPs pwSigma piEs) piPs
        pwSigma = true) ∧
    codeAtB (ladung (bildFuerP pw3Cfg (encodeAll []) pw3Certs pw3Src (encodeAll pw3Prog) piPs
      pwSigma piEs)) (natAdresse (pw3Cfg.codeBase - (encodeAll ([] : List Befehl)).length))
      (encodeAll []) = true :=
  ⟨bildFuer_ok .p48 pw3Cfg pw3Prog piPs pwSigma piEs pw3Certs pw3Src pw3_bauOk,
    (bildFuerP_ok .p48 pw3Cfg [] pw3Prog piPs pwSigma piEs pw3Certs pw3Src pw3_bauOk).2.2⟩

/-- STRIDE ONE CANNOT IMAGE BOTH REASONS: the same program with the
    original stride `1` compiles, but its built image is REFUSED (the stub
    of reason 0 overlaps the stub of reason 1), and the layout conditions
    refuse too. -/
def pw3Cfg1 : PipeCfg := pwCfg

def pw3Bytes1 : List Byte := (compile pw3Cfg1 (layoutVon piPs) pw3Certs pw3Src).getD []

theorem gift_stride_eins :
    (compile pw3Cfg1 (layoutVon piPs) pw3Certs pw3Src).isSome = true ∧
      validate pw3Cfg1 (layoutVon piPs) pw3Certs pw3Src pw3Bytes1 = true ∧
      imageOk .p48 (bildFuer pw3Cfg1 pw3Certs pw3Src pw3Bytes1 piPs pwSigma piEs) pw3Cfg1 piPs
        piEs pw3Certs pw3Src pw3Bytes1 = false ∧
      bauOk .p48 pw3Cfg1 [] pw3Bytes1 (ohneDoppel (grundListe (optimise pw3Certs pw3Src))) piPs
        piEs = false := by
  decide

/-- A stride of 10 leaves no stop byte between the two stubs: refused. -/
theorem gift_stride_zehn :
    bauOk .p48 { pw3Cfg with exitStride := 10 } []
      ((compile { pw3Cfg with exitStride := 10 } (layoutVon piPs) pw3Certs pw3Src).getD [])
      (ohneDoppel (grundListe (optimise pw3Certs pw3Src))) piPs piEs = false := by
  decide

/-- An exit band inside the data extent: refused by the layout check. -/
theorem gift_ausgang_in_daten :
    bauOk .p48 { pw3Cfg with exitBase := 8192 } []
      ((compile { pw3Cfg with exitBase := 8192 } (layoutVon piPs) pw3Certs pw3Src).getD [])
      (ohneDoppel (grundListe (optimise pw3Certs pw3Src))) piPs piEs = false := by
  decide

/-- Overlapping placements: refused by the layout check (strict separation). -/
theorem gift_bau_platz :
    bauOk .p48 pw3Cfg [] pw3Bytes (ohneDoppel (grundListe (optimise pw3Certs pw3Src))) piPsSep
      piEs = false := by
  decide

/-- A duplicated reason gets ONE stub (`ohneDoppel`). -/
theorem ohneDoppel_probe : ohneDoppel [1, 0, 1, 2, 0] = [1, 2, 0] ∧
    (ohneDoppel [1, 0, 1, 2, 0]).Nodup ∧ (2 ∈ ohneDoppel [1, 0, 1, 2, 0] ↔ 2 ∈ [1, 0, 1, 2, 0]) :=
  ⟨by decide, ohneDoppel_nodup _, mem_ohneDoppel _ _⟩

/-! ## 8. The entry: the entry sequence establishes `EnvRepr`

    The two-reason program behind the entry sequence `mov r10, rdi` of
    the System V parameter order, a stack extent of 64 bytes at `16384`,
    and an entry state whose `r10` holds GARBAGE (999) while the parameter
    arrives in `rdi`: `EnvRepr` is FALSE at the entry and established by
    the fetched entry sequence. -/

def peN : Nat := pwCtx.length

def pePro : List Befehl := prolog pw3Cfg sysvParameter peN

def peProBytes : List Byte := encodeAll pePro

theorem pe_pro : pePro = [.movReg64 .r10 .rdi] := by decide

/-- The table extents plus a stack extent (no placement in it). -/
def peEs : List TabLayout := piEs ++ [{ tab := 1, basis := 16384, len := 64, ausr := 16 }]

def peBild : Bild := bildFuerP pw3Cfg peProBytes pw3Certs pw3Src pw3Bytes piPs pwSigma peEs

/-- Entry registers: parameter in `rdi`, garbage in `r10`, `rsp` at the
    top of the stack extent. -/
def peReg (x : Int) : Register → Wort := fun q =>
  if q = .rdi then intWort x else if q = .rsp then natAdresse 16448
  else if q = .r10 then intWort 999 else 0

def peZ (x : Int) : EintrittZustand :=
  { zustand := eintrittStart peBild pw3Cfg peProBytes.length (peReg x) witnessFlags
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := false }

theorem pe_prologOk : prologOk pw3Cfg sysvParameter peN = true := by decide

theorem pe_bauOk :
    bauOk .p48 pw3Cfg (encodeAll (prolog pw3Cfg sysvParameter pwCtx.length)) (encodeAll pw3Prog)
      (ohneDoppel (grundListe (optimise pw3Certs pw3Src))) piPs peEs = true := by
  decide

theorem pe_bedingung30 : eintrittBedingung .nolibcMain peEs 16448 (peZ 30) = true := by
  unfold eintrittBedingung
  decide

theorem pe_bedingung70 : eintrittBedingung .nolibcMain peEs 16448 (peZ 70) = true := by
  unfold eintrittBedingung
  decide

/-- JOINT WITNESS for `bildFuerP_eintritt`: the GENERAL theorem gives the
    entry-sequence check and the entry admission of the built image. -/
theorem bildFuerP_eintritt_zeuge :
    (prologImageOk peBild pw3Cfg sysvParameter peN = true ∧
      eintrittOk .p48 peBild 0 .nolibcMain (peZ 30) = true) ∧
    eintrittOk .p48 peBild 0 .nolibcMain (peZ 70) = true :=
  ⟨bildFuerP_eintritt .p48 pw3Cfg sysvParameter pw3Prog piPs pwSigma peEs pw3Certs pw3Src
    pe_prologOk pe_bauOk .nolibcMain 16448 (peReg 30) witnessFlags (peZ 30) rfl pe_bedingung30,
   (bildFuerP_eintritt .p48 pw3Cfg sysvParameter pw3Prog piPs pwSigma peEs pw3Certs pw3Src
    pe_prologOk pe_bauOk .nolibcMain 16448 (peReg 70) witnessFlags (peZ 70) rfl pe_bedingung70).2⟩

theorem pe_wohlgeformt : wohlgeformt .p48 peBild = true :=
  valX86_wohlgeformt _ _ (imageOk_teile .p48 peBild pw3Cfg piPs peEs pw3Certs pw3Src
    pw3Bytes (bildFuerP_ok .p48 pw3Cfg pePro pw3Prog piPs pwSigma peEs pw3Certs pw3Src
      pe_bauOk).1).1

theorem pe_zulassung30 :
    eintrittZulassung .p48 peBild (effBias peBild.modus) .nolibcMain (peZ 30) [] = true := by
  show (wohlgeformt .p48 peBild && eintrittOk .p48 peBild 0 .nolibcMain (peZ 30) && valTore []) =
    true
  rw [pe_wohlgeformt, bildFuerP_eintritt_zeuge.1.2]
  rfl

theorem pe_zulassung70 :
    eintrittZulassung .p48 peBild (effBias peBild.modus) .nolibcMain (peZ 70) [] = true := by
  show (wohlgeformt .p48 peBild && eintrittOk .p48 peBild 0 .nolibcMain (peZ 70) && valTore []) =
    true
  rw [pe_wohlgeformt, bildFuerP_eintritt_zeuge.2]
  rfl

theorem pe_abi (x : Int) (hx0 : 0 ≤ x) (hx1 : x ≤ 100) :
    AbiArgs sysvParameter (.cons (⟨x, hx0, hx1⟩ : Zahl 0 100) .nil : Env pwD pwCtx) (peReg x) := by
  intro lo hi v
  cases v with
  | hier => rfl
  | dort v => exact nomatch v

/-- WITHOUT the entry sequence the entry registers do NOT represent the
    environment: `r10` holds 999, not 30. -/
theorem pe_ohne_prolog : ¬ EnvRepr pwEnv30 (peReg 30) (abbOf pw3Cfg) := by
  intro h
  have := h 0 100 .hier
  revert this
  decide

/-- The fetched entry run by computation: one step later `r10 = 30`,
    seventeen steps reach the code end, the eighteenth stops. -/
theorem pe_lauf :
    (peZ 30).zustand.rip = natAdresse 4093 ∧
      ausgangRip (laufBytes 1 (peZ 30).zustand) = some (natAdresse 4096) ∧
      ausgangReg .r10 (laufBytes 1 (peZ 30).zustand) = some (intWort 30) ∧
      ausgangRip (laufBytes 17 (peZ 30).zustand) = some (natAdresse 4200) ∧
      ausgangRip (laufBytes 18 (peZ 30).zustand) = none := by
  decide

/-- JOINT WITNESS for `pipeline_correct_entry`: an admitted entry whose
    `r10` is garbage; the theorem's premises hold jointly WITHOUT any
    `EnvRepr` premise; the run changes rows 7 -> 35 and 9 -> 6 and keeps
    the stack word readable and writable. -/
theorem pipeline_correct_entry_zeuge :
    ¬ EnvRepr pwEnv30 (peReg 30) (abbOf pw3Cfg) ∧
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx), execBlock pwO 0 pwR pw3Src pwSigma pwEnv30 = .ok σ' ρ' ∧
      ∃ n s', laufBytes n (peZ 30).zustand = .weiter s' ∧
        s'.rip = natAdresse (pw3Cfg.codeBase + pw3Bytes.length) ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pw3Cfg) ∧
        byteschritt s' = .verweigert ∧
        lesbar8 s'.speicher (eintrittRsp (peZ 30) - BitVec.ofNat 64 8) = true ∧
        schreibbar8 s'.speicher (eintrittRsp (peZ 30) - BitVec.ofNat 64 8) = true ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 35) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 6) := by
  have hok := bildFuerP_ok .p48 pw3Cfg pePro pw3Prog piPs pwSigma peEs pw3Certs pw3Src pe_bauOk
  have hval := (kompiliert_geladen .p48 pw3Cfg piPs piEs pw3Certs pw3Src pw3Bytes pwSigma
    pw3_compile pw3_bauOk).1
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw3_quelle30
  obtain ⟨n, s', hrun, hrip, hW, hE, hstop, hl, hs⟩ := pipeline_correct_entry .p48 peBild pw3Cfg
    sysvParameter piPs peEs pw3Certs pw3Src pw3Bytes hval hok.1 bildFuerP_eintritt_zeuge.1.1
    pwSigma hok.2.1 .nolibcMain (peZ 30) [] pe_zulassung30 (peReg 30) witnessFlags rfl pwEnv30
    (pe_abi 30 (by decide) (by decide)) pwO 0 pwR σ' ρ' hsrc
  exact ⟨pe_ohne_prolog, σ', ρ', hsrc, n, s', hrun, hrip, hW, hE, hstop, hl, hs,
    pi_lesen _ σ' 0 8192 hW rfl 35 h0, pi_lesen _ σ' 1 8200 hW rfl 6 h1⟩

/-- JOINT WITNESS for `pipeline_refuses_entry`: from the same admitted
    entry with `x = 70`, reason 1, `rax = 1` at `12314`. -/
theorem pipeline_refuses_entry_zeuge :
    ∃ (σ' : World pwD), execBlock pwO 0 pwR pw3Src pwSigma pwEnv70 = .grund σ' ⟨1, by decide⟩ ∧
      ∃ n s', laufBytes n (peZ 70).zustand = .weiter s' ∧
        s'.rip = natAdresse (exitAdr pw3Cfg 1 + 10) ∧ s'.register exitReg = intWort 1 ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ byteschritt s' = .verweigert ∧
        lesbar8 s'.speicher (eintrittRsp (peZ 70) - BitVec.ofNat 64 8) = true ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 75) := by
  have hok := bildFuerP_ok .p48 pw3Cfg pePro pw3Prog piPs pwSigma peEs pw3Certs pw3Src pe_bauOk
  have hval := (kompiliert_geladen .p48 pw3Cfg piPs piEs pw3Certs pw3Src pw3Bytes pwSigma
    pw3_compile pw3_bauOk).1
  obtain ⟨σ', hsrc, h0⟩ := pw3_quelle70
  obtain ⟨n, s', hrun, hrip, hreg, hW, hstop, hl, -⟩ := pipeline_refuses_entry .p48 peBild pw3Cfg
    sysvParameter piPs peEs pw3Certs pw3Src pw3Bytes hval hok.1 bildFuerP_eintritt_zeuge.1.1
    pwSigma hok.2.1 .nolibcMain (peZ 70) [] pe_zulassung70 (peReg 70) witnessFlags rfl pwEnv70
    (pe_abi 70 (by decide) (by decide)) pwO 0 pwR σ' ⟨1, by decide⟩ hsrc
  exact ⟨σ', hsrc, n, s', hrun, hrip, hreg, hW, hstop, hl, pi_lesen _ σ' 0 8192 hW rfl 75 h0⟩

/-! ### Entry poison probes -/

/-- A CLOBBERING entry sequence: `rsi <- rdi` then `rdi <- rsi` reads the
    overwritten `rsi`. Refused. -/
theorem gift_prolog_klobber :
    prologOk { pw3Cfg with regs := [.rsi, .rdi] } sysvParameter 2 = false := by decide

/-- An entry sequence that writes `rsp`: refused. -/
theorem gift_prolog_rsp : prologOk { pw3Cfg with regs := [.rsp] } sysvParameter 1 = false := by
  decide

/-- A parameter without an ABI register: refused. -/
theorem gift_prolog_ohne_abi : prologOk pw3Cfg [] 1 = false := by decide

/-- A tampered entry-sequence byte in the image: refused. -/
def peBildFalsch : Bild := { peBild with datei := peBild.datei.set 2 (natByte 0xD7) }

theorem gift_prolog_byte : prologImageOk peBildFalsch pw3Cfg sysvParameter peN = false := by
  decide

/-- A misaligned entry stack: the decided conditions and the admission
    refuse. -/
def peZSchief : EintrittZustand :=
  { peZ 30 with zustand := { (peZ 30).zustand with
      register := fun q => if q = .rsp then natAdresse 16440 else peReg 30 q } }

theorem gift_stapel_schief :
    eintrittBedingung .nolibcMain peEs 16440 peZSchief = false ∧
      eintrittOk .p48 peBild 0 .nolibcMain peZSchief = false := by
  decide

/-- An entry stack outside every extent: the admission refuses (the word
    below the top is not readable). -/
def peZAussen : EintrittZustand :=
  { peZ 30 with zustand := { (peZ 30).zustand with
      register := fun q => if q = .rsp then natAdresse 20480 else peReg 30 q } }

theorem gift_stapel_aussen : eintrittOk .p48 peBild 0 .nolibcMain peZAussen = false := by
  decide

/-- A thread root promises a guard page; without the finding the entry is
    refused. -/
theorem gift_eintritt_guard : eintrittBedingung .fadenWurzel peEs 16448 (peZ 30) = false := by
  unfold eintrittBedingung
  decide


/-! ## 9. Joint witnesses of the generic builder and entry lemmas

    Every lemma of the completeness proof and of the entry, instantiated
    on the two-reason image (`B3`) and the entry image (`peBild`). -/

/-- The duplicate-free reason list of the two-reason program. -/
def gs3 : List Nat := ohneDoppel (grundListe (optimise pw3Certs pw3Src))

theorem gs3_eq : gs3 = [1, 0] := by decide

theorem gs3_nodup : gs3.Nodup := ohneDoppel_nodup _

/-- The built image of section 7, as the builder sees it. -/
def B3 : Bild := baueBildP pw3Cfg (encodeAll ([] : List Befehl)) (encodeAll pw3Prog) gs3 piPs pwSigma piEs

theorem F3 : BauFakten .p48 pw3Cfg (encodeAll ([] : List Befehl)) (encodeAll pw3Prog) gs3 piPs piEs :=
  bauOk_fakten .p48 pw3Cfg (encodeAll ([] : List Befehl)) (encodeAll pw3Prog) gs3 piPs piEs pw3_bauOk

/-- The code section of `B3`. -/
def B3code : Abschnitt := codeAbschnittP pw3Cfg (encodeAll ([] : List Befehl)) (encodeAll pw3Prog)

theorem B3code_mem : B3code ∈ B3.abschnitte := List.mem_cons_self

/-- The stub section of reason 1 in `B3`. -/
def B3stub1 : Abschnitt :=
  { dateiOff := 104, dateiLen := 10, vaddr := 12304, memLen := 10, lesbar := true,
    schreibbar := false, ausfuehrbar := true, ausr := 1 }

theorem B3stub1_mem : B3stub1 ∈ B3.abschnitte := by decide

theorem baueBildP_zeuge :
    valX86 .p48 B3 = true ∧ wohlgeformt .p48 B3 = true ∧ bildDeckung B3 = true ∧
    B3.abschnitte.Pairwise VGetrennt ∧ KetteE 0 B3.abschnitte B3.datei.length ∧
    B3code.vaddr + B3code.memLen ≤ halbe .p48 ∧
    (B3stub1 = B3code ∨
      (∃ g ∈ gs3, B3stub1.vaddr = exitAdr pw3Cfg g ∧ B3stub1.memLen = 10 ∧ B3stub1.dateiLen = 10 ∧
        B3stub1.lesbar = true ∧ B3stub1.schreibbar = false ∧ B3stub1.ausfuehrbar = true ∧
        B3stub1.ausr = 1) ∨
      (∃ e ∈ piEs, B3stub1.vaddr = e.basis ∧ B3stub1.memLen = e.len ∧ B3stub1.dateiLen = e.len ∧
        B3stub1.lesbar = true ∧ B3stub1.schreibbar = true ∧ B3stub1.ausfuehrbar = false ∧
        B3stub1.ausr = e.ausr)) :=
  ⟨baueBildP_valX86 .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup,
    baueBildP_wohlgeformt .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup,
    baueBildP_deckung pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs,
    baueBildP_pairwise .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup,
    baueBildP_kette pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs,
    baueBildP_halb .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 B3code B3code_mem,
    baueBildP_sek pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs B3stub1 B3stub1_mem⟩

theorem baueBildP_lade_zeuge :
    codeAtB (ladung B3) (natAdresse pw3Cfg.codeBase) (encodeAll pw3Prog) = true ∧
    (ladung B3).ausfuehrbar (natAdresse (pw3Cfg.codeBase + (encodeAll pw3Prog).length)) = false ∧
    codeAtB (ladung B3) (natAdresse (exitAdr pw3Cfg 1)) (stubBytes 1) = true ∧
    (ladung B3).ausfuehrbar (natAdresse (exitAdr pw3Cfg 1 + 10)) = false ∧
    platzOkB (ladung B3) piPs = true ∧ weltB (ladung B3) piPs pwSigma = true ∧
    lesbar8 (ladung B3) (natAdresse 8200) = true ∧ schreibbar8 (ladung B3) (natAdresse 8200) = true ∧
    (∃ t ∈ B3.abschnitte, abteilFinden B3.abschnitte 0 8195 = some t ∧ t.lesbar = true ∧
      t.schreibbar = true ∧ ladenByte B3 0 8195 = slotByte piPs pwSigma 8195 ∧ 8195 < 2 ^ 64) :=
  ⟨(baueBildP_code .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup).1,
    baueBildP_stop .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3,
    (baueBildP_stubs .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup 1 (by decide)).1,
    (baueBildP_stubs .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup 1 (by decide)).2,
    (baueBildP_welt .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup).1,
    (baueBildP_welt .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup).2,
    (baueBildP_extent_rw .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup _
      List.mem_cons_self 8200 (by decide) (by decide)).1,
    (baueBildP_extent_rw .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup _
      List.mem_cons_self 8200 (by decide) (by decide)).2,
    baueBildP_extent_byte .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup _
      List.mem_cons_self 8195 (by decide) (by decide)⟩

theorem loader_zeuge :
    abteilFinden B3.abschnitte 0 12305 = some B3stub1 ∧
    (B3stub1 ∈ B3.abschnitte ∧ B3stub1.vaddr ≤ 12305 ∧ 12305 < B3stub1.vaddr + B3stub1.memLen) ∧
    ladenAusfuehrbar B3 0 12314 = false ∧
    ladenByte B3 0 (B3stub1.vaddr + 1) = B3.datei.getD (B3stub1.dateiOff + 1) (BitVec.ofNat 8 0) ∧
    codeAtB (ladung B3) (natAdresse (B3stub1.vaddr + 0)) (stubBytes 1) = true ∧
    paarweise (virtReich 0) B3.abschnitte = true := by
  have hpw := baueBildP_pairwise .p48 pw3Cfg [] pw3Prog gs3 piPs pwSigma piEs F3 gs3_nodup
  have hf := abteilFinden_eindeutig _ hpw B3stub1 B3stub1_mem 12305 (by decide) (by decide)
  exact ⟨hf, abteilFinden_mem _ _ _ hf, ladenAusfuehrbar_aus B3 12314 (by decide),
    ladenByte_in B3 hpw B3stub1 B3stub1_mem (by decide) 1 (by decide),
    codeAtB_von B3 rfl hpw B3stub1 B3stub1_mem (by decide) rfl rfl 0 (stubBytes 1) (by decide)
      (by decide) (by decide),
    paarweise_von _ _ (hpw.imp fun {s t} h => by unfold VGetrennt at h; simp only [virtReich]; omega)⟩

theorem stub_mem_v_zeuge :
    ∃ g ∈ [1, 0], B3stub1.vaddr = exitAdr pw3Cfg g ∧ B3stub1.memLen = 10 ∧ B3stub1.dateiLen = 10 ∧
      B3stub1.lesbar = true ∧ B3stub1.schreibbar = false ∧ B3stub1.ausfuehrbar = true ∧
      B3stub1.ausr = 1 :=
  stub_mem_v pw3Cfg [1, 0] 104 B3stub1 (by decide)

theorem stub_vorhanden_zeuge :
    ∃ t ∈ stubAbschnitte pw3Cfg ([7, 7] : List Byte).length [1, 0], t.vaddr = exitAdr pw3Cfg 0 ∧
      t.memLen = 10 ∧ t.dateiLen = 10 ∧ t.schreibbar = false ∧ t.ausfuehrbar = true ∧
      (([7, 7] ++ ([1, 0].map stubBytes).flatten ++ [5]).drop t.dateiOff).take 10 = stubBytes 0 :=
  stub_vorhanden pw3Cfg [1, 0] [7, 7] [5] 0 (by decide)

/-- The second stub section (reason 0) after a two-byte prefix. -/
def stub0Sek : Abschnitt :=
  { dateiOff := 12, dateiLen := 10, vaddr := 12288, memLen := 10, lesbar := true,
    schreibbar := false, ausfuehrbar := true, ausr := 1 }

theorem stub_bytes_zeuge :
    ∃ g ∈ [1, 0], (([7, 7] ++ ([1, 0].map stubBytes).flatten ++ [5]).drop stub0Sek.dateiOff).take 10 =
      stubBytes g :=
  stub_bytes pw3Cfg [1, 0] [7, 7] [5] stub0Sek (by decide)

/-- The data section of the witness extent from offset 3. -/
def datenSek : Abschnitt :=
  { dateiOff := 3, dateiLen := 16, vaddr := 8192, memLen := 16, lesbar := true,
    schreibbar := true, ausfuehrbar := false, ausr := 8 }

theorem daten_mem_v_zeuge :
    ∃ e ∈ piEs, datenSek.vaddr = e.basis ∧ datenSek.memLen = e.len ∧ datenSek.dateiLen = e.len ∧
      datenSek.lesbar = true ∧ datenSek.schreibbar = true ∧ datenSek.ausfuehrbar = false ∧
      datenSek.ausr = e.ausr :=
  daten_mem_v piEs 3 datenSek (by decide)

def piE : TabLayout := { tab := 0, basis := 8192, len := 16, ausr := 8 }

theorem daten_vorhanden_zeuge :
    ∃ t ∈ datenAbschnitte ([7, 7, 7] : List Byte).length piEs, t.vaddr = piE.basis ∧
      t.memLen = piE.len ∧ t.dateiLen = piE.len ∧ t.lesbar = true ∧ t.schreibbar = true ∧
      (([7, 7, 7] ++ datenDatei piPs pwSigma piEs).drop t.dateiOff).take piE.len =
        datenChunk piPs pwSigma piE :=
  daten_vorhanden piPs pwSigma piEs [7, 7, 7] piE (by decide)

theorem datenChunk_zeuge :
    (datenChunk piPs pwSigma piE).length = 16 ∧
      (datenChunk piPs pwSigma piE).getD 8 (BitVec.ofNat 8 0) = slotByte piPs pwSigma (8192 + 8) ∧
      slotByte piPs pwSigma (8192 + 8) = natByte 9 ∧
      slotByte piPs pwSigma ((⟨(), 1, (), 8200⟩ : Platz pwD).a + 0) =
        wortByte (slotWort _ (pwSigma.slots () 1 ())) 0 :=
  ⟨datenChunk_length _ _ _, datenChunk_getD _ _ _ 8 (by decide), by decide,
    slotByte_von piPs pwSigma (by decide) ⟨(), 1, (), 8200⟩
      (List.mem_cons_of_mem _ List.mem_cons_self) 0 (by decide)⟩

theorem kette_zeuge :
    KetteE 104 (stubAbschnitte pw3Cfg 104 [1, 0]) (104 + 10 * [1, 0].length) ∧
    KetteE 3 (datenAbschnitte 3 piEs) (3 + (datenDatei piPs pwSigma piEs).length) ∧
    KetteE 104 (stubAbschnitte pw3Cfg 104 [1, 0] ++ datenAbschnitte 124 piEs)
      (124 + (datenDatei piPs pwSigma piEs).length) ∧
    104 ≤ 124 ∧ (104 ≤ B3stub1.dateiOff ∧ B3stub1.dateiOff + B3stub1.dateiLen ≤ 124) ∧
    (stubAbschnitte pw3Cfg 104 [1, 0]).Pairwise FGetrennt ∧
    ((([1, 0].map stubBytes).flatten).length = 10 * [1, 0].length) :=
  have h1 := ketteE_stubs pw3Cfg [1, 0] 104
  have h2 := ketteE_daten piPs pwSigma piEs 124
  ⟨h1, ketteE_daten piPs pwSigma piEs 3, ketteE_append _ _ 104 124 _ h1 h2,
    ketteE_le _ 104 124 h1, ketteE_mem _ 104 124 h1 B3stub1 (by decide),
    ketteE_pairwise _ 104 124 h1, stubs_flatten_length _⟩

theorem trennung_zeuge :
    (stubAbschnitte pw3Cfg 104 [1, 0]).Pairwise VGetrennt ∧
    (datenAbschnitte 124 peEs).Pairwise VGetrennt ∧
    decodeFuel (pw3Prog.length + 1) (encodeAll pw3Prog) = some (pw3Prog.map kanon, []) ∧
    validAllFuel (pw3Prog.length + 1) (encodeAll pw3Prog) = true ∧
    gleicherSchluessel (⟨(), 1, (), 8200⟩ : Platz pwD) ⟨(), 1, (), 8200⟩ = true ∧
    sepB piPs = true ∧
    paarweise fileReich B3.abschnitte = true :=
  have hl : layoutOk peEs = true := by decide
  ⟨stubs_pairwise pw3Cfg (by decide) [1, 0] 104 (by decide),
    daten_pairwise peEs 124 (by unfold layoutOk at hl; simp only [Bool.and_eq_true] at hl; exact hl.2),
    decodeFuel_encodeAll pw3Prog _ (Nat.le_refl _),
    validAllFuel_encodeAll pw3Prog _ (Nat.le_refl _),
    gleicherSchluessel_selbst _, sepB_von piPs (by decide),
    paarweise_von _ _ ((ketteE_pairwise _ _ _ (baueBildP_kette pw3Cfg [] pw3Prog gs3 piPs pwSigma
      piEs)).imp fun h => by simpa [fileReich, FGetrennt] using h)⟩

theorem worte_zeuge :
    lesbar8 (ladung B3) (natAdresse 8192) = true ∧ schreibbar8 (ladung B3) (natAdresse 8192) = true ∧
    read64 (ladung B3) (natAdresse 8192) = some (BitVec.ofNat 64 7) := by
  have hl : lesbar8 (ladung B3) (natAdresse 8192) = true :=
    lesbar8_von _ _ (by decide)
  exact ⟨hl, schreibbar8_von _ _ (by decide), read64_von _ _ _ hl (by decide)⟩

/-- The compiler output and the slot addresses of the optimised block. -/
theorem compile_zeuge :
    (∃ prog, cfgOk pw3Cfg = true ∧
      senkBlock pw3Cfg (layoutVon piPs) 0 (optimise pw3Certs pw3Src) = some prog ∧
      pw3Bytes = encodeAll prog) ∧
    slotAdressen (layoutVon piPs) (optimise pw3Certs pw3Src) = [8192, 8200] ∧
    (∃ t k f, (layoutVon piPs).loc t k f = some 8200) ∧
    (∃ t k f, (layoutVon piPs).loc t k f = some 8192) :=
  ⟨compile_inv pw3Cfg _ pw3Certs pw3Src pw3Bytes pw3_compile, by decide,
    slotAdressen_loc (layoutVon piPs) (optimise pw3Certs pw3Src) 8200 (by decide),
    stmtAdresse_loc (layoutVon piPs) (Stmt.assignSlot (V := pw2V) (l := false) () () pwIdx0 pwWert0
      pw2Hw pwHL) 8192 (by decide)⟩

/-! ### The entry lemmas -/

theorem prolog_zeuge :
    ((prologPaare pw3Cfg sysvParameter 1).Pairwise ZugOk ∧
      ∀ q ∈ prologPaare pw3Cfg sysvParameter 1, q.1 ≠ .rsp) ∧
    (prolog pw3Cfg sysvParameter 1).all gerade = true ∧
    varIdx (Var.hier (Γ := []) (τ := .int 0 100)) < ([.int 0 100] : Ctx).length ∧
    eintrittStart peBild pw3Cfg 0 (peReg 30) witnessFlags = startZustand peBild pw3Cfg (peReg 30)
      witnessFlags :=
  ⟨prologOk_teile pw3Cfg sysvParameter 1 pe_prologOk, prolog_gerade _ _ _, varIdx_lt _,
    eintrittStart_null _ _ _ _⟩

/-- The entry copies run on the admitted entry state: `r10` goes from 999
    to the parameter 30, memory stays. -/
theorem zuege_lauf_zeuge :
    (peZ 30).zustand.register .r10 = intWort 999 ∧
    ∃ s', lauf (([(Register.r10, Register.rdi)].map fun q => Befehl.movReg64 q.1 q.2).map kanon)
        (peZ 30).zustand = some s' ∧ s'.speicher = (peZ 30).zustand.speicher ∧
      s'.register .r10 = intWort 30 ∧ s'.register .rsp = natAdresse 16448 := by
  obtain ⟨s', hrun, hmem, hset, hrest⟩ := zuege_lauf [(Register.r10, Register.rdi)] (peZ 30).zustand
    (by decide)
  refine ⟨by decide, s', hrun, hmem, ?_, ?_⟩
  · rw [hset _ List.mem_cons_self]
    rfl
  · rw [hrest .rsp (by decide)]
    rfl

/-- `EnvRepr` from the ABI and the copies, and the whole entry run. -/
theorem prolog_lauf_zeuge :
    ¬ EnvRepr pwEnv30 (peZ 30).zustand.register (abbOf pw3Cfg) ∧
    ∃ s1, laufBytes (prolog pw3Cfg sysvParameter pwCtx.length).length (peZ 30).zustand =
        .weiter s1 ∧ s1.rip = natAdresse pw3Cfg.codeBase ∧ s1.speicher = ladung peBild ∧
      s1.register .rsp = (peZ 30).zustand.register .rsp ∧ EnvRepr pwEnv30 s1.register (abbOf pw3Cfg) :=
  ⟨pe_ohne_prolog, prolog_lauf peBild pw3Cfg sysvParameter pwEnv30 bildFuerP_eintritt_zeuge.1.1
    (peZ 30).zustand rfl rfl (pe_abi 30 (by decide) (by decide))⟩

theorem prolog_envRepr_zeuge :
    EnvRepr pwEnv30 (regSet (peReg 30) .r10 (intWort 30)) (abbOf pw3Cfg) :=
  prolog_envRepr pw3Cfg sysvParameter pwEnv30 (peReg 30) _ (pe_abi 30 (by decide) (by decide))
    (by decide)

/-! ### The stride lemmas -/

theorem exitAdr_zeuge :
    exitAdr pwCfg 3 = pwCfg.exitBase + 3 ∧ exitAdr pw3Cfg 0 + pw3Cfg.exitStride ≤ exitAdr pw3Cfg 1 ∧
    exitAdr pw3Cfg 1 = 12304 :=
  ⟨exitAdr_eins pwCfg rfl 3, exitAdr_abstand pw3Cfg 0 1 (by decide), rfl⟩

/-- JOINT WITNESS for `pipeline_refuses_eins`: the ORIGINAL refusal form
    (exit `exitBase + r`) re-derived for the stride-one configuration. -/
theorem pipeline_refuses_eins_zeuge :
    ∃ (σ' : World pwD), execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' ⟨0, by decide⟩ ∧
      ∃ n s', laufBytes n (pwStart 70) = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.exitBase + 0) ∧ WorldRep pwL s'.speicher σ' ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 75) := by
  obtain ⟨σ', hsrc, h0, -⟩ := pw_quelle70
  obtain ⟨n, s', hrun, hrip, hW⟩ := pipeline_refuses_eins pwCfg rfl pwL pwCerts pwSrc pwBytes
    pw_validate pw_layoutSep pwO 0 pwR pwSigma pwEnv70 (pwStart 70) pw_code rfl pw_worldRep
    pw_envRepr70 σ' ⟨0, by decide⟩ hsrc
  exact ⟨σ', hsrc, n, s', hrun, hrip, hW, read_von_worldRep _ σ' 0 8192 hW rfl 75 h0⟩

/-! ## 10. The widened fragment: a depth-3 value, a deep check and an `ite`

    One program over the same declaration and placements, compiled with
    NO optimiser certificate, using all three widenings at once:

      T[0].f = ((x + 7) - 2) + x;              -- depth 3, two scratch registers
      check ((x + 3) - 1) < 90 else reason 0;   -- deep operand
      if x < 40 { T[1].f = x + 100 } else { T[1].f = (x - 40) + 500 }

    The configuration adds the scratch stack `frei = [rdx, rsi]` and the
    exit stride 16. The candidate is written out literally (as an untrusted
    producer would emit it), the validator recomputes it, the image is
    built and checked, and the run from the LOADED image is taken for both
    branch outcomes (`x = 30` then-branch, `x = 60` else-branch, both
    changing memory) and for the refusal (`x = 95`), by computation AND
    through the general closing theorems. -/

/-- `((x + 7) - 2) + x`, widened to the field type: three binary levels. -/
def pdWert0 : Expr pwD pwCtx [] (pwD.typ () ()) :=
  .weiter (lo := 7 + 0 - 2 + 0) (hi := 107 - 2 + 100) (by decide) (by decide)
    (.add (.sub (.add (.var .hier) (.lit 7)) (.lit 2)) (.var .hier))

/-- The deep check `((x + 3) - 1) < 90`. -/
def pdCheck : Expr pwD pwCtx [] .bool := .lt (.sub (.add (.var .hier) (.lit 3)) (.lit 1)) (.lit 90)

/-- The `ite` condition `x < 40`. -/
def pdBed : Expr pwD pwCtx [] .bool := .lt (.var .hier) (.lit 40)

/-- The then-value `x + 100`. -/
def pdThen : Expr pwD pwCtx [] (pwD.typ () ()) :=
  .weiter (lo := 0 + 100) (hi := 100 + 100) (by decide) (by decide) (.add (.var .hier) (.lit 100))

/-- The else-value `(x - 40) + 500` (a negative intermediate range). -/
def pdElse : Expr pwD pwCtx [] (pwD.typ () ()) :=
  .weiter (lo := 0 - 40 + 500) (hi := 100 - 40 + 500) (by decide) (by decide)
    (.add (.sub (.var .hier) (.lit 40)) (.lit 500))

/-- The then-block and the else-block: both store to row 1. -/
def pdT : Block pwD pwV false pwCtx [] [] := .cons (.assignSlot () () pwIdx1 pdThen pwHw pwHL) .nil
def pdE : Block pwD pwV false pwCtx [] [] := .cons (.assignSlot () () pwIdx1 pdElse pwHw pwHL) .nil

/-- THE WIDENED SOURCE PROGRAM. -/
def pdSrc : Block pwD pwV false pwCtx [] [] :=
  .cons (.assignSlot () () pwIdx0 pdWert0 pwHw pwHL)
    (.pruefung pdCheck (.retGrund ⟨0, by decide⟩ pwHΛ)
      (.cons (.ite pdBed pdT pdE) .nil))

/-- The configuration: the original registers, scratch stack `rdx, rsi`,
    exit stride 16. -/
def pdCfg : PipeCfg := { pwCfg with exitStride := 16, frei := [.rdx, .rsi] }

/-- THE UNTRUSTED CANDIDATE, written out: the depth-3 value (9), the deep
    check with its jump to the exit 12288 (7), the `ite` condition with the
    jump over the then-block (+38 bytes) (4), the then-block and the jump
    over the else-block (+46 bytes) (6), the else-block (7). -/
def pdProg : List Befehl :=
  [ .movReg64 .rax .r10, .movImm64 .rsi (intWort 7), .addReg64 .rax .rsi,
    .movImm64 .rdx (intWort 2), .subReg64 .rax .rdx, .movReg64 .rcx .r10, .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 8192), .store64 .rbx .rax (BitVec.ofNat 32 0),
    .movReg64 .rax .r10, .movImm64 .rsi (intWort 3), .addReg64 .rax .rsi,
    .movImm64 .rdx (intWort 1), .subReg64 .rax .rdx, .movImm64 .rcx (intWort 90),
    .cmpReg64 .rax .rcx, .jumpIf32 .ge (BitVec.ofNat 32 8092),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 40), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (BitVec.ofNat 32 38),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 100), .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 8200), .store64 .rbx .rax (BitVec.ofNat 32 0),
    .jump32 (BitVec.ofNat 32 46),
    .movReg64 .rax .r10, .movImm64 .rdx (intWort 40), .subReg64 .rax .rdx,
    .movImm64 .rcx (intWort 500), .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 8200), .store64 .rbx .rax (BitVec.ofNat 32 0) ]

def pdBytes : List Byte := encodeAll pdProg

theorem pd_cfgOk : cfgOk pdCfg = true := by decide

/-- The compiler produces exactly the candidate (no certificate needed). -/
theorem pd_compile : compile pdCfg (layoutVon piPs) [] pdSrc = some pdBytes := by decide

/-- THE VALIDATOR ACCEPTS the untrusted candidate, by computation. -/
theorem pd_validate : validate pdCfg (layoutVon piPs) [] pdSrc pdBytes = true := by decide

theorem pd_laenge : pdBytes.length = 206 := by decide

/-- The reasons the image needs a stub for: the deep check's reason 0. -/
theorem pd_gruende : grundListe (optimise [] pdSrc) = [0] := by decide

/-- The decided layout side conditions hold. -/
theorem pd_bauOk :
    bauOk .p48 pdCfg [] pdBytes (ohneDoppel (grundListe (optimise [] pdSrc))) piPs piEs = true := by
  decide

def pdBild : Bild := bildFuer pdCfg [] pdSrc pdBytes piPs pwSigma piEs

def pdStart (x : Int) : Zustand := startZustand pdBild pdCfg (pwReg x) witnessFlags

/-- The environments `x = 60` (else-branch) and `x = 95` (failed check). -/
def pwEnv60 : Env pwD pwCtx := .cons (⟨60, by decide, by decide⟩ : Zahl 0 100) .nil
def pwEnv95 : Env pwD pwCtx := .cons (⟨95, by decide, by decide⟩ : Zahl 0 100) .nil

theorem pw_envRepr60 : EnvRepr pwEnv60 (pwReg 60) (abbOf pdCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

theorem pw_envRepr95 : EnvRepr pwEnv95 (pwReg 95) (abbOf pdCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

theorem pd_envRepr30 : EnvRepr pwEnv30 (pwReg 30) (abbOf pdCfg) := pw_envRepr30

/-- The REAL source runs: `x = 30` takes the then-branch (rows 7 -> 65,
    9 -> 130), `x = 60` the else-branch (rows -> 125, 520), `x = 95` fails
    the deep check (row 0 already 195). -/
theorem pd_quelle30 : ∃ σ' ρ', execBlock pwO 0 pwR pdSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
    (σ'.slots () 0 ()).n = 65 ∧ (σ'.slots () 1 ()).n = 130 :=
  ⟨_, _, rfl, rfl, rfl⟩

theorem pd_quelle60 : ∃ σ' ρ', execBlock pwO 0 pwR pdSrc pwSigma pwEnv60 = .ok σ' ρ' ∧
    (σ'.slots () 0 ()).n = 125 ∧ (σ'.slots () 1 ()).n = 520 :=
  ⟨_, _, rfl, rfl, rfl⟩

theorem pd_quelle95 : ∃ σ', execBlock pwO 0 pwR pdSrc pwSigma pwEnv95 =
    .grund σ' ⟨0, by decide⟩ ∧ (σ'.slots () 0 ()).n = 195 ∧ (σ'.slots () 1 ()).n = 9 :=
  ⟨_, rfl, rfl, rfl⟩

/-- The fetched runs from the LOADED image, by computation: `x = 30` runs
    27 steps (falls through the `ite` jump, takes the jump over the else
    block) to the code end 4302 with rows 65 and 130; `x = 60` is at the
    else-block (4256) after 21 steps (the `ite` jump taken) and at the code
    end after 28, with rows 125 and 520 (bytes 8, 2); both STOP there.
    `x = 95` reaches the exit 12288 after 17 steps and stops after the stub
    with `rax = 0`. -/
theorem pd_laeufe :
    ausgangRip (laufBytes 27 (pdStart 30)) = some (natAdresse 4302) ∧
      ausgangByte (natAdresse 8192) (laufBytes 27 (pdStart 30)) = some (natByte 65) ∧
      ausgangByte (natAdresse 8200) (laufBytes 27 (pdStart 30)) = some (natByte 130) ∧
      ausgangRip (laufBytes 28 (pdStart 30)) = none ∧
      ausgangRip (laufBytes 21 (pdStart 60)) = some (natAdresse 4256) ∧
      ausgangRip (laufBytes 28 (pdStart 60)) = some (natAdresse 4302) ∧
      ausgangByte (natAdresse 8192) (laufBytes 28 (pdStart 60)) = some (natByte 125) ∧
      ausgangByte (natAdresse 8200) (laufBytes 28 (pdStart 60)) = some (natByte 8) ∧
      ausgangByte (natAdresse 8201) (laufBytes 28 (pdStart 60)) = some (natByte 2) ∧
      ausgangRip (laufBytes 29 (pdStart 60)) = none ∧
      ausgangRip (laufBytes 17 (pdStart 95)) = some (natAdresse 12288) ∧
      ausgangRip (laufBytes 18 (pdStart 95)) = some (natAdresse 12298) ∧
      ausgangReg .rax (laufBytes 18 (pdStart 95)) = some (intWort 0) ∧
      ausgangByte (natAdresse 8192) (laufBytes 18 (pdStart 95)) = some (natByte 195) ∧
      ausgangRip (laufBytes 19 (pdStart 95)) = none := by
  decide

/-- JOINT WITNESS for `pipeline_correct_compiled` over the WIDENED
    fragment, BOTH branch outcomes of the `ite`: from the compiler output
    alone, the loaded image's run changes rows 7/9 to 65/130 (then) and to
    125/520 (else) and stops at the code end. -/
theorem pipeline_correct_compiled_ite_zeuge :
    (∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      execBlock pwO 0 pwR pdSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      ∃ n s', laufBytes n (pdStart 30) = .weiter s' ∧
        s'.rip = natAdresse (pdCfg.codeBase + pdBytes.length) ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pdCfg) ∧
        byteschritt s' = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 65) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 130)) ∧
    (∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      execBlock pwO 0 pwR pdSrc pwSigma pwEnv60 = .ok σ' ρ' ∧
      ∃ n s', laufBytes n (pdStart 60) = .weiter s' ∧
        s'.rip = natAdresse (pdCfg.codeBase + pdBytes.length) ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pdCfg) ∧
        byteschritt s' = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 125) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 520)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pd_quelle30
    obtain ⟨n, s', hrun, hrip, hW, hE, hstop⟩ := pipeline_correct_compiled .p48 pdCfg piPs piEs
      [] pdSrc pdBytes pd_compile pd_bauOk pwSigma (pwReg 30) witnessFlags pwEnv30
      pd_envRepr30 pwO 0 pwR σ' ρ' hsrc
    exact ⟨σ', ρ', hsrc, n, s', hrun, hrip, hW, hE, hstop, pi_lesen _ σ' 0 8192 hW rfl 65 h0,
      pi_lesen _ σ' 1 8200 hW rfl 130 h1⟩
  · obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pd_quelle60
    obtain ⟨n, s', hrun, hrip, hW, hE, hstop⟩ := pipeline_correct_compiled .p48 pdCfg piPs piEs
      [] pdSrc pdBytes pd_compile pd_bauOk pwSigma (pwReg 60) witnessFlags pwEnv60
      pw_envRepr60 pwO 0 pwR σ' ρ' hsrc
    exact ⟨σ', ρ', hsrc, n, s', hrun, hrip, hW, hE, hstop, pi_lesen _ σ' 0 8192 hW rfl 125 h0,
      pi_lesen _ σ' 1 8200 hW rfl 520 h1⟩

/-- JOINT WITNESS for `pipeline_refuses_compiled` over the deep check:
    `x = 95` fails `((x + 3) - 1) < 90`, the loaded run ends after the stub
    at `12298` with `rax = 0` and row 0 already rewritten to 195. -/
theorem pipeline_refuses_compiled_tief_zeuge :
    ∃ σ', execBlock pwO 0 pwR pdSrc pwSigma pwEnv95 = .grund σ' ⟨0, by decide⟩ ∧
      ∃ n s', laufBytes n (pdStart 95) = .weiter s' ∧
        s'.rip = natAdresse (exitAdr pdCfg 0 + 10) ∧ s'.register exitReg = intWort 0 ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ byteschritt s' = .verweigert ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 195) := by
  obtain ⟨σ', hsrc, h0, -⟩ := pd_quelle95
  obtain ⟨n, s', hrun, hrip, hreg, hW, hstop⟩ := pipeline_refuses_compiled .p48 pdCfg piPs
    piEs [] pdSrc pdBytes pd_compile pd_bauOk pwSigma (pwReg 95) witnessFlags pwEnv95
    pw_envRepr95 pwO 0 pwR σ' ⟨0, by decide⟩ hsrc
  exact ⟨σ', hsrc, n, s', hrun, hrip, hreg, hW, hstop, pi_lesen _ σ' 0 8192 hW rfl 195 h0⟩

/-- JOINT WITNESS for `senkBlock_korrektC` (the generic block theorem with
    the code region carried) on the widened program from the LOADED image,
    both branch outcomes; and for `senkBlock_ausgang` through the `ite`. -/
theorem senkBlock_korrektC_zeuge :
    (∃ n s', laufBytes n (pdStart 30) = .weiter s' ∧
      CodeAt s'.speicher (natAdresse pdCfg.codeBase) pdBytes ∧
      Entspricht pdCfg (layoutVon piPs) (addrOff (natAdresse pdCfg.codeBase)
        (([] : List Byte).length + pdBytes.length))
        (execBlock pwO 0 pwR pdSrc pwSigma pwEnv30) s') ∧
    (∃ n s', laufBytes n (pdStart 60) = .weiter s' ∧
      CodeAt s'.speicher (natAdresse pdCfg.codeBase) pdBytes ∧
      Entspricht pdCfg (layoutVon piPs) (addrOff (natAdresse pdCfg.codeBase)
        (([] : List Byte).length + pdBytes.length))
        (execBlock pwO 0 pwR pdSrc pwSigma pwEnv60) s') ∧
    ((∃ σ' ρ', execBlock pwO 0 pwR pdSrc pwSigma pwEnv95 = .ok σ' ρ') ∨
      (∃ σ' r, execBlock pwO 0 pwR pdSrc pwSigma pwEnv95 = .grund σ' r)) := by
  have himg := (kompiliert_geladen .p48 pdCfg piPs piEs [] pdSrc pdBytes pwSigma pd_compile
    pd_bauOk).2
  have hcode := imageOk_codeAt .p48 pdBild pdCfg piPs piEs [] pdSrc pdBytes himg.1
  have hsep := imageOk_layoutSep .p48 pdBild pdCfg piPs piEs [] pdSrc pdBytes himg.1
  have hW := imageOk_worldRep .p48 pdBild pdCfg piPs piEs [] pdSrc pdBytes himg.1 pwSigma himg.2
  obtain ⟨prog, hc, hlow, hb, -⟩ := validate_sound pdCfg (layoutVon piPs) [] pdSrc pdBytes
    pd_validate
  have hlow' : senkBlock pdCfg (layoutVon piPs) ([] : List Byte).length (optimise [] pdSrc) =
      some prog := hlow
  refine ⟨?_, ?_, ?_⟩
  · have := senkBlock_korrektC pdCfg (layoutVon piPs) hc hsep pwO 0 pwR pdBytes
      (optimise [] pdSrc) [] [] prog hlow' pwSigma pwEnv30 (pdStart 30) hcode (by rw [hb]; simp)
      (by show natAdresse 4096 = addrOff (natAdresse 4096) 0; exact (addrOff_null _).symm)
      hW pd_envRepr30
    rw [← hb, optimise_sound [] pdSrc pwO 0 pwR pwSigma pwEnv30] at this
    exact this
  · have := senkBlock_korrektC pdCfg (layoutVon piPs) hc hsep pwO 0 pwR pdBytes
      (optimise [] pdSrc) [] [] prog hlow' pwSigma pwEnv60 (pdStart 60) hcode (by rw [hb]; simp)
      (by show natAdresse 4096 = addrOff (natAdresse 4096) 0; exact (addrOff_null _).symm)
      hW pw_envRepr60
    rw [← hb, optimise_sound [] pdSrc pwO 0 pwR pwSigma pwEnv60] at this
    exact this
  · have := senkBlock_ausgang pdCfg (layoutVon piPs) pwO 0 pwR (optimise [] pdSrc) 0 prog hlow
      pwSigma pwEnv95
    rw [optimise_sound [] pdSrc pwO 0 pwR pwSigma pwEnv95] at this
    exact this

/-- JOINT WITNESS for `senkBlock_ite_inv`: the accepted `ite` (at its
    position behind the value and the check) decomposes into the deep
    condition, the two lowered branches, the two checked forward jumps and
    the (empty) rest. -/
theorem senkBlock_ite_inv_zeuge :
    ∃ code j pt pe q,
      senkBedT pdCfg pdBed = some (code, j) ∧
      senkBlock pdCfg (layoutVon piPs) (100 + (encodeAll code).length + 6) pdT = some pt ∧
      senkBlock pdCfg (layoutVon piPs)
        (100 + (encodeAll code).length + 6 + (encodeAll pt).length + 5) pdE = some pe ∧
      sprungOk ((encodeAll pt).length + 5) = true ∧ sprungOk (encodeAll pe).length = true ∧
      senkBlock pdCfg (layoutVon piPs) (100 + (encodeAll (iteCode code j pt pe)).length)
        (.nil : Block pwD pwV false pwCtx [] []) = some q ∧
      iteCode code j pt pe ++ q = pdProg.drop 17 ∧ j = .ge ∧ (encodeAll pt).length = 33 ∧
      (encodeAll pe).length = 46 := by
  have h : senkBlock pdCfg (layoutVon piPs) 100 (.cons (.ite pdBed pdT pdE) .nil :
      Block pwD pwV false pwCtx [] []) = some (pdProg.drop 17) := by decide
  obtain ⟨code, j, pt, pe, q, hb, ht, he, hk1, hk2, hq, hp⟩ :=
    senkBlock_ite_inv pdCfg (layoutVon piPs) pdBed pdT pdE .nil 100 _ h
  have hb' : senkBedT pdCfg pdBed =
      some ([.movReg64 .rax .r10, .movImm64 .rcx (intWort 40), .cmpReg64 .rax .rcx], .ge) := by
    decide
  rw [hb'] at hb
  injection hb with hb
  injection hb with hc hj
  subst hc; subst hj
  have ht' : senkBlock pdCfg (layoutVon piPs) (100 + (encodeAll [Befehl.movReg64 .rax .r10,
      .movImm64 .rcx (intWort 40), .cmpReg64 .rax .rcx]).length + 6) pdT =
      some [.movReg64 .rax .r10, .movImm64 .rcx (intWort 100), .addReg64 .rax .rcx,
        .movImm64 .rbx (natAdresse 8200), .store64 .rbx .rax (BitVec.ofNat 32 0)] := by decide
  rw [ht'] at ht
  injection ht with ht
  subst ht
  have he' : senkBlock pdCfg (layoutVon piPs) (100 + (encodeAll [Befehl.movReg64 .rax .r10,
      .movImm64 .rcx (intWort 40), .cmpReg64 .rax .rcx]).length + 6 +
      (encodeAll [Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 100), .addReg64 .rax .rcx,
        .movImm64 .rbx (natAdresse 8200), .store64 .rbx .rax (BitVec.ofNat 32 0)]).length + 5)
      pdE = some [.movReg64 .rax .r10, .movImm64 .rdx (intWort 40), .subReg64 .rax .rdx,
        .movImm64 .rcx (intWort 500), .addReg64 .rax .rcx,
        .movImm64 .rbx (natAdresse 8200), .store64 .rbx .rax (BitVec.ofNat 32 0)] := by decide
  rw [he'] at he
  injection he with he
  subst he
  exact ⟨_, _, _, _, q, hb', ht', he', hk1, hk2, hq, hp.symm, rfl, by decide, by decide⟩

/-- JOINT WITNESS for `senkWertT_korrekt` and `assignT_lauf` on the depth-3
    value from the image start with `x = 30`: the value code leaves 65 in
    `rax`, keeps `r10`, and the assignment chunk writes 65 at row 0. -/
theorem senkWertT_korrekt_zeuge :
    ∃ p, senkWertT pdCfg pdWert0 = some p ∧ p.length = 7 ∧
      (∃ s', lauf (p.map kanon) (pdStart 30) = some s' ∧
        s'.register pdCfg.dst = intWort 65 ∧ s'.speicher = (pdStart 30).speicher ∧
        s'.register .r10 = intWort 30) ∧
      (∃ s', lauf ((p ++ [Befehl.movImm64 pdCfg.adr (natAdresse 8192),
          Befehl.store64 pdCfg.adr pdCfg.dst (BitVec.ofNat 32 0)]).map kanon) (pdStart 30) =
          some s' ∧ read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 65)) := by
  have hp : senkWertT pdCfg pdWert0 = some (pdProg.take 7) := by decide
  refine ⟨_, hp, by decide, ?_, ?_⟩
  · obtain ⟨s', hrun, hval, hmem, hreg⟩ := senkWertT_korrekt pdCfg pd_cfgOk pdWert0 pwHT pwEnv30
      pwSigma pwSigma (pdStart 30) pd_envRepr30 _ hp
    refine ⟨s', hrun, ?_, hmem, ?_⟩
    · rw [hval]; rfl
    · rw [hreg .r10 (by decide) (by decide)]; rfl
  · have hwr : schreibbar8 (pdStart 30).speicher (natAdresse 8192) = true := by decide
    obtain ⟨s', hrun, hw, -⟩ := assignT_lauf pdCfg pd_cfgOk pdWert0 pwHT (by decide) (by decide)
      _ hp 8192 pwEnv30 pwSigma pwSigma (pdStart 30) pd_envRepr30 hwr
    refine ⟨s', hrun, ?_⟩
    rw [read64_nach_write64 _ _ _ _ hw (by decide)]
    rfl

/-- JOINT WITNESS for `senkBedT_korrekt` and `vergleichT_lauf` on the deep
    check: for `x = 30` the jump condition is false (check holds), for
    `x = 95` it is true (check fails), each matching the source truth. -/
theorem senkBedT_korrekt_zeuge :
    ∃ code j, senkBedT pdCfg pdCheck = some (code, j) ∧ j = .ge ∧
      (∃ s', lauf (code.map kanon) (pdStart 30) = some s' ∧
        wahr? (eval pwSigma pdCheck pwSigma pwEnv30) = true ∧ bedingung j s'.flags = false) ∧
      (∃ s', lauf (code.map kanon) (pdStart 95) = some s' ∧
        wahr? (eval pwSigma pdCheck pwSigma pwEnv95) = false ∧ bedingung j s'.flags = true) := by
  have hb : senkBedT pdCfg pdCheck = some (pdProg.drop 9 |>.take 7, .ge) := by decide
  refine ⟨_, _, hb, rfl, ?_, ?_⟩
  · obtain ⟨-, s', hrun, -, -, hval⟩ := senkBedT_korrekt pdCfg pd_cfgOk pdCheck _ _ hb pwEnv30
      pwSigma pwSigma (pdStart 30) pd_envRepr30
    have ht : wahr? (eval pwSigma pdCheck pwSigma pwEnv30) = true := rfl
    refine ⟨s', hrun, ht, ?_⟩
    rw [ht] at hval
    cases h : bedingung Bedingung.ge s'.flags
    · rfl
    · rw [h] at hval; cases hval
  · obtain ⟨-, s', hrun, -, -, hval⟩ := senkBedT_korrekt pdCfg pd_cfgOk pdCheck _ _ hb pwEnv95
      pwSigma pwSigma (pdStart 95) pw_envRepr95
    have ht : wahr? (eval pwSigma pdCheck pwSigma pwEnv95) = false := rfl
    refine ⟨s', hrun, ht, ?_⟩
    rw [ht] at hval
    cases h : bedingung Bedingung.ge s'.flags
    · rw [h] at hval; cases hval
    · rfl

/-- JOINT WITNESS for `cfgOk_frischListe`, `cfgOk_rsp`, `cfgOk_var_frei`
    and `envRepr_tief` on the widened configuration. -/
theorem cfgOk_frischListe_zeuge :
    FrischListe (abbOf pdCfg (Γ := pwCtx)) pdCfg.dst (pdCfg.tmp :: pdCfg.frei) ∧
      (pdCfg.dst ≠ .rsp ∧ Register.rsp ∉ pdCfg.tmp :: pdCfg.frei) ∧
      abbOf pdCfg (Γ := pwCtx) _ .hier ∉ pdCfg.tmp :: pdCfg.frei ∧
      pdCfg.frei = [.rdx, .rsi] ∧
      EnvRepr pwEnv30 (fun q => if q = .rdx then 77 else pwReg 30 q) (abbOf pdCfg) :=
  ⟨cfgOk_frischListe pdCfg pd_cfgOk, cfgOk_rsp pdCfg pd_cfgOk,
    (cfgOk_var_frei pdCfg pd_cfgOk .hier).2, rfl,
    envRepr_tief pdCfg pd_cfgOk pwEnv30 (pwReg 30) _ pd_envRepr30 (fun q _ hq => by
      have : q ≠ .rdx := fun h => hq (by rw [h]; decide)
      simp [this])⟩

/-- JOINT WITNESS for the special-case theorems: the ORIGINAL fragment's
    value `x + 5` and check `x < 50` lower to the same code under the deep
    lowering with the widened stack (`senkWert_als_tief`,
    `senkBed_als_tief`, `senkAtom_als_tief`). -/
theorem als_tief_zeuge :
    senkTief (abbOf pdCfg) pwWert0 pdCfg.dst (pdCfg.tmp :: pdCfg.frei) =
        senkWert (abbOf pwCfg) pwWert0 pwCfg.dst pwCfg.tmp ∧
      (senkWert (abbOf pwCfg) pwWert0 pwCfg.dst pwCfg.tmp).isSome = true ∧
      senkBedT pdCfg pwCheck = senkBed (abbOf pdCfg) pwCheck pdCfg.dst pdCfg.tmp ∧
      (senkBed (abbOf pdCfg) pwCheck pdCfg.dst pdCfg.tmp).isSome = true ∧
      senkTief (abbOf pdCfg) (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) .rcx [] =
        senkAtom (abbOf pdCfg) (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) .rcx := by
  have hv : senkWert (abbOf pwCfg) pwWert0 pwCfg.dst pwCfg.tmp =
      some [.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx] := by decide
  have hb : senkBed (abbOf pdCfg) pwCheck pdCfg.dst pdCfg.tmp =
      some ([.movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx], .ge) := by
    decide
  have ha : senkAtom (abbOf pdCfg) (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) .rcx =
      some [.movReg64 .rcx .r10] := rfl
  refine ⟨?_, by rw [hv]; rfl, ?_, by rw [hb]; rfl, ?_⟩
  · rw [hv]; exact senkWert_als_tief _ pwWert0 _ _ pdCfg.frei _ hv
  · rw [hb]; exact senkBed_als_tief pdCfg pwCheck _ _ hb
  · rw [ha]; exact senkAtom_als_tief _ _ _ [] _ ha

/-- JOINT WITNESS for `bedingung_negBed`, `sprungOk_addr` and the jump
    lengths: the negation flips every flag state tested, the checked
    forward jump of 38 lands 38 bytes on, a jump of `2^31` is refused. -/
theorem sprung_zeuge :
    bedingung (negBed .l) witnessFlags = !bedingung .l witnessFlags ∧
      negBed .l = .ge ∧ negBed .le = .g ∧ negBed .e = .ne ∧
      sprungOk 38 = true ∧ sprungOk (2 ^ 31) = false ∧
      addrOff (natAdresse 4096) 136 + dispWort (BitVec.ofNat 32 38) =
        addrOff (natAdresse 4096) (136 + 38) ∧
      (encode (.jumpIf32 .ge (BitVec.ofNat 32 38))).length = 6 ∧
      (encode (.jump32 (BitVec.ofNat 32 46))).length = 5 :=
  ⟨bedingung_negBed _ _, rfl, rfl, rfl, by decide, by decide,
    sprungOk_addr _ _ _ (by decide), encode_jumpIf32_len _ _, encode_jump32_len _⟩

/-- JOINT WITNESS for `grund_mem` and `slotAdressen_loc` through the `ite`:
    a block whose ONLY check sits inside the else-branch lists its reason,
    and the written slots of both branches are placed. -/
def pdCheckE : Expr pwD pwCtx [] .bool := .lt (.var .hier) (.lit 80)

def pdSrcG : Block pwD pwV false pwCtx [] [] :=
  .cons (.ite pdBed pdT (.pruefung pdCheckE (.retGrund ⟨0, by decide⟩ pwHΛ) pdE)) .nil

def pdProgG : List Befehl := (senkBlock pdCfg (layoutVon piPs) 0 pdSrcG).getD []

theorem pd_senkG : senkBlock pdCfg (layoutVon piPs) 0 pdSrcG = some pdProgG := by decide

theorem grund_mem_ite_zeuge :
    grundListe pdSrcG = [0] ∧ slotAdressen (layoutVon piPs) pdSrcG = [8200, 8200] ∧
      (compile pdCfg (layoutVon piPs) [] pdSrcG).isSome = true ∧
      ∃ σ', execBlock pwO 0 pwR pdSrcG pwSigma pwEnv95 = .grund σ' ⟨0, by decide⟩ ∧
        (0 : Nat) ∈ grundListe pdSrcG ∧ ∃ t k f, (layoutVon piPs).loc t k f = some 8200 :=
  ⟨by decide, by decide, by decide, _, rfl,
    grund_mem pdCfg (layoutVon piPs) pwO 0 pwR pdSrcG 0 pdProgG pd_senkG pwSigma pwEnv95 _
      ⟨0, by decide⟩ rfl,
    slotAdressen_loc _ pdSrcG 8200 (by decide)⟩

/-! ### The widened program behind the entry sequence

    The same entry as section 8 (`mov r10, rdi`, garbage 999 in `r10`, the
    parameter in `rdi`, a 64-byte stack extent), now in front of the
    widened program: `pipeline_correct_entry` runs the ELSE-branch
    (`x = 60`) from the admitted entry without an `EnvRepr` premise. -/

def pdPro : List Befehl := prolog pdCfg sysvParameter peN

def pdpeBild : Bild := bildFuerP pdCfg (encodeAll pdPro) [] pdSrc pdBytes piPs pwSigma peEs

def pdpeZ (x : Int) : EintrittZustand :=
  { zustand := eintrittStart pdpeBild pdCfg (encodeAll pdPro).length (peReg x) witnessFlags
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := false }

theorem pdpe_prologOk : prologOk pdCfg sysvParameter peN = true := by decide

theorem pdpe_bauOk :
    bauOk .p48 pdCfg (encodeAll (prolog pdCfg sysvParameter pwCtx.length)) (encodeAll pdProg)
      (ohneDoppel (grundListe (optimise [] pdSrc))) piPs peEs = true := by
  decide

theorem pdpe_bedingung60 : eintrittBedingung .nolibcMain peEs 16448 (pdpeZ 60) = true := by
  unfold eintrittBedingung
  decide

theorem pdpe_eintritt :
    prologImageOk pdpeBild pdCfg sysvParameter peN = true ∧
      eintrittOk .p48 pdpeBild 0 .nolibcMain (pdpeZ 60) = true :=
  bildFuerP_eintritt .p48 pdCfg sysvParameter pdProg piPs pwSigma peEs [] pdSrc
    pdpe_prologOk pdpe_bauOk .nolibcMain 16448 (peReg 60) witnessFlags (pdpeZ 60) rfl
    pdpe_bedingung60

theorem pdpe_zulassung60 :
    eintrittZulassung .p48 pdpeBild (effBias pdpeBild.modus) .nolibcMain (pdpeZ 60) [] = true := by
  have hw : wohlgeformt .p48 pdpeBild = true :=
    valX86_wohlgeformt _ _ (imageOk_teile .p48 pdpeBild pdCfg piPs peEs [] pdSrc
      pdBytes (bildFuerP_ok .p48 pdCfg pdPro pdProg piPs pwSigma peEs [] pdSrc
        pdpe_bauOk).1).1
  show (wohlgeformt .p48 pdpeBild && eintrittOk .p48 pdpeBild 0 .nolibcMain (pdpeZ 60) &&
    valTore []) = true
  rw [hw, pdpe_eintritt.2]
  rfl

/-- JOINT WITNESS for `pipeline_correct_entry` over the widened fragment:
    the admitted entry with garbage in `r10` runs the entry sequence, the
    depth-3 value, the deep check and the ELSE-branch of the `ite`; rows
    7/9 become 125/520 and the stack word stays readable and writable. -/
theorem pipeline_correct_entry_ite_zeuge :
    ¬ EnvRepr pwEnv60 (peReg 60) (abbOf pdCfg) ∧
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx), execBlock pwO 0 pwR pdSrc pwSigma pwEnv60 = .ok σ' ρ' ∧
      ∃ n s', laufBytes n (pdpeZ 60).zustand = .weiter s' ∧
        s'.rip = natAdresse (pdCfg.codeBase + pdBytes.length) ∧
        WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pdCfg) ∧
        byteschritt s' = .verweigert ∧
        lesbar8 s'.speicher (eintrittRsp (pdpeZ 60) - BitVec.ofNat 64 8) = true ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 125) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 520) := by
  have hok := bildFuerP_ok .p48 pdCfg pdPro pdProg piPs pwSigma peEs [] pdSrc pdpe_bauOk
  have hval := (kompiliert_geladen .p48 pdCfg piPs piEs [] pdSrc pdBytes pwSigma
    pd_compile pd_bauOk).1
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pd_quelle60
  obtain ⟨n, s', hrun, hrip, hW, hE, hstop, hl, -⟩ := pipeline_correct_entry .p48 pdpeBild pdCfg
    sysvParameter piPs peEs [] pdSrc pdBytes hval hok.1 pdpe_eintritt.1
    pwSigma hok.2.1 .nolibcMain (pdpeZ 60) [] pdpe_zulassung60 (peReg 60) witnessFlags rfl pwEnv60
    (pe_abi 60 (by decide) (by decide)) pwO 0 pwR σ' ρ' hsrc
  refine ⟨?_, σ', ρ', hsrc, n, s', hrun, hrip, hW, hE, hstop, hl,
    pi_lesen _ σ' 0 8192 hW rfl 125 h0, pi_lesen _ σ' 1 8200 hW rfl 520 h1⟩
  intro h
  have := h 0 100 .hier
  revert this
  decide

/-- JOINT WITNESS for `vergleichT_lauf` on the deep check's two operands
    (`(x + 3) - 1` into `rax`, `90` into `rcx`, scratch `[rdx, rsi]`) from
    the image start with `x = 95`: the flags are the SUB flags of 97 and 90. -/
def pdLinks : Expr pwD pwCtx [] (.int (0 + 3 - 1) (100 + 3 - 1)) :=
  .sub (.add (.var .hier) (.lit 3)) (.lit 1)

theorem vergleichT_lauf_zeuge :
    ∃ s', lauf ((pdProg.drop 9).take 7 |>.map kanon) (pdStart 95) = some s' ∧
      s'.speicher = (pdStart 95).speicher ∧ s'.register .r10 = intWort 95 ∧
      s'.flags = (sub64 (intWort 97) (intWort 90)).2 := by
  have ha : senkTief (abbOf pdCfg) pdLinks .rax [.rdx, .rsi] = some ((pdProg.drop 9).take 5) := by
    decide
  have hb : senkTief (abbOf pdCfg) (Expr.lit (D := pwD) (Γ := pwCtx) (Λ := []) 90) .rcx
      [.rdx, .rsi] = some [.movImm64 .rcx (intWort 90)] := rfl
  obtain ⟨s', hrun, hmem, hreg, hfl⟩ := vergleichT_lauf (abbOf pdCfg) pdLinks (.lit 90) .rax .rcx
    [.rdx, .rsi] _ _ (istTief_von_senkTief _ _ _ _ _ ha) (istTief_von_senkTief _ _ _ _ _ hb)
    pwEnv95 pwSigma pwSigma (pdStart 95) (cfgOk_frischListe pdCfg pd_cfgOk) (cfgOk_rsp pdCfg pd_cfgOk)
    pw_envRepr95
  have hp : (pdProg.drop 9).take 7 = (pdProg.drop 9).take 5 ++ [.movImm64 .rcx (intWort 90)] ++
      [Befehl.cmpReg64 .rax .rcx] := by decide
  refine ⟨s', by rw [hp]; exact hrun, hmem, ?_, ?_⟩
  · rw [hreg .r10 (by decide) (by decide)]; rfl
  · rw [hfl]; rfl

/-- JOINT WITNESS for the structural helpers of the widened lowering on the
    widened program: straight-line deep code (`istTief_gerade`,
    `senkWertT_gerade`), the `ite` code layout (`encodeAll_iteCode`,
    `encodeAll_iteCode_len`), the assignment equation (`senkBlock_assign`),
    the source `ite` step and the two `cons` continuations
    (`execStmt_ite`, `execBlock_cons_stmtOk`, `execBlock_cons_stmtGrund`),
    the written-slot equation (`slotAdressen_cons_eq`) and the decided
    scratch facts (`cfgOk_frei_liste`). -/
theorem hilfs_zeuge :
    ((pdProg.take 7).all gerade = true) ∧
    ((encodeAll (iteCode [.movReg64 .rax .r10, .movImm64 .rcx (intWort 40), .cmpReg64 .rax .rcx] .ge
        ((pdProg.drop 21).take 5) ((pdProg.drop 27).take 7))).length = 106 ∧
      encodeAll (iteCode [.movReg64 .rax .r10, .movImm64 .rcx (intWort 40), .cmpReg64 .rax .rcx]
        .ge ((pdProg.drop 21).take 5) ((pdProg.drop 27).take 7)) = encodeAll (pdProg.drop 17)) ∧
    (senkBlock pdCfg (layoutVon piPs) 0 pdSrc = some pdProg) ∧
    (execStmt pwO 0 pwR (.ite pdBed pdT pdE) pwSigma pwEnv60 =
      execBlock pwO 0 pwR pdE pwSigma pwEnv60) ∧
    (∃ σ' ρ', execStmt pwO 0 pwR (.ite pdBed pdT pdE) pwSigma pwEnv60 = .ok σ' ρ' ∧
      execBlock pwO 0 pwR (.cons (.ite pdBed pdT pdE) .nil : Block pwD pwV false pwCtx [] [])
        pwSigma pwEnv60 = .ok σ' ρ' ∧ (σ'.slots () 1 ()).n = 520) ∧
    (∃ σ', execBlock pwO 0 pwR pdSrcG pwSigma pwEnv95 = .grund σ' ⟨0, by decide⟩) ∧
    slotAdressen (layoutVon piPs) pdSrc = [8192, 8200, 8200] ∧
    (pdCfg.frei.Nodup ∧ ∀ r ∈ pdCfg.frei, r ∉ pdCfg.regs ∧ r ≠ pdCfg.dst ∧ r ≠ pdCfg.tmp ∧
      r ≠ pdCfg.adr ∧ r ≠ .rsp) := by
  have hp : senkWertT pdCfg pdWert0 = some (pdProg.take 7) := by decide
  refine ⟨senkWertT_gerade pdCfg pdWert0 _ hp, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, cfgOk_frei_liste pdCfg pd_cfgOk⟩
  · rw [encodeAll_iteCode_len]; decide
  · rw [encodeAll_iteCode]; decide
  · exact (senkBlock_assign (V := pwV) pdCfg (layoutVon piPs) () () pwIdx0 pdWert0 pwHw pwHL
      _ 0).trans (by decide)
  · rw [execStmt_ite]; rfl
  · refine ⟨_, _, rfl, ?_, rfl⟩
    exact execBlock_cons_stmtOk pwO 0 pwR _ .nil pwSigma pwEnv60 _ _ rfl
  · exact ⟨_, execBlock_cons_stmtGrund pwO 0 pwR _ .nil pwSigma _ pwEnv95 ⟨0, by decide⟩ rfl⟩
  · unfold pdSrc; rw [slotAdressen_cons_eq _ _ _ rfl]; decide

/-! ### Poison probes of the widened fragment: every one is REFUSED -/

/-- WRONG BRANCH DISPLACEMENT: the candidate with the `ite` jump one byte
    too far (39 instead of 38) is refused although it decodes; so is the
    jump over the else-block one byte short. -/
def pdProgFalschIte : List Befehl :=
  pdProg.take 20 ++ [.jumpIf32 .ge (BitVec.ofNat 32 39)] ++ pdProg.drop 21

def pdProgFalschEnde : List Befehl :=
  pdProg.take 26 ++ [.jump32 (BitVec.ofNat 32 45)] ++ pdProg.drop 27

theorem gift_ite_verschiebung :
    pdProg[20]? = some (.jumpIf32 .ge (BitVec.ofNat 32 38)) ∧
      decodeAll (encodeAll pdProgFalschIte).length (encodeAll pdProgFalschIte) =
        some pdProgFalschIte ∧
      validate pdCfg (layoutVon piPs) [] pdSrc (encodeAll pdProgFalschIte) = false ∧
      pdProg[26]? = some (.jump32 (BitVec.ofNat 32 46)) ∧
      validate pdCfg (layoutVon piPs) [] pdSrc (encodeAll pdProgFalschEnde) = false := by
  refine ⟨by decide, decodeAll_encodeAll _ _ (length_le_encodeAll _), by decide, by decide,
    by decide⟩

/-- TAMPERED JUMP BYTE: flipping the low displacement byte of the `ite`
    jump in the candidate BYTES is refused. -/
def pdSprungOffset : Nat := (encodeAll (pdProg.take 20)).length + 2

theorem gift_sprung_byte :
    pdSprungOffset = 118 ∧ pdBytes[pdSprungOffset]? = some (natByte 38) ∧
      validate pdCfg (layoutVon piPs) [] pdSrc (pdBytes.set pdSprungOffset (natByte 39)) =
        false := by
  decide

/-- SCRATCH EXHAUSTION: with one scratch register (`frei = [rdx]`) the
    depth-3 value does not fit and the compile REFUSES (no spilling); with
    the original configuration (`frei = []`) too. The deep lowering itself
    names the refusal. -/
theorem gift_erschoepft :
    compile { pdCfg with frei := [.rdx] } (layoutVon piPs) [] pdSrc = none ∧
      compile { pdCfg with frei := [] } (layoutVon piPs) [] pdSrc = none ∧
      senkWertT { pdCfg with frei := [.rdx] } pdWert0 = none ∧
      (senkWertT pdCfg pdWert0).isSome = true := by
  decide

/-- OUT-OF-RANGE COMPARISON: an operand whose TYPE leaves the signed 64-bit
    window (`x + (2^63 - 50)`, range up to `2^63 + 50`) is refused by the
    decided side condition, although its tree lowers; the program around
    it is refused. -/
def pdCheckWeit : Expr pwD pwCtx [] .bool :=
  .lt (.add (.var .hier) (.lit (2 ^ 63 - 50))) (.lit 0)

def pdSrcWeit : Block pwD pwV false pwCtx [] [] :=
  .pruefung pdCheckWeit (.retGrund ⟨0, by decide⟩ pwHΛ) .nil

theorem gift_vergleich_fenster :
    (senkVergleich (abbOf pdCfg) pdCheckWeit pdCfg.dst (pdCfg.tmp :: pdCfg.frei)).isSome = true ∧
      imFensterB pdCheckWeit = false ∧ senkBedT pdCfg pdCheckWeit = none ∧
      compile pdCfg (layoutVon piPs) [] pdSrcWeit = none := by
  decide

/-- A NON-COMPARISON `ite` condition (the literal `true`, a negation) and
    an `ite` with an unsupported statement in a branch are refused. -/
def pdSrcWahr : Block pwD pwV false pwCtx [] [] := .cons (.ite .wahr pdT pdE) .nil

def pdSrcNicht : Block pwD pwV false pwCtx [] [] := .cons (.ite (.nicht pdBed) pdT pdE) .nil

def pdSrcZweig : Block pwD pwV false pwCtx [] [] :=
  .cons (.ite pdBed (.cons (.assignVar .hier (.var .hier)) .nil) pdE) .nil

theorem gift_ite_form :
    compile pdCfg (layoutVon piPs) [] pdSrcWahr = none ∧
      compile pdCfg (layoutVon piPs) [] pdSrcNicht = none ∧
      compile pdCfg (layoutVon piPs) [] pdSrcZweig = none := by
  decide

/-- The original configuration has no extra scratch register, so its
    check is the original one (`cfgOk_ohne_frei`); with the stack it still
    passes. -/
theorem cfgOk_ohne_frei_zeuge :
    cfgOk pwCfg = decide (pwCfg.dst ∉ pwCfg.regs ∧ pwCfg.tmp ∉ pwCfg.regs ∧
      pwCfg.adr ∉ pwCfg.regs ∧ pwCfg.dst ≠ pwCfg.tmp ∧ pwCfg.dst ≠ pwCfg.adr ∧
      pwCfg.tmp ≠ pwCfg.adr ∧ pwCfg.dst ≠ .rsp ∧ pwCfg.tmp ≠ .rsp ∧ pwCfg.adr ≠ .rsp) ∧
      cfgOk pwCfg = true ∧ cfgOk pdCfg = true :=
  ⟨cfgOk_ohne_frei pwCfg rfl, by decide, pd_cfgOk⟩

/-- A scratch register that is a variable register, or `rsp`, or doubled,
    or the scratch register `tmp`: the configuration check refuses it. -/
theorem gift_frei_cfg :
    cfgOk { pdCfg with frei := [.r10] } = false ∧ cfgOk { pdCfg with frei := [.rsp] } = false ∧
      cfgOk { pdCfg with frei := [.rdx, .rdx] } = false ∧
      cfgOk { pdCfg with frei := [.rcx] } = false := by
  decide

/-! ## CUTS (what this witness file does NOT show)

   - One declaration, two programs, one layout: the witnesses instantiate
     the generic theorems of `PipelineImage.lean`; they prove nothing for
     other programs by themselves.
   - The image is built by `bildFuer`/`bildFuerP`; the first candidate's
     bytes are written out by hand, the two-reason program's are named as
     the compiler's own output (`pw3Prog`); no Rust producer is run.
   - The completeness witnesses check the decided side conditions
     (`pw3_bauOk`, `pe_bauOk`) by computation and then apply the GENERAL
     theorems; `pw3_imageOk_rechnung` cross-checks one image check by
     computation as well.
   - The entry witness uses one stated ABI order (`sysvParameter`) and one
     entry kind (`nolibcMain`); the parameter arrives in `rdi` by the
     witness's own choice of entry registers (`AbiArgs` is the caller's
     duty, not shown for any real caller).
   - All runs are computed by `decide` over the model `Speicher`; no
     hardware and no operating-system loader is involved.
   - Section 10 (the widened fragment) shows ONE program with a depth-3
     value, one deep check and one `ite` whose branches each hold one
     store, under one scratch stack `[rdx, rsi]`; nested `ite`, an `ite`
     inside an `ite` branch's check, `<=`/`=` conditions and `neg` are
     covered by the generic theorems but not run here. The poison probes
     show refusal by the validator or the compiler, not that a tampered
     image would misbehave. -/

#print axioms pi_layout_gleich
#print axioms pi_validate
#print axioms pi_gruende
#print axioms pi_bild_form
#print axioms pi_imageOk
#print axioms pi_weltOk
#print axioms pi_start_lesen
#print axioms pi_lauf30
#print axioms pi_lauf70
#print axioms pi_lesen
#print axioms pipeline_correct_loaded_zeuge
#print axioms pipeline_refuses_loaded_zeuge
#print axioms pipeline_loaded_ausgang_zeuge
#print axioms pw2_validate
#print axioms pw2_gruende
#print axioms pw2_imageOk
#print axioms pw2_weltOk
#print axioms pipeline_refuses_loaded_zeuge_grund1
#print axioms pw2_lauf70
#print axioms sepB_zeuge
#print axioms worldRep_von_zeuge
#print axioms codeAtB_zeuge
#print axioms layoutVon_zeuge
#print axioms imageOk_folgen_zeuge
#print axioms grund_mem_zeuge
#print axioms rahmen_zeuge
#print axioms schritt_rahmen_zeuge
#print axioms byteschritt_rahmen_zeuge
#print axioms byteschritt_stop_zeuge
#print axioms slotWort_zeuge
#print axioms byteRahmen_write64_zeuge
#print axioms byteRahmen_trans_zeuge
#print axioms gift_ueberlapp
#print axioms gift_code_schreibbar
#print axioms gift_code_als_daten
#print axioms gift_ohne_stub
#print axioms gift_stub_byte
#print axioms gift_code_byte
#print axioms gift_falscher_grund
#print axioms gift_platz_ueberlapp
#print axioms gift_platz_aussen
#print axioms gift_welt
#print axioms gift_kein_stop
#print axioms gift_fremdes_bild

#print axioms pw3_compile
#print axioms pw3_laenge
#print axioms pw3_gruende
#print axioms pw3_bauOk
#print axioms kompiliert_geladen_zeuge
#print axioms pw3_imageOk_rechnung
#print axioms pw3_bild_form
#print axioms pw3_quelle30
#print axioms pw3_quelle55
#print axioms pw3_quelle70
#print axioms pw_envRepr55
#print axioms pw3_laeufe
#print axioms pipeline_correct_compiled_zeuge
#print axioms pipeline_refuses_compiled_zeuge
#print axioms bildFuer_ok_zeuge
#print axioms gift_stride_eins
#print axioms gift_stride_zehn
#print axioms gift_ausgang_in_daten
#print axioms gift_bau_platz
#print axioms ohneDoppel_probe
#print axioms pe_pro
#print axioms pe_prologOk
#print axioms pe_bauOk
#print axioms pe_bedingung30
#print axioms pe_bedingung70
#print axioms bildFuerP_eintritt_zeuge
#print axioms pe_wohlgeformt
#print axioms pe_zulassung30
#print axioms pe_zulassung70
#print axioms pe_abi
#print axioms pe_ohne_prolog
#print axioms pe_lauf
#print axioms pipeline_correct_entry_zeuge
#print axioms pipeline_refuses_entry_zeuge
#print axioms gift_prolog_klobber
#print axioms gift_prolog_rsp
#print axioms gift_prolog_ohne_abi
#print axioms gift_prolog_byte
#print axioms gift_stapel_schief
#print axioms gift_stapel_aussen
#print axioms gift_eintritt_guard
#print axioms gs3_eq
#print axioms gs3_nodup
#print axioms F3
#print axioms B3code_mem
#print axioms B3stub1_mem
#print axioms baueBildP_zeuge
#print axioms baueBildP_lade_zeuge
#print axioms loader_zeuge
#print axioms stub_mem_v_zeuge
#print axioms stub_vorhanden_zeuge
#print axioms stub_bytes_zeuge
#print axioms daten_mem_v_zeuge
#print axioms daten_vorhanden_zeuge
#print axioms datenChunk_zeuge
#print axioms kette_zeuge
#print axioms trennung_zeuge
#print axioms worte_zeuge
#print axioms compile_zeuge
#print axioms prolog_zeuge
#print axioms zuege_lauf_zeuge
#print axioms prolog_lauf_zeuge
#print axioms prolog_envRepr_zeuge
#print axioms exitAdr_zeuge
#print axioms pipeline_refuses_eins_zeuge

#print axioms pd_cfgOk
#print axioms pd_compile
#print axioms pd_validate
#print axioms pd_laenge
#print axioms pd_gruende
#print axioms pd_bauOk
#print axioms pw_envRepr60
#print axioms pw_envRepr95
#print axioms pd_envRepr30
#print axioms pd_quelle30
#print axioms pd_quelle60
#print axioms pd_quelle95
#print axioms pd_laeufe
#print axioms pipeline_correct_compiled_ite_zeuge
#print axioms pipeline_refuses_compiled_tief_zeuge
#print axioms senkBlock_korrektC_zeuge
#print axioms senkBlock_ite_inv_zeuge
#print axioms senkWertT_korrekt_zeuge
#print axioms senkBedT_korrekt_zeuge
#print axioms cfgOk_frischListe_zeuge
#print axioms als_tief_zeuge
#print axioms sprung_zeuge
#print axioms pd_senkG
#print axioms grund_mem_ite_zeuge
#print axioms pdpe_prologOk
#print axioms pdpe_bauOk
#print axioms pdpe_bedingung60
#print axioms pdpe_eintritt
#print axioms pdpe_zulassung60
#print axioms pipeline_correct_entry_ite_zeuge
#print axioms vergleichT_lauf_zeuge
#print axioms hilfs_zeuge
#print axioms gift_ite_verschiebung
#print axioms gift_sprung_byte
#print axioms gift_erschoepft
#print axioms gift_vergleich_fenster
#print axioms gift_ite_form
#print axioms cfgOk_ohne_frei_zeuge
#print axioms gift_frei_cfg

end Gabbro.Grammatik.X86.PipelineImageWitnesses
