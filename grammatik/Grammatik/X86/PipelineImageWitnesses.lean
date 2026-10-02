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
             instantiated jointly (sections 7-9).

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
     hardware and no operating-system loader is involved. -/

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

end Gabbro.Grammatik.X86.PipelineImageWitnesses
