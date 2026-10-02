/-
  File:      Grammatik/X86/PipelineImageWitnesses.lean
  Subject:   Joint non-degenerate witnesses and poison probes for
             `PipelineImage.lean`: the pipeline witness program of
             `PipelineWitnesses.lean` taken through image construction,
             the decided image check (by computation), the existing loader,
             and the fetched byte run to the defined stop -- in the success
             case and in the refusal case through the exit stub, with
             memory changes. A second program refuses with reason 1, so the
             exit register carries a nonzero reason.

  Reused: `PipelineWitnesses` (declaration, contract, program, certificate,
  configuration, candidate bytes, world, environments) and everything of
  `PipelineImage.lean`. Nothing here is on the trust path (witness only).
-/
import Grammatik.X86.PipelineImage
import Grammatik.X86.PipelineWitnesses

namespace Gabbro.Grammatik.X86.PipelineImageWitnesses

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineImage

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
          s'.rip = natAdresse (pwCfg.exitBase + r.val + 10) ∧
          s'.register exitReg = intWort r.val ∧
          WorldRep (layoutVon piPs) s'.speicher σ'))) ∧
    (∃ n s', laufBytes n (piStart 70) = .weiter s' ∧ byteschritt s' = .verweigert ∧
      ((s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
          ∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .ok σ' ρ' ∧
            WorldRep (layoutVon piPs) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pwCfg)) ∨
        (∃ σ' r, execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' r ∧
          s'.rip = natAdresse (pwCfg.exitBase + r.val + 10) ∧
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
        (⟨(), 0, (), 8192⟩ : Platz pwD).a + 8 ≤ pwCfg.exitBase + g ∨
          pwCfg.exitBase + g + 10 ≤ (⟨(), 0, (), 8192⟩ : Platz pwD).a) ∧
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

/-! ## CUTS (what this witness file does NOT show)

   - One declaration, two programs, one layout: the witnesses instantiate
     the generic theorems of `PipelineImage.lean`; they prove nothing for
     other programs by themselves.
   - The image is built by `bildFuer` and the candidate bytes are written
     out by hand; no Rust producer is run.
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

end Gabbro.Grammatik.X86.PipelineImageWitnesses
