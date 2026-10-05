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

/-! ## 2. Call family: the admitted caller frame plus validated callee
    bytes, over the loaded image.

    The joint validator (`rufExecOk`: admitted frame, single-assignment
    shape, recomputed bytes) and the loaded premises (`imageOk` over
    the same layout and certificate list, `weltOk`) feed the accepted
    `einzelRuf_korrekt`: the fetched run from the loader's state
    reaches the code end with the REAL `execBlock` outcome represented
    and every callee-saved register preserved. Every premise is
    consumed. -/

/-- CALL CORRECTNESS OVER THE LOADED IMAGE: frame admission plus the
    fetched callee run with callee-saved preservation. -/
theorem ruf_correct_loaded {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (p : Profil) (bild : Bild) (c : PipeCfg)
    (ps : List (Platz D)) (es : List TabLayout)
    (b : Belegung) (rh : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (bytes : List Byte)
    (hval : rufExecOk b rh nArgs benutztRot c (layoutVon ps)
      ((.cons (.assignSlot t f i e hw hL) .nil : Block D V l Γ Λ Λ)) bytes = true)
    (himg : imageOk p bild c ps es []
      ((.cons (.assignSlot t f i e hw hL) .nil : Block D V l Γ Λ Λ)) bytes = true)
    (σ : World D) (hwelt : weltOk bild ps σ = true)
    (hfremd : calleeFremd c = true)
    (reg : Register → Wort) (fl : Flags) (ρ : Env D Γ)
    (hE : EnvRepr ρ reg (abbOf c))
    (O : Orakel D) (passes : Nat)
    (R : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R
      ((.cons (.assignSlot t f i e hw hL) .nil : Block D V l Γ Λ Λ)) σ ρ =
      (.ok σ' ρ' : Ausgang V l Γ)) :
    rufOk b rh nArgs benutztRot = true ∧
    ∃ n s', laufBytes n (startZustand bild c reg fl) = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c) ∧
      (∀ q, q ∈ calleeGerettet →
        s'.register q = (startZustand bild c reg fl).register q) := by
  have hsep := imageOk_layoutSep p bild c ps es [] _ _ himg
  have hcode := imageOk_codeAt p bild c ps es [] _ _ himg
  have hW := imageOk_worldRep p bild c ps es [] _ _ himg σ hwelt
  have hrip : (startZustand bild c reg fl).rip = natAdresse c.codeBase := rfl
  exact einzelRuf_korrekt b rh nArgs benutztRot c (layoutVon ps) t f i e hw hL bytes
    hval hsep hfremd O passes R σ ρ (startZustand bild c reg fl) hcode hrip hW hE
    σ' ρ' hsrc

/-! ## 2b. Call witness image and joint witness.

    The single-assignment callee body gets its own built image
    (placements and extents shared with the pipeline witness image);
    validator, image and world checks all hold by computation. -/

/-- The callee image: the built image of the single-assignment body. -/
def cwBild : Bild := bildFuer cwCfg [] cwBody cwBytes piPs pwSigma piEs

/-- The code validator accepts the callee over the placement layout. -/
theorem cw_validate_pi : validate cwCfg (layoutVon piPs) [] cwBody cwBytes = true := by
  decide

/-- THE CALLEE IMAGE CHECK ACCEPTS, by computation. -/
theorem cw_imageOk : imageOk .p48 cwBild cwCfg piPs piEs [] cwBody cwBytes = true := by
  decide

/-- The loaded callee image represents the initial world. -/
theorem cw_weltOk : weltOk cwBild piPs pwSigma = true := by
  decide

/-- The joint validator accepts the callee over the placement layout. -/
theorem cw_rufExec_pi :
    rufExecOk rufWitBelegung rufWitRahmen 7 false cwCfg (layoutVon piPs)
      cwBody cwBytes = true := by
  decide

/-- JOINT WITNESS for `ruf_correct_loaded`: every premise holds
    jointly on the single-assignment callee (admitted seven-argument
    frame, joint validator, image and world checks by computation,
    working registers off the callee-saved set, the REAL source run
    that changes row 7 -> 35); the theorem then gives frame admission
    plus the fetched loaded run with callee-saved preservation,
    beside the reached frame saves (observably changed result byte,
    reloaded argument word). -/
theorem ruf_correct_loaded_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx) (n : Nat) (s' : Zustand),
      pwV.schreibt () = true ∧
      rufExecOk rufWitBelegung rufWitRahmen 7 false cwCfg (layoutVon piPs)
        cwBody cwBytes = true ∧
      imageOk .p48 cwBild cwCfg piPs piEs [] cwBody cwBytes = true ∧
      weltOk cwBild piPs pwSigma = true ∧
      calleeFremd cwCfg = true ∧
      EnvRepr pwEnv30 (cwReg 30) (abbOf cwCfg) ∧
      execBlock pwO 0 pwR cwBody pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      rufOk rufWitBelegung rufWitRahmen 7 false = true ∧
      laufBytes n (startZustand cwBild cwCfg (cwReg 30) witnessFlags) = .weiter s' ∧
      s'.rip = natAdresse (cwCfg.codeBase + cwBytes.length) ∧
      WorldRep (layoutVon piPs) s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf cwCfg) ∧
      (∀ q, q ∈ calleeGerettet → s'.register q = (cwReg 30) q) ∧
      speicherZeuge.bytes (rufWitRahmen.schlitzAddr 0) ≠
        rufWitM1.bytes (rufWitRahmen.schlitzAddr 0) ∧
      ladeWort rufWitM2 rufWitRahmen 7 = some 42 := by
  obtain ⟨σW, ρW, hok, h35, -⟩ := cw_quelle
  obtain ⟨hv0, -⟩ := pw_quelle_vorher
  obtain ⟨hruf, m, sW, hrun, hrip', hW, hE', hcallee⟩ :=
    ruf_correct_loaded .p48 cwBild cwCfg piPs piEs rufWitBelegung rufWitRahmen 7
      false () () pwIdx0 pwWert0 pwHw pwHL cwBytes cw_rufExec_pi cw_imageOk pwSigma
      cw_weltOk cw_fremd (cwReg 30) witnessFlags pwEnv30 cw_envRepr pwO 0 pwR σW ρW hok
  exact ⟨σW, ρW, m, sW, pwHw, cw_rufExec_pi, cw_imageOk, cw_weltOk, cw_fremd,
    cw_envRepr, hok, hv0, h35, hruf, hrun, hrip', hW, hE', hcallee,
    rufWit_wechselt, rufWit_rundreise⟩

/-! ## 3. Table family: anchored loads and stores, over loaded memory.

    A lowered store (`senkSchreiben`) runs from a state whose memory
    IS the loaded mapping (`hst`), with the code bytes (`CodeAt`,
    W^X per byte) and the decided anchor checks (`tabOkB`,
    `tabWeltB`, projected through `tabWorldRep`) feeding the accepted
    `tabellen_schreiben_laufBytes`. Every premise is consumed. -/

/-- TABLE-STORE CORRECTNESS OVER LOADED MEMORY: the fetched byte run
    of a lowered store reaches the code end with the real `execStmt`
    outcome represented. -/
theorem tabellen_correct_loaded {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (bild : Bild) (c : PipeCfg) (A : TabAnker D)
    (hc : cfgOk c = true) (hsep : ankerSepB A = true)
    (flat pre post : List Byte) (p : List Befehl)
    (s : Stmt D V l Γ Λ Λ)
    (ρ : Env D Γ) (σ : World D) (st : Zustand)
    (hst : st.speicher = ladung bild)
    (hrip0 : st.rip = addrOff (natAdresse c.codeBase) pre.length)
    (hE : EnvRepr ρ st.register (abbOf c))
    (hokB : tabOkB A (ladung bild) = true) (hwB : tabWeltB A (ladung bild) σ = true)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (h : senkSchreiben A c s = some p) (hgp : p.all gerade = true)
    (hcode : CodeAt (ladung bild) (natAdresse c.codeBase) flat)
    (hf : flat = pre ++ encodeAll p ++ post) :
    ∃ n s' σ', laufBytes n st = .weiter s' ∧
      s'.rip = addrOff (natAdresse c.codeBase) (pre.length + (encodeAll p).length) ∧
      execStmt O passes R s σ ρ = .ok σ' ρ ∧
      WorldRep (tabLayout A) s'.speicher σ' ∧ EnvRepr ρ s'.register (abbOf c) := by
  have hW := tabWorldRep A (ladung bild) σ hokB hwB
  have hcode' : CodeAt st.speicher (natAdresse c.codeBase) flat := by
    rw [hst]
    exact hcode
  have hW' : WorldRep (tabLayout A) st.speicher σ := by
    rw [hst]
    exact hW
  exact tabellen_schreiben_laufBytes A c hc hsep s ρ σ st hE hW' O passes R flat
    pre post p h hgp hcode' hf hrip0

/-! ## 3b. Table witness image and joint witness.

    A minimal two-section image (code plus the four-slot data extent)
    whose loaded bytes carry word 7 in every anchored slot; the
    decided code, admission and world checks all hold by computation.
    No full `imageOk` is needed: the table chunk theorem consumes
    exactly these three checks. -/

/-- Witness code section: the lowered store bytes at 4096. -/
def zeBildCode : Abschnitt :=
  { dateiOff := 0, dateiLen := zeBytes.length, vaddr := 4096,
    memLen := zeBytes.length, lesbar := false, schreibbar := false,
    ausfuehrbar := true, ausr := 1 }

/-- Witness data section: four slots of word 7 at 8192. -/
def zeBildDaten : Abschnitt :=
  { dateiOff := zeBytes.length, dateiLen := 32, vaddr := 8192, memLen := 32,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 8 }

/-- Witness file: code bytes plus the four word-7 slots. -/
def zeBildDatei : List Byte :=
  zeBytes ++ (List.range 32).map fun i => wortByte 7 (i % 8)

/-- The table witness image. -/
def zeBild : Bild :=
  { datei := zeBildDatei
    abschnitte := [zeBildCode, zeBildDaten]
    reloks := []
    eintraege := [4096]
    modus := .fest }

/-- DECIDED CODE over the loaded witness image. -/
theorem zeBild_codeAtB :
    codeAtB (ladung zeBild) (natAdresse zeCfg.codeBase) zeBytes = true := by
  decide

/-- LOADED CODE for the witness image. -/
theorem zeBild_codeAt :
    CodeAt (ladung zeBild) (natAdresse zeCfg.codeBase) zeBytes :=
  codeAtB_sound _ _ _ zeBild_codeAtB

/-- DECIDED ADMISSION over the loaded witness image. -/
theorem zeBild_okB : tabOkB zeA (ladung zeBild) = true := by
  decide

/-- DECIDED WORLD CHECK over the loaded witness image. -/
theorem zeBild_weltB : tabWeltB zeA (ladung zeBild) zeSigma = true := by
  decide

/-- The loaded start state is at the code base. -/
theorem zeBild_rip :
    (startZustand zeBild zeCfg zeReg witnessFlags).rip =
      addrOff (natAdresse zeCfg.codeBase) ([] : List Byte).length := by
  have h1 : (startZustand zeBild zeCfg zeReg witnessFlags).rip =
      natAdresse zeCfg.codeBase := rfl
  have h2 : natAdresse zeCfg.codeBase =
      addrOff (natAdresse zeCfg.codeBase) ([] : List Byte).length := by
    simp [addrOff_null]
  exact h1.trans h2

/-- JOINT WITNESS for `tabellen_correct_loaded`: every premise holds
    jointly on the two-field record program (checked configuration
    and separation, decided checks over the loaded witness image,
    recomputed store code, the REAL `execStmt` run that writes 42);
    the theorem then gives the fetched loaded run with the outcome
    represented, beside the memory-changing run (byte 7 becomes 42). -/
theorem tabellen_correct_loaded_zeuge :
    ∃ (σ' : World zeD) (n : Nat) (s' : Zustand),
      cfgOk zeCfg = true ∧ ankerSepB zeA = true ∧
      EnvRepr (D := zeD) (Env.nil : Env zeD []) zeReg (abbOf zeCfg) ∧
      tabOkB zeA (ladung zeBild) = true ∧
      tabWeltB zeA (ladung zeBild) zeSigma = true ∧
      senkSchreiben zeA zeCfg zeWrite = some zeStoreProg ∧
      zeStoreProg.all gerade = true ∧
      CodeAt (ladung zeBild) (natAdresse zeCfg.codeBase) zeBytes ∧
      zeBytes = ([] : List Byte) ++ encodeAll zeStoreProg ++ [] ∧
      execStmt zeO 0 zeR zeWrite zeSigma (Env.nil : Env zeD []) = .ok σ' Env.nil ∧
      (σ'.slots false 1 true).n = 42 ∧
      laufBytes n (startZustand zeBild zeCfg zeReg witnessFlags) = .weiter s' ∧
      s'.rip = addrOff (natAdresse zeCfg.codeBase)
        (([] : List Byte).length + (encodeAll zeStoreProg).length) ∧
      WorldRep (tabLayout zeA) s'.speicher σ' ∧
      EnvRepr (D := zeD) (Env.nil : Env zeD []) s'.register (abbOf zeCfg) ∧
      zeV.schreibt false = true ∧
      zeRunChange := by
  obtain ⟨σ', hsrc, h42⟩ := zeSrcWrite
  have hst : (startZustand zeBild zeCfg zeReg witnessFlags).speicher =
      ladung zeBild := rfl
  obtain ⟨n, sW, σW, hrun, hrip, hsrcW, hW, hE2⟩ :=
    tabellen_correct_loaded zeBild zeCfg zeA zeCfgOk zeSep zeBytes [] [] zeStoreProg
      zeWrite Env.nil zeSigma (startZustand zeBild zeCfg zeReg witnessFlags) hst
      zeBild_rip zeEnvRepr zeBild_okB zeBild_weltB zeO 0 zeR zeLowWrite zeGerade
      zeBild_codeAt zeBytesEq
  have heq : σW = σ' := by
    have h := hsrcW.symm.trans hsrc
    cases h
    rfl
  subst heq
  exact ⟨σW, n, sW, zeCfgOk, zeSep, zeEnvRepr, zeBild_okB, zeBild_weltB, zeLowWrite,
    zeGerade, zeBild_codeAt, zeBytesEq, hsrc, h42, hrun, hrip, hW, hE2, zeHw,
    zeRunChangeProof⟩

/- CUTS (skeleton):
   Only the shared loaded-code predicate so far. Per-family
   correctness, refusals, probes and witnesses follow in pieces.
-/

#print axioms fragmentBytesGeladen

end Gabbro.Grammatik.X86.PipelineLoadedAll
