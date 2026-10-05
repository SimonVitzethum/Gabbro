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
import Grammatik.X86.Pipeline.Kern.Pipeline
import Grammatik.X86.Pipeline.Kern.PipelineImage
import Grammatik.X86.Laden.LoadedExecution
import Grammatik.X86.Pipeline.Binden.PipelineLink
import Grammatik.X86.Pipeline.Kern.PipelineRegAlloc
import Grammatik.X86.Pipeline.Aufrufe.PipelineSpill
import Grammatik.X86.Pipeline.Aufrufe.PipelineCalls
import Grammatik.X86.Pipeline.Aufrufe.PipelineCallsExec
import Grammatik.X86.Pipeline.Ausdruecke.PipelineTables
import Grammatik.X86.Pipeline.Ausdruecke.PipelineFloat
import Grammatik.X86.Pipeline.Ablauf.PipelineWork
import Grammatik.X86.Pipeline.Kern.PipelineWitnesses
import Grammatik.X86.Pipeline.Kern.PipelineImageWitnesses

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

/-! ## 4. Work family: validated bytes with retired-work and
    named-time bounds, over loaded memory.

    The validator closing (`pipeline_arbeit_korrekt`: fetched run
    agreement plus validated-bytes equation plus work/time bounds)
    runs from a state whose memory IS the loaded mapping (`hst`);
    the code, representation and entry premises are the loaded ones.
    Named timing stays a hardware assumption. Every premise is
    consumed. -/

/-- WORK CORRECTNESS OVER LOADED MEMORY: the fetched run reaches the
    code end with world and environment represented, the bytes are
    the encoding of the counted program, and retired work and named
    time are bounded. -/
theorem arbeit_correct_loaded {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (bild : Bild) (c : PipeCfg) (L : Layout D)
    (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (prog : List Befehl)
    (hval : validate c L certs src bytes = true)
    (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (st : Zustand)
    (hst : st.speicher = ladung bild)
    (hrip0 : st.rip = natAdresse c.codeBase)
    (hcode : CodeAt (ladung bild) (natAdresse c.codeBase) bytes)
    (hW : WorldRep L (ladung bild) σ) (hE : EnvRepr ρ st.register (abbOf c))
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ')
    (hdec : decodeAll bytes.length bytes = some prog)
    (prof : HardwareProfil) (srcB B tt k : Nat)
    (hDeck : Deckung pipeSummary srcB (decodiertZu prog))
    (hCost : laufKosten prof (decodiertZu prog) = some tt)
    (hb : ∀ dd ∈ decodiertZu prog,
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B)
    (hk : expandBound pipeSummary srcB = some k) :
    (∃ n s', laufBytes n st = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c)) ∧
    bytes = encodeAll prog ∧
    targetWork prog ≤ k ∧ tt ≤ B * k := by
  have hcode' : CodeAt st.speicher (natAdresse c.codeBase) bytes := by
    rw [hst]
    exact hcode
  have hW' : WorldRep L st.speicher σ := by
    rw [hst]
    exact hW
  exact pipeline_arbeit_korrekt c L certs src bytes prog hval hsep O passes R σ ρ
    st hcode' hrip0 hW' hE σ' ρ' hsrc hdec prof srcB B tt k hDeck hCost hb hk

/-- JOINT WITNESS for `arbeit_correct_loaded`: every premise holds
    jointly on the accepted program over the witness loaded image
    (validator, image and world checks, priced steps, two written
    slots with the source run 7 -> 35 and 9 -> 6); the theorem then
    gives the fetched loaded run plus the validated-bytes equation
    and the retired-work and named-time bounds. -/
theorem arbeit_correct_loaded_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      validate pwCfg (layoutVon piPs) pwCerts pwSrc pwBytes = true ∧
      LayoutSep (layoutVon piPs) ∧
      CodeAt (ladung piBild) (natAdresse pwCfg.codeBase) pwBytes ∧
      (piStart 30).rip = natAdresse pwCfg.codeBase ∧
      WorldRep (layoutVon piPs) (ladung piBild) pwSigma ∧
      EnvRepr pwEnv30 (piStart 30).register (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      decodeAll pwBytes.length pwBytes = some pwProg ∧
      Deckung pipeSummary 2 (decodiertZu pwProg) ∧
      laufKosten profilZeuge (decodiertZu pwProg) = some 18 ∧
      (∀ dd ∈ decodiertZu pwProg,
        ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3) ∧
      expandBound pipeSummary 2 = some 12 ∧
      (∃ k s2, laufBytes k (piStart 30) = .weiter s2 ∧
        s2.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
        WorldRep (layoutVon piPs) s2.speicher σ' ∧
        EnvRepr ρ' s2.register (abbOf pwCfg)) ∧
      pwBytes = encodeAll pwProg ∧
      targetWork pwProg ≤ 12 ∧ 18 ≤ 3 * 12 ∧
      PipePaket := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  have hst : (piStart 30).speicher = ladung piBild := rfl
  have hrip0 : (piStart 30).rip = natAdresse pwCfg.codeBase := rfl
  have hcode := imageOk_codeAt .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes
    pi_imageOk
  have hsep := imageOk_layoutSep .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes
    pi_imageOk
  have hW := imageOk_worldRep .p48 piBild pwCfg piPs piEs pwCerts pwSrc pwBytes
    pi_imageOk pwSigma pi_weltOk
  obtain ⟨⟨m, sW, hrun, hrip, hW2, hE2⟩, hbytes, hwork, htime⟩ :=
    arbeit_correct_loaded piBild pwCfg (layoutVon piPs) pwCerts pwSrc pwBytes pwProg
      pi_validate hsep pwO 0 pwR pwSigma pwEnv30 (piStart 30) hst hrip0 hcode hW
      pi_envRepr30 σ' ρ' hsrc pw_decode profilZeuge 2 3 18 12 deckung_pwProg
      kosten_pwProg hb_pwProg (pipeSummary_expand 2)
  exact ⟨σ', ρ', pi_validate, hsep, hcode, hrip0, hW, pi_envRepr30, hsrc,
    pw_decode, deckung_pwProg, kosten_pwProg, hb_pwProg, pipeSummary_expand 2,
    ⟨m, sW, hrun, hrip, hW2, hE2⟩, hbytes, hwork, htime, pipePaket_hold⟩

/-! ## 5. Float family: IEEE sequences over a loaded Fp state.

    Float correctness lives over `FpZustand`, never over pilot bytes:
    one source op is one machine op under the checked control word.
    The loaded leg is the state memory equation (`hst`): the run that
    the accepted `pipelineFloat_seq` delivers keeps the loaded
    mapping. A failed validator leg refuses step and run together
    (`float_loaded_verweigert`); the byte-fetch connection stays
    explicitly open (see CUTS). -/

/-- FLOAT SEQUENCE OVER LOADED MEMORY: the lowered two-step run
    computes the source model op bit for bit and keeps the loaded
    mapping, the control word and the integer registers. -/
theorem float_seq_geladen (op : GleitOp) (dst a b : XmmReg) (t : FpZustand)
    (hne : b ≠ dst)
    (hok : laengeOk 4 = true)
    (hfp : fpEintritt t.fp = true)
    (bild : Bild) (hst : t.kern.speicher = ladung bild) :
    ∃ t' : FpZustand,
      laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp op dst b, 4⟩] t = some t' ∧
      t'.kern.rip = ripNach (ripNach t.kern.rip 4) 4 ∧
      xmmTief t'.xmm dst =
        muster64 (gleitRechne op (bites64 (xmmTief t.xmm a)) (bites64 (xmmTief t.xmm b))) ∧
      t'.fp = t.fp ∧
      t'.kern.speicher = ladung bild ∧
      t'.kern.register = t.kern.register := by
  obtain ⟨t', hrun, hrip, hval, hfp', hmem0, hreg0⟩ :=
    pipelineFloat_seq op dst a b t hne hok hfp
  exact ⟨t', hrun, hrip, hval, hfp', by rw [hmem0]; exact hst, hreg0⟩

/-- FLOAT REFUSAL, LOADED: a failed validator leg refuses the step
    and the one-step run together -- refused, never executed. -/
theorem float_loaded_verweigert (d : FpDecodiert) (t : FpZustand)
    (h : floatPipeOk t.fp d.laenge = false) :
    fpSchritt d t = none ∧ laufFp [d] t = none := by
  have hr := pipelineFloat_refuses_validator d t h
  exact ⟨hr, by rw [laufFp_cons, hr]⟩

/-- JOINT WITNESS for the float family: the lowered divide sequence
    computes `1.0 / +0.0` on the witness state with the stored
    infinity observably changing memory, under the admitted profile;
    beside it the profile and length poison probes. -/
theorem float_seq_geladen_zeuge :
    ∃ t' t'' : FpZustand,
      laufFp [⟨.movsdRR XmmReg.xmm0 XmmReg.xmm0, 4⟩,
        ⟨senkGleitOp .div XmmReg.xmm0 XmmReg.xmm1, 4⟩] fpZeugeT = some t' ∧
      fpSchritt ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ t' = some t'' ∧
      read64 t''.kern.speicher (BitVec.ofNat 64 8192) =
        some 0x7FF0000000000000 ∧
      fpZeugeT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
        t''.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ∧
      floatPipeOk kontextReset 4 = true ∧
      fpSchritt ⟨.addsdRR XmmReg.xmm0 XmmReg.xmm1, 4⟩
        { fpZeugeT with fp := ⟨0x9F80⟩ } = none ∧
      fpSchritt ⟨.addsdRR XmmReg.xmm0 XmmReg.xmm1, 16⟩ fpZeugeT = none := by
  obtain ⟨t', t'', hrun, hstep, hliest, hwechselt⟩ := pipelineFloat_zeuge
  exact ⟨t', t'', hrun, hstep, hliest, hwechselt, floatPipeOk_reset,
    pipelineFloat_probe_profil, pipelineFloat_probe_laenge⟩

/-! ## 6. Relocation leg, generic over the fragments.

    Linking only concatenates, resolves, patches and re-checks: no
    relocation changes a byte outside its operand (`linkPatch_rahmen`,
    reused inside the accepted closing), and a patched rel32 jump
    operand re-decodes to the patched displacement through the
    accepted producer closing. The theorem below is that closing on
    the witness link, so every fragment run above also holds over
    patched bytes with the frame outside the operand untouched. -/

/-- RELOCATION RE-DECODE OVER LINKED BYTES: displacement, fit,
    coverage, coverage union, W^X, executed mapping, range and the
    outside-operand frame, through the accepted link closing. -/
theorem reloc_redecode_geladen :
    dispSigned zeugenDispField = 16 ∧
    rel32Passt 16 = true ∧
    decktAb ⟨.jump32 zeugenDispField, 5⟩ ∧
    bildDeckung (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht 0x1000) =
      (abschnittDeckung (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht
        0x1000) (linkAbschnittA zeugenEinheitA zeugenEinheitB) &&
        abschnittDeckung (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht
          0x1000) (linkAbschnittB zeugenEinheitA zeugenEinheitB)) ∧
    wxOk (linkAbschnittA zeugenEinheitA zeugenEinheitB) = true ∧
    ladenByte (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht 0x1000) 0
      0x1000 =
      dateiByte zeugenGepatcht
        ((linkAbschnittA zeugenEinheitA zeugenEinheitB).dateiOff +
          (0x1000 - (0 + (linkAbschnittA zeugenEinheitA zeugenEinheitB).vaddr))) ∧
    0 + 1 + (feldBytes (.rel32 16)).length ≤ zeugenVerknuepft.length ∧
    zeugenGepatcht[5]? = zeugenVerknuepft[5]? :=
  verknuepft_korrekt zeugenEinheitA zeugenEinheitB 0x1000 0 16 zeugenGepatcht
    zeugenDispField [natByte 195] (linkAbschnittA zeugenEinheitA zeugenEinheitB)
    0x1000 5 zeugen_patch zeugen_opcode zeugen_dek zeugen_bild_wohlgeformt
    zeugen_mem zeugen_find zeugen_innen zeugen_aussen

/-! ## 7. Poison probes: every refusal fires on concrete data. -/

/-- A spill frame over the code region is refused. -/
theorem gift_spill_code :
    spillPlanOk ⟨4096, 16⟩ [0] 4096 pwBytes.length spillD0 = false := by
  decide

/-- A call that uses the red zone is not admitted. -/
theorem gift_ruf_rot :
    rufOk rufWitBelegung rufWitRahmen 7 true = false := by
  decide

/-- A read of the unlisted table is refused. -/
theorem gift_tabelle_fremd : senkLesen zeA zeCfg zeReadFremd = none := by
  decide

/-- Under flush-to-zero the admitted divide refuses. -/
theorem gift_float_profil :
    fpSchritt ⟨.addsdRR XmmReg.xmm0 XmmReg.xmm1, 4⟩
      { fpZeugeT with fp := ⟨0x9F80⟩ } = none :=
  pipelineFloat_probe_profil

/-- A 16-byte float form refuses. -/
theorem gift_float_laenge :
    fpSchritt ⟨.addsdRR XmmReg.xmm0 XmmReg.xmm1, 16⟩ fpZeugeT = none :=
  pipelineFloat_probe_laenge

/-- An out-of-range displacement patches nothing. -/
theorem gift_link_range :
    linkPatch zeugenVerknuepft 1 (.rel32 2147483648) = none := by
  decide

/-- `2 * 3` has no deep lowering. -/
theorem gift_arbeit_mul :
    senkWertT (D := pwD) pwCfg
      (Expr.mul (Expr.lit (Γ := pwCtx) (Λ := []) 2)
        (Expr.lit (Γ := pwCtx) (Λ := []) 3)) = none := by
  decide

/- CUTS (exactly what is NOT proved here):

   Covered (lowered, with correctness over the loaded image):
   - spill: validated bytes plus a validated spill plan give the
     fetched loaded run plus slot-vs-table privacy, pairwise slot
     separation and slot-vs-extent separation
     (`spill_correct_loaded`, joint witness on the pipeline witness
     program with the transported frame separation);
   - calls: the joint validator (admitted frame, single-assignment
     shape, recomputed bytes) plus the loaded image give frame
     admission and the fetched callee run with callee-saved
     preservation (`ruf_correct_loaded`, joint witness on the
     single-assignment callee with its own built image);
   - tables: the lowered store over loaded memory with decided
     anchor checks gives the fetched run with the real `execStmt`
     outcome (`tabellen_correct_loaded`, joint witness on the
     two-field record with a minimal two-section image);
   - work: validated bytes over loaded memory give the fetched run
     plus the validated-bytes equation and the retired-work and
     named-time bounds (`arbeit_correct_loaded`, joint witness on
     the accepted program over the witness loaded image);
   - floats: the lowered sequence computes the source model op bit
     for bit and keeps the loaded mapping (`float_seq_geladen`,
     joint witness with a real memory change); a failed validator
     leg refuses step and run (`float_loaded_verweigert`);
   - relocations: the accepted link closing on the witness link
     (`reloc_redecode_geladen`); one planted probe per refusal path.
   Refused (`false`/`none`, never guessed), each with a poison
   probe: spill frame over code, red-zone call, unlisted-table
   read, refused MXCSR profile, bad float decode length,
   out-of-range displacement, multiplication without lowering.
   NOT covered, and not claimed:
   - no byte-fetch connection for floats: `laufFp` runs constructed
     `FpDecodiert` values through `fpSchritt`, never bytes through
     the decoder (inherited from lane 1161); the scalar-codec bridge
     stays with its owner;
   - no multi-statement callee bodies, no optimiser certificates in
     the call fragment (inherited from `einzelRuf_korrekt`);
   - no block-level integration of table reads (inherited from the
     tables lane);
   - no per-access target-to-W/GX simulation, no TSO/store-buffer
     claim, no second core, no time beyond named bounds (all
     inherited from the fragment lanes);
   - no silicon correspondence beyond the accepted producers; no
     new interpreter, no second cost model, no IR.
-/

#print axioms fragmentBytesGeladen
#print axioms spill_correct_loaded
#print axioms spill_correct_loaded_zeuge
#print axioms piSpillRahmen
#print axioms ruf_correct_loaded
#print axioms cwBild
#print axioms cw_validate_pi
#print axioms cw_imageOk
#print axioms cw_weltOk
#print axioms cw_rufExec_pi
#print axioms ruf_correct_loaded_zeuge
#print axioms tabellen_correct_loaded
#print axioms zeBildCode
#print axioms zeBildDaten
#print axioms zeBildDatei
#print axioms zeBild
#print axioms zeBild_codeAtB
#print axioms zeBild_codeAt
#print axioms zeBild_okB
#print axioms zeBild_weltB
#print axioms zeBild_rip
#print axioms tabellen_correct_loaded_zeuge
#print axioms arbeit_correct_loaded
#print axioms arbeit_correct_loaded_zeuge
#print axioms float_seq_geladen
#print axioms float_loaded_verweigert
#print axioms float_seq_geladen_zeuge
#print axioms reloc_redecode_geladen
#print axioms gift_spill_code
#print axioms gift_ruf_rot
#print axioms gift_tabelle_fremd
#print axioms gift_float_profil
#print axioms gift_float_laenge
#print axioms gift_link_range
#print axioms gift_arbeit_mul

end Gabbro.Grammatik.X86.PipelineLoadedAll
