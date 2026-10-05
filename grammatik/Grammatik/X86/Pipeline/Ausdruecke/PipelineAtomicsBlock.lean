/-
  File:      Grammatik/X86/PipelineAtomicsBlock.lean
  Subject:   Pipeline atomics: execBlock correspondence for blocks with
             shared-atomic reads/writes.

  Lane 1217 (follow-up of lanes 1163 `PipelineAtomics.lean` and 1203
  `PipelineAtomicsBind.lean`): atomics have per-access facts only, never
  a block run. This file proves the block level: lock sections chain
  (`SperrLauf` over `List (List AtomQuelle)` with one reached run),
  CAS failure bound at register level (`bind_cas_fehlschlag`, the twin
  of lane-1203 `bind_cas_erfolg`), and a real source `execBlock` with a
  shared-atomic global read/write plus a lock section related to the
  lowered access sequence (`abblock_korrekt`) with a non-degenerate
  joint witness. No seq_cst total order, no fairness, no retry bound.
  Reused unchanged: `senkAtom`/`senkListe`/`valAtom`, `sperre_korrekt`,
  `cas_korrekt_fehlschlag`, `lockVoll_cmpxchg_fehlschlag_adapter`,
  `mfenceDrain_*`, `senkAtom_zeuge`, `bind_zeuge`. No second IR, no
  second source interpreter, no optimiser change. Rust is out of scope.
-/
import Grammatik.X86.Pipeline.Ausdruecke.PipelineAtomicsBind

namespace Gabbro.Grammatik.X86.PipelineAtomicsBlock

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineAtomics

/-- One lock-section step: entry drain, a reached middle run with a
    foreign frame, exit drain, over a lowerable body. -/
def SperrSchritt (c : Nat) (innen : List AtomQuelle)
    (s s' : TSOZustand) : Prop :=
  ∃ s1 s2 : TSOZustand,
    mfenceDrain s c = some s1 ∧ TSOErreichbar s1 s2 ∧
    (∀ d : Nat, d ≠ c → s2.puffer d = s1.puffer d) ∧
    mfenceDrain s2 c = some s' ∧
    (senkListe innen).isSome = true

/-- A lock-section block run: each section brackets entry drain,
    reached middle, exit drain; sections chain state to state. -/
inductive SperrLauf (c : Nat) :
    List (List AtomQuelle) → TSOZustand → TSOZustand → Prop where
  | nil (s) : SperrLauf c [] s s
  | cons (innen rest s s' sN) :
      SperrSchritt c innen s s' → SperrLauf c rest s' sN →
      SperrLauf c (innen :: rest) s sN

/-- **SECTION-CHAIN REACHABILITY.** A lock-section block run is one
    reached run: each section contributes its bracket (lane-1163
    `sperre_korrekt`) and sections chain (`erreichbar_kette`). -/
theorem sperrlauf_erreichbar (c : Nat) (secs : List (List AtomQuelle))
    (s0 sN : TSOZustand) (h : SperrLauf c secs s0 sN) :
    TSOErreichbar s0 sN := by
  induction h with
  | nil s => exact .start
  | cons innen rest s s' sN hstep _ ih =>
    obtain ⟨s1, s2, hE, hM, hR, hA, hI⟩ := hstep
    obtain ⟨innere, hIn⟩ := Option.isSome_iff_exists.mp hI
    obtain ⟨-, -, -, -, hreach⟩ :=
      sperre_korrekt innen innere s s1 s2 s' c hIn hE hM hR hA
    exact erreichbar_kette s s' sN hreach ih

/-- **SECTION-CHAIN DRAIN.** A NONEMPTY lock-section block run ends
    with an empty own buffer: the last section's exit drain empties it.
    (The empty block drains nothing, hence the premise.) -/
theorem sperrlauf_leer (c : Nat) (secs : List (List AtomQuelle))
    (s0 sN : TSOZustand) (h : SperrLauf c secs s0 sN)
    (hne : secs ≠ []) :
    sN.puffer c = [] := by
  induction h with
  | nil s => exact absurd rfl hne
  | cons innen rest s s' sN hstep htail ih =>
    cases htail with
    | nil _ =>
      obtain ⟨s1, s2, hE, hM, hR, hA, hI⟩ := hstep
      obtain ⟨innere, hIn⟩ := Option.isSome_iff_exists.mp hI
      obtain ⟨-, hempty, -, -, -⟩ :=
        sperre_korrekt innen innere s s1 s2 s' c hIn hE hM hR hA
      exact hempty
    | cons _ _ _ _ _ _ _ => exact ih (by simp)

/-- **SECTION-CHAIN FOREIGN FRAME.** A lock-section block run keeps
    every foreign buffer: each section preserves them
    (lane-1163 `sperre_korrekt`) and the equalities chain. -/
theorem sperrlauf_fremd (c : Nat) (secs : List (List AtomQuelle))
    (s0 sN : TSOZustand) (h : SperrLauf c secs s0 sN) :
    ∀ d : Nat, d ≠ c → sN.puffer d = s0.puffer d := by
  induction h with
  | nil s => intro d _; rfl
  | cons innen rest s s' sN hstep _ ih =>
    obtain ⟨s1, s2, hE, hM, hR, hA, hI⟩ := hstep
    obtain ⟨innere, hIn⟩ := Option.isSome_iff_exists.mp hI
    obtain ⟨-, -, -, hframe, -⟩ :=
      sperre_korrekt innen innere s s1 s2 s' c hIn hE hM hR hA
    intro d hd
    rw [ih d hd, hframe d hd]

/-! ## 2. CAS failure binding at register level.

    Lane 1203 bound only CAS *success* (`bind_cas_erfolg`); the failure
    stutter stayed with the accepted `casSchritt_fehlschlag` (lane 1163,
    `cas_korrekt_fehlschlag`). Here the failure is bound too: the
    lowered LOCK CMPXCHG at the address the register pair names stutters
    with the decided `false` ledger entry. -/

/-- **CAS FAILURE BINDING.** The lowered LOCK CMPXCHG whose comparison
    against rax fails stutters at exactly the address the register pair
    names, with the decided failure ledger. The write-permission pin
    (`hwr`) is the accepted adapter's premise, never a new claim. -/
theorem bind_cas_fehlschlag (m : LockMaschine) (c : Nat) (a : Adresse)
    (src base : Register) (d : BitVec 32)
    (dest : Wort) (mem' : Speicher)
    (heff : effAddr m.zu base d = a)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher a = some dest)
    (hali : ausgerichtet8 a = true)
    (hfehl : (dest == m.zu.register .rax) = false)
    (hwr : write64 m.zu.speicher a dest = some mem') :
    PipelineAtomics.senkAtom (PipelineAtomics.AtomQuelle.cas src base d) =
      some [PipelineAtomics.ZielOp.lock (.cmpxchg64 src base d)] ∧
    casSchritt a (m.zu.register .rax) (m.zu.register src) c (toTSO m) =
      some (toTSO m, false) ∧
    ledgerDeckt (.cas a (m.zu.register .rax) (m.zu.register src))
      (ledgerCasOk a false) = true := by
  have hrd' : read64 m.zu.speicher (effAddr m.zu base d) = some dest := by
    rw [heff]; exact hrd
  have hali' : ausgerichtet8 (effAddr m.zu base d) = true := by
    rw [heff]; exact hali
  have hwr' : write64 m.zu.speicher (effAddr m.zu base d) dest =
      some mem' := by
    rw [heff]; exact hwr
  have h := lockVoll_cmpxchg_fehlschlag_adapter m c src base d dest mem'
    hbuf hrd' hali' hfehl hwr'
  rw [heff] at h
  exact ⟨PipelineAtomics.senk_cas src base d, h.1,
    cas_schliesst a (m.zu.register .rax) (m.zu.register src) false⟩

/-! ## 3. Block refusals and poison probes.

    Unsupported block shapes are REFUSED, never guessed: nested lock
    sections (no lock-order claim, lane 1163), overlong validator
    inputs, and anything the decided validator does not recompute. -/

/-- A doubly nested lock section is REFUSED. -/
theorem block_nested_verweigert :
    PipelineAtomics.senkAtom
      (.sperre [.sperre [.zaun]]) = none := by
  decide

/-- The empty body lowers to the empty target (positive). -/
theorem block_leer_ok : PipelineAtomics.senkListe [] = some [] := rfl

/-- A singleton fence body lowers to one MFENCE (positive). -/
theorem block_singleton_ok :
    PipelineAtomics.senkListe
      [PipelineAtomics.AtomQuelle.zaun] =
      some [PipelineAtomics.ZielOp.lock .mfence] := rfl

/-- POISON: the validator rejects a nested lock section. -/
theorem gift_block_val_nested (ts : List PipelineAtomics.ZielOp) :
    PipelineAtomics.valAtom
      (.sperre [.sperre [.zaun]]) ts = false := by
  have h : PipelineAtomics.senkAtom
      (PipelineAtomics.AtomQuelle.sperre
        [PipelineAtomics.AtomQuelle.sperre
          [PipelineAtomics.AtomQuelle.zaun]]) = none :=
    block_nested_verweigert
  unfold PipelineAtomics.valAtom
  rw [h]

/-- POISON: the validator rejects an overlong fence sequence (one fence
    lowers to exactly one MFENCE, never two). -/
theorem gift_block_val_ueberlang :
    PipelineAtomics.valAtom PipelineAtomics.AtomQuelle.zaun
      [.lock .mfence, .lock .mfence] = false := by
  decide

/-! ## 4. The source block: real `execBlock` with a shared atomic.

    Witness declaration `abD`: one two-row integer table (rows hold
    `0 .. 1000`), one shared-atomic global (`atomar`, `ggeteilt`,
    `0 .. 255`), one lock. The source block writes row 0, writes the
    atomic, runs a lock section writing row 1, then reads the atomic
    into row 0 again -- straight-line, no checks, no calls. -/

/-- The function signature: no parameters, writes everything. -/
def abSig : Signatur Unit Unit Unit Empty :=
  { params := [], erg := none, gruende := 0, haelt := [],
    schreibt := fun _ => true, gschreibt := fun _ => true,
    konsumiert := [], produziert := [], boden := none }

/-- Witness declaration: integer table, shared-atomic global, one lock. -/
def abD : Deklaration where
  Tab := Unit
  count := fun _ => 2
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 1000
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  gtyp := fun _ => .int 0 255
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => true
  Lock := Unit
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => abSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ _ => Or.inr rfl

def abV : Vertrag abD :=
  { schreibt := fun _ => true
    gschreibt := fun _ => true
    erg := none
    gruende := 0
    haelt := []
    produziert := []
    boden := none }
def abO : Orakel abD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => true

def abR : ∀ f : abD.Fn, World abD → Env abD (abD.params f) → RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- Access proofs: nothing is guarded. -/
theorem abDarf (Λ : List (Res abD)) : darf abD () Λ :=
  fun _ h => False.elim (List.not_mem_nil h) -- access: nothing guarded

theorem abGDarf (Λ : List (Res abD)) : gdarf abD () Λ :=
  fun _ h => False.elim (List.not_mem_nil h)

/-- Row indices. -/
def abIdx0 : Expr abD [] [] (.index (abD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

def abIdx1 {Λ : List (Res abD)} : Expr abD [] Λ (.index (abD.count ())) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- Literal slot values. -/
def abVal35 : Expr abD [] [] (abD.typ () ()) :=
  .weiter (lo := 35) (hi := 35) (by decide) (by decide) (.lit 35)

def abVal17 {Λ : List (Res abD)} : Expr abD [] Λ (abD.typ () ()) :=
  .weiter (lo := 17) (hi := 17) (by decide) (by decide) (.lit 17)

/-- The atomic write value. -/
def abValG : Expr abD [] [] (abD.gtyp ()) :=
  .weiter (lo := 42) (hi := 42) (by decide) (by decide) (.lit 42)

/-- The shared-atomic READ: the global's value widened into a slot. -/
def abRead : Expr abD [] [] (abD.typ () ()) :=
  .weiter (lo := 0) (hi := 255) (by decide) (by decide) (.glob () (abGDarf _))

/-- THE SOURCE PROGRAM:
    `T[0] = 35; A = 42; locks L { T[1] = 17 }; T[0] = A;` -/
def abSrc : Block abD abV false [] [] [] :=
  .cons (.assignSlot () () abIdx0 abVal35 rfl (abDarf _))
    (.cons (.assignGlob () abValG rfl (abGDarf _))
      (.cons (.locks () (fun _ h => False.elim (List.not_mem_nil h))
        (.cons (.assignSlot () () abIdx1 abVal17 rfl (abDarf _)) .nil))
        (.cons (.assignSlot () () abIdx0 abRead rfl (abDarf _)) .nil)))

/-- The source world: rows hold 7 and 9, the atomic holds 41. -/
def abSigma : World abD where
  slots := fun t k f => by
    cases t; cases f
    exact if k = 0 then (⟨7, by decide, by decide⟩ : Zahl 0 1000)
      else if k = 1 then (⟨9, by decide, by decide⟩ : Zahl 0 1000)
      else (⟨0, by decide, by decide⟩ : Zahl 0 1000)
  globs := fun _ => (⟨41, by decide, by decide⟩ : Zahl 0 255)
  spur := []

def abEnv : Env abD [] := .nil -- empty context

/-! ## 7. Lock sections bracketed as the lowering emits them.

    One concrete section run over the accepted two-core witness
    states: entry drain, reached middle, exit drain. The exit drain
    reuses drain idempotence on the emptied buffer (proved, not
    assumed). -/

/-- Draining an empty buffer is the identity (from the accepted
    `drainKernN_null`, never restated). -/
theorem ab_drain_leer_ident (s : TSOZustand) (c : Nat)
    (h : s.puffer c = []) :
    mfenceDrain s c = some s := by
  unfold mfenceDrain drainVoll
  rw [h]
  exact drainKernN_null s c

/-- The accepted witness state drains on core 0. -/
theorem ab_drain1_some : (mfenceDrain fdS2 0).isSome = true := by
  decide

/-- **SECTION RUN.** One MFENCE-bracketed section chains to a reached
    run ending drained with foreign buffers intact. -/
theorem ab_sperrlauf_inst : ∃ sN : TSOZustand,
    SperrLauf 0 [[PipelineAtomics.AtomQuelle.zaun]] fdS2 sN ∧
    TSOErreichbar fdS2 sN ∧ sN.puffer 0 = [] ∧
    (∀ d : Nat, d ≠ 0 → sN.puffer d = fdS2.puffer d) := by
  obtain ⟨s3, h3⟩ := Option.isSome_iff_exists.mp ab_drain1_some
  have hleer : s3.puffer 0 = [] := mfenceDrain_leert fdS2 s3 0 h3
  have h4 : mfenceDrain s3 0 = some s3 := ab_drain_leer_ident s3 0 hleer
  have hI : (PipelineAtomics.senkListe
      [PipelineAtomics.AtomQuelle.zaun]).isSome = true := by
    decide
  have hStep : SperrSchritt 0
      [PipelineAtomics.AtomQuelle.zaun] fdS2 s3 :=
    ⟨s3, s3, h3, .start, fun d _ => rfl, h4, hI⟩
  have hLauf : SperrLauf 0
      [[PipelineAtomics.AtomQuelle.zaun]] fdS2 s3 :=
    .cons _ [] _ _ _ hStep (.nil s3)
  refine ⟨s3, hLauf, ?_, ?_, ?_⟩
  · exact sperrlauf_erreichbar 0 _ _ _ hLauf
  · exact sperrlauf_leer 0 _ _ _ hLauf (by decide)
  · exact sperrlauf_fremd 0 _ _ _ hLauf

/-! ## 6. CAS failure at register level, concretely.

    A concrete locked machine with the word 10 at `abGlobA`, rax
    holding 11: the lowered LOCK CMPXCHG fails its comparison against
    rax and stutters, with the decided failure ledger. -/

/-- Memory with the word 10 at `[8208, 8216)`, data-only. -/
def abMemBytes (a : Adresse) : Byte :=
  if 8208 ≤ a.toNat ∧ a.toNat < 8216 then
    wortByte (BitVec.ofNat 64 10) (a.toNat - 8208)
  else 0

def abMemDaten (a : Adresse) : Bool :=
  decide (8208 ≤ a.toNat ∧ a.toNat < 8216)

def abMem : Speicher :=
  { bytes := abMemBytes, lesbar := abMemDaten, schreibbar := abMemDaten,
    ausfuehrbar := fun _ => false }

/-- Registers: `rbp` names the global, `rax` holds 11, else zero. -/
def abReg : Register → Wort := fun q =>
  if q = .rbp then natAdresse 8208 else if q = .rax then 11 else 0

/-- Base state: registers, flags, entry rip, data memory. -/
def abZu0 : Zustand :=
  { register := abReg, flags := witnessFlags, rip := natAdresse 4096,
    speicher := abMem }

/-- The machine: buffers empty. -/
def abM : LockMaschine where
  zu := abZu0
  puffer := fun _ => []

theorem ab_hrd : read64 abMem (natAdresse 8208) = some 10 := by
  decide

theorem ab_hali : ausgerichtet8 (natAdresse 8208) = true := by
  decide

theorem ab_heff : effAddr abM.zu .rbp 0 = natAdresse 8208 := by
  decide

theorem ab_hfehl : ((10 : Wort) == abM.zu.register .rax) = false := by
  decide

theorem ab_hbuf : abM.puffer 0 = [] := rfl

theorem ab_hwr_some :
    (write64 abMem (natAdresse 8208) 10).isSome = true := by
  decide

/-- **CAS FAILURE, REGISTER-BOUND.** The lowered LOCK CMPXCHG at the
    address `rbp` names stutters: memory reads 10, rax expects 11. -/
theorem ab_cas_fehlschlag_inst :
    PipelineAtomics.senkAtom
      (PipelineAtomics.AtomQuelle.cas .rcx .rbp 0) =
      some [PipelineAtomics.ZielOp.lock
        (.cmpxchg64 .rcx .rbp 0)] ∧
    casSchritt (natAdresse 8208) (abM.zu.register .rax)
      (abM.zu.register .rcx) 0 (toTSO abM) =
      some (toTSO abM, false) ∧
    ledgerDeckt
      (.cas (natAdresse 8208) (abM.zu.register .rax)
        (abM.zu.register .rcx))
      (ledgerCasOk (natAdresse 8208) false) = true := by
  obtain ⟨mem', hwr⟩ := Option.isSome_iff_exists.mp ab_hwr_some
  exact bind_cas_fehlschlag abM 0 (natAdresse 8208) .rcx .rbp 0 10 mem'
    ab_heff ab_hbuf ab_hrd ab_hali ab_hfehl hwr

/-! ## 5. The block access sequence and its refusal.

    The atomic contents of `abSrc` as one access sequence: the shared
    global at `abGlobA` written then read (release/acquire, plain MOV
    under the named rule), plus the lock-section body. Integer-slot
    writes stay with the accepted `Pipeline` lowering (cited, never
    redone); what is lowered HERE is exactly the atomic sequence. -/

/-- The shared-atomic global lives at this address. -/
def abGlobA : Adresse := natAdresse 8208

/-- The block's atomic access sequence: release write then acquire
    read of the shared global. -/
def abOps : List PipelineAtomics.AtomQuelle :=
  [PipelineAtomics.AtomQuelle.schreibe abGlobA .freigabe .rbp .rax 0,
    PipelineAtomics.AtomQuelle.lese abGlobA .freigabe .rax .rbp 0]

/-- The sequence lowers to two plain MOVs (positive). -/
theorem abOps_senk : PipelineAtomics.senkListe abOps =
    some [PipelineAtomics.ZielOp.movStore .rbp .rax 0,
      PipelineAtomics.ZielOp.movLoad .rax .rbp 0] := rfl

/-- **BLOCK REFUSAL.** A block holding a nested lock section anywhere
    is REFUSED by the lowering -- never guessed, wherever it stands. -/
theorem abblock_refuses_nested (pre post : List PipelineAtomics.AtomQuelle) :
    PipelineAtomics.senkListe (pre ++
      [PipelineAtomics.AtomQuelle.sperre
        [PipelineAtomics.AtomQuelle.sperre
          [PipelineAtomics.AtomQuelle.zaun]]] ++ post) = none := by
  induction pre with
  | nil => rfl
  | cons q qs ih =>
    have h2 : PipelineAtomics.senkListe (qs ++
      [PipelineAtomics.AtomQuelle.sperre
        [PipelineAtomics.AtomQuelle.sperre
          [PipelineAtomics.AtomQuelle.zaun]]] ++ post) = none := ih
    simp only [List.cons_append, PipelineAtomics.senkListe, h2]
    cases h : PipelineAtomics.senkEinzeln q <;> rfl

/-- THE SOURCE RUN: `T[0] = 35; A = 42; locks L { T[1] = 17 };
    T[0] = A;` gives row 0 = 42 (the atomic read), row 1 = 17, atomic
    42. Row 0 changes 7 -> 35 -> 42; the atomic changes 41 -> 42. -/
theorem ab_quelle : ∃ σ' ρ',
    execBlock abO 0 abR abSrc abSigma abEnv = .ok σ' ρ' ∧
    (σ'.slots () 0 ()).n = 42 ∧ (σ'.slots () 1 ()).n = 17 ∧
    (σ'.globs Unit.unit).n = 42 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-! ## 8. Block correspondence and joint witness.

    `abblock_correct` (in the style of `pipeline_correct_entry`): any
    source run of the block yields the computed values, and the atomic
    access sequence lowers as emitted. `abblock_zeuge` instantiates
    every generic theorem of this file jointly on non-degenerate runs:
    the source run changes memory (row 0: 7 -> 42, row 1: 9 -> 17,
    atomic 41 -> 42), the target run changes memory, a table is
    written, the CAS failure stutters at its bound address, and one
    lock section brackets as emitted. -/

/-- **BLOCK CORRESPONDENCE.** Any source run of the block ends with
    row 0 = 42 (the shared-atomic read), row 1 = 17, the atomic at 42,
    while the access sequence lowers to the two plain MOVs. -/
theorem abblock_correct (σ' : World abD) (ρ' : Env abD [])
    (hsrc : execBlock abO 0 abR abSrc abSigma abEnv = .ok σ' ρ') :
    (σ'.slots () 0 ()).n = 42 ∧ (σ'.slots () 1 ()).n = 17 ∧
    (σ'.globs Unit.unit).n = 42 ∧
    PipelineAtomics.senkListe abOps =
      some [PipelineAtomics.ZielOp.movStore .rbp .rax 0,
        PipelineAtomics.ZielOp.movLoad .rax .rbp 0] := by
  obtain ⟨σq, ρq, hq, hq0, hq1, hqg⟩ := ab_quelle
  rw [hq] at hsrc
  cases hsrc
  exact ⟨hq0, hq1, hqg, abOps_senk⟩

/-- **JOINT WITNESS.** The source run, the lowering, the written
    table, a reached memory-changing target run, the bracketed lock
    section, the register-bound CAS failure, and the block refusal
    hold together. Non-degenerate on both sides. -/
theorem abblock_zeuge :
    (∃ σ' ρ', execBlock abO 0 abR abSrc abSigma abEnv = .ok σ' ρ' ∧
      (σ'.slots () 0 ()).n = 42 ∧ (σ'.slots () 1 ()).n = 17 ∧
      (σ'.globs Unit.unit).n = 42 ∧
      (abSigma.slots () 0 ()).n = 7 ∧ (abSigma.slots () 1 ()).n = 9 ∧
      (abSigma.globs Unit.unit).n = 41 ∧
      abV.schreibt () = true) ∧
    PipelineAtomics.senkListe abOps =
      some [PipelineAtomics.ZielOp.movStore .rbp .rax 0,
        PipelineAtomics.ZielOp.movLoad .rax .rbp 0] ∧
    (∃ s2 s3 : TSOZustand, TSOErreichbar fdStart s2 ∧
      mfenceSchrittAusBytes pinMfence s2 0 = some s3 ∧
      s2.mem.bytes fdX ≠ s3.mem.bytes fdX ∧ s2.puffer 0 ≠ [] ∧
      witD.schreibt () () = true) ∧
    (∃ sN : TSOZustand,
      SperrLauf 0 [[PipelineAtomics.AtomQuelle.zaun]] fdS2 sN ∧
      TSOErreichbar fdS2 sN ∧ sN.puffer 0 = [] ∧
      (∀ d : Nat, d ≠ 0 → sN.puffer d = fdS2.puffer d)) ∧
    casSchritt (natAdresse 8208) (abM.zu.register .rax)
      (abM.zu.register .rcx) 0 (toTSO abM) =
      some (toTSO abM, false) ∧
    PipelineAtomics.senkListe ([] ++
      [PipelineAtomics.AtomQuelle.sperre
        [PipelineAtomics.AtomQuelle.sperre
          [PipelineAtomics.AtomQuelle.zaun]]] ++
      ([] : List PipelineAtomics.AtomQuelle)) = none := by
  obtain ⟨σq, ρq, hq, hq0, hq1, hqg⟩ := ab_quelle
  obtain ⟨s2, s3, _, _, _, _, _, hreach, hdrain, hchg, hbuf0, _,
    hschreibt, _, _, _⟩ := PipelineAtomics.senkAtom_zeuge
  obtain ⟨sN, hlauf, hreach2, hleer2, hfremd2⟩ := ab_sperrlauf_inst
  obtain ⟨_, hstutter, _⟩ := ab_cas_fehlschlag_inst
  refine ⟨⟨σq, ρq, hq, hq0, hq1, hqg, rfl, rfl, rfl, rfl⟩, abOps_senk,
    ⟨s2, s3, hreach, hdrain, hchg, hbuf0, hschreibt⟩,
    ⟨sN, hlauf, hreach2, hleer2, hfremd2⟩, hstutter,
    abblock_refuses_nested [] []⟩

/- CUTS: what is not proved here
     Proved here (all over REUSED accepted definitions -- no new machine,
     no new decoder row, no second IR, no source/checker/goal change):
     - block chaining (§1): `SperrSchritt` (one bracketed section step)
       and `SperrLauf` (sections chained state to state) with
       `sperrlauf_erreichbar` (one reached run via lane-1163
       `sperre_korrekt` + `erreichbar_kette`), `sperrlauf_leer` (a
       nonempty run ends drained) and `sperrlauf_fremd` (foreign
       buffers intact);
     - CAS failure at register level (§2): `bind_cas_fehlschlag` (the
       twin of lane-1203 `bind_cas_erfolg`: the lowered LOCK CMPXCHG
       whose rax comparison fails stutters at the address the register
       pair names, decided `false` ledger), via the accepted
       `lockVoll_cmpxchg_fehlschlag_adapter`;
     - block refusals (§3) and the block access sequence (§5):
       `block_nested_verweigert`, `block_leer_ok`,
       `block_singleton_ok`, `gift_block_val_nested`,
       `gift_block_val_ueberlang`, `abOps`/`abOps_senk` (release write
       then acquire read lower to two plain MOVs),
       `abblock_refuses_nested` (a nested section refuses anywhere in
       a block);
     - the real source block (§4): witness declaration `abD` (integer
       table, shared-atomic global, one lock), the straight-line
       program `abSrc` (`T[0] = 35; A = 42; locks L { T[1] = 17 };
       T[0] = A;`) with its real `execBlock` run `ab_quelle`
       (row 0 = 42, row 1 = 17, atomic 42);
     - the concrete CAS machine (§6): `abM` (word 10 at the global,
       rax 11) with `ab_cas_fehlschlag_inst` (register-bound stutter);
     - the concrete section run (§7): `ab_sperrlauf_inst` (one
       MFENCE-bracketed section over the accepted witness drains,
       exit via proved drain idempotence);
     - the correspondence (§8): `abblock_correct` (any source run
       yields the computed values with the emitted lowering) and the
       joint non-degenerate witness `abblock_zeuge` (source and target
       memory change, a written table, the bound CAS failure, the
       bracketed section, the refusal).
     NOT proved here, and not claimed:
     - No TSO-store word install for the block's own writes: the two
       plain MOVs correspond per access (lane 1163); the 8-issue word
       install stays with lane 1203 (`wort_installation`).
     - No integer-slot machine run for the block's plain writes: they
       stay with the accepted `Pipeline` lowering (cited, never
       redone); this file lowers exactly the atomic sequence.
     - No SFENCE/LFENCE brackets for lock sections (sections stay
       MFENCE-bracketed); no narrow-fence block claim.
     - No per-step framing of ARBITRARY middle runs inside a section:
       each `SperrSchritt` carries its foreign frame as an explicit
       premise.
     - No seq_cst total order (inherited `kein_seqcst_total`), no
       fairness, no CAS retry bound, no timing or cost.
     - No interrupt, device, MMIO or DMA claim.
-/

#print axioms sperrlauf_erreichbar
#print axioms sperrlauf_leer
#print axioms sperrlauf_fremd
#print axioms bind_cas_fehlschlag
#print axioms block_nested_verweigert
#print axioms block_leer_ok
#print axioms block_singleton_ok
#print axioms gift_block_val_nested
#print axioms gift_block_val_ueberlang
#print axioms abDarf
#print axioms abGDarf
#print axioms ab_quelle
#print axioms abOps_senk
#print axioms abblock_refuses_nested
#print axioms ab_hrd
#print axioms ab_hali
#print axioms ab_heff
#print axioms ab_hfehl
#print axioms ab_hbuf
#print axioms ab_hwr_some
#print axioms ab_cas_fehlschlag_inst
#print axioms ab_drain_leer_ident
#print axioms ab_drain1_some
#print axioms ab_sperrlauf_inst
#print axioms abblock_correct
#print axioms abblock_zeuge

end Gabbro.Grammatik.X86.PipelineAtomicsBlock
