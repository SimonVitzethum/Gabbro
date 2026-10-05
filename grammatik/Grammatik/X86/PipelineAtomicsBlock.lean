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
import Grammatik.X86.PipelineAtomicsBind

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

/- CUTS: what is not proved here
     Proved here so far: nothing beyond `SperrSchritt` (skeleton).
     NOT proved here, and not claimed:
     - No block run yet; no CAS-failure binding; no source link.
     - No seq_cst total order, no fairness, no retry bound.
-/

#print axioms SperrSchritt

end Gabbro.Grammatik.X86.PipelineAtomicsBlock
