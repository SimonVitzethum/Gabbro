/-
  File:      Grammatik/X86/HardwareExecution.lean
  Subject:   Coherent multicore architectural execution over the accepted
             byte-facing dispatcher and canonical TSO memory.

  Lane 660: ONE selected composition -- canonical per-core integer/FP
  data, ONE shared canonical memory, per-core TSO buffers and a checked
  core/control profile -- reusing `decodeExt`/`stepExt`/`extByteschritt`
  (ExtendedExecution575) and `issueByte`/`loadByte`/`flushKern`
  (TSO) with the `WortGruppe`/`FremdFrei` guard (WordAccessGrouping).
  No SC word effect is substituted for a buffered access; tearing and
  LOCK cases are explicitly refused (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat
import Grammatik.X86.FeatureProfile
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.LockedOps

namespace Gabbro.Grammatik.X86

/-- Per-core data WITHOUT memory: integer file, flags, RIP, XMM file
    and FP context. Memory lives once in the machine below, so all
    core-memory projections agree by construction. -/
structure HwKern where
  register : Register → Wort
  flags : Flags
  rip : Adresse
  xmm : XmmDatei
  fp : FPKontext

/-- The coherent machine: one shared canonical memory, per-core data,
    per-core TSO buffers, one silicon profile and per-core readiness. -/
structure HwMaschine where
  mem : Speicher
  kerne : Nat → HwKern
  puffer : Nat → List TSOEintrag
  hw : HwProfil
  bereit : Nat → BereitProfil

/-! ## 1. Projections: one shared memory seen by every core.

  The TSO view, the canonical core view and the extended FP view all
  read the SAME `mem`. Coherence is therefore proved, never assumed. -/

/-- The shared TSO view: machine memory plus machine buffers. -/
def tsoAnsicht (m : HwMaschine) : TSOZustand :=
  ⟨m.mem, m.puffer⟩

/-- The canonical core view of core `c`: its data over shared memory. -/
def projZustand (m : HwMaschine) (c : Nat) : Zustand :=
  ⟨(m.kerne c).register, (m.kerne c).flags, (m.kerne c).rip, m.mem⟩

/-- The extended FP view of core `c`: canonical core plus XMM/FP data. -/
def projFp (m : HwMaschine) (c : Nat) : FpZustand :=
  ⟨projZustand m c, (m.kerne c).xmm, (m.kerne c).fp⟩

/-- All core-memory projections agree: every core sees `m.mem`. -/
theorem projZustand_speicher (m : HwMaschine) (c : Nat) :
    (projZustand m c).speicher = m.mem := rfl

/-- The extended view agrees on memory as well. -/
theorem projFp_speicher (m : HwMaschine) (c : Nat) :
    (projFp m c).kern.speicher = m.mem := rfl

/-- Two cores project to the same memory. -/
theorem kerne_ein_speicher (m : HwMaschine) (c d : Nat) :
    (projZustand m c).speicher = (projZustand m d).speicher := rfl

/-- The TSO view carries the machine memory. -/
theorem tsoAnsicht_speicher (m : HwMaschine) :
    (tsoAnsicht m).mem = m.mem := rfl

/-- The TSO view carries the machine buffers. -/
theorem tsoAnsicht_puffer (m : HwMaschine) (c : Nat) :
    (tsoAnsicht m).puffer c = m.puffer c := rfl

/-! ## 2. Well-formedness: data state versus checked profile.

  `HwWf` never restates memory agreement (proved in §1); it checks the
  core/control profile: no core admits a feature its silicon lacks.
  Updates below keep profiles untouched, so well-formedness survives
  every memory/buffer/core step. -/

/-- Well-formedness: admitted features have silicon behind them. -/
def HwWf (m : HwMaschine) : Prop :=
  ∀ (c : Nat) (f : PerfMerkmal),
    merkmalZugelassen m.hw (m.bereit c) f = true → hat m.hw f = true

/-- Admission implies silicon: the accepted profile lemma, lifted. -/
theorem hwWf_aus_zugelassen (m : HwMaschine)
    (h : ∀ (c : Nat) (f : PerfMerkmal),
      merkmalZugelassen m.hw (m.bereit c) f = true) :
    HwWf m := by
  intro c f _
  exact (merkmalZugelassen_heisst_beide m.hw (m.bereit c) f (h c f)).1

/-- Core-data update: new data for core `c`, everything else kept. -/
def setKernDaten (m : HwMaschine) (c : Nat) (k : HwKern) : HwMaschine :=
  { m with kerne := fun d => if d = c then k else m.kerne d }

/-- Memory/buffer update from a TSO successor: profiles and core data
    are untouched. -/
def setTso (m : HwMaschine) (s : TSOZustand) : HwMaschine :=
  { m with mem := s.mem, puffer := s.puffer }

/-- Core updates preserve well-formedness (profiles untouched). -/
theorem setKernDaten_wf (m : HwMaschine) (c : Nat) (k : HwKern)
    (h : HwWf m) : HwWf (setKernDaten m c k) := h

/-- Memory/buffer updates preserve well-formedness. -/
theorem setTso_wf (m : HwMaschine) (s : TSOZustand)
    (h : HwWf m) : HwWf (setTso m s) := h

/-- The TSO view of a memory/buffer update is the successor state. -/
theorem setTso_ansicht (m : HwMaschine) (s : TSOZustand) :
    tsoAnsicht (setTso m s) = s := by
  cases s with
  | mk mem puffer => rfl

/-! ## 3. Machine steps: fetch, register execution, TSO memory events.

  Every case names its accepted equation. The register path re-embeds
  ONLY core data and keeps machine memory; it is gated by the
  memory-unchanged premise, so no SC word effect is ever substituted
  for a buffered access. Memory moves only through `issueByte`,
  `loadByte` and `flushKern` on the shared TSO view. -/

/-- Observable machine events: what one step did. -/
inductive HwEreignis where
  | regAusf : Nat → ExtInstr → HwEreignis
  | leseBeob : Nat → Adresse → Byte → HwEreignis
  | schreibAusgabe : Nat → Adresse → Byte → HwEreignis
  | spülung : Nat → TSOEintrag → HwEreignis
  | verweigert : Nat → HwEreignis
  deriving DecidableEq, Repr

/-- Re-embed a successor core view: core data moves, machine memory
    and buffers stay. This is the register path ONLY (see `HwSchritt.reg`
    for the memory-unchanged gate). -/
def setKernVonFp (m : HwMaschine) (c : Nat) (t' : FpZustand) : HwMaschine :=
  setKernDaten m c ⟨t'.kern.register, t'.kern.flags, t'.kern.rip,
    t'.xmm, t'.fp⟩

/-- After re-embedding, the core projects to the successor data over
    the shared memory. -/
theorem setKernVonFp_register (m : HwMaschine) (c : Nat) (t' : FpZustand) :
    ((setKernVonFp m c t').kerne c).register = t'.kern.register := by
  unfold setKernVonFp setKernDaten
  simp

/-- Re-embedding keeps the shared memory. -/
theorem setKernVonFp_speicher (m : HwMaschine) (c : Nat) (t' : FpZustand) :
    (setKernVonFp m c t').mem = m.mem := rfl

/-- Re-embedding keeps the buffers. -/
theorem setKernVonFp_puffer (m : HwMaschine) (c : Nat) (t' : FpZustand)
    (d : Nat) :
    (setKernVonFp m c t').puffer d = m.puffer d := rfl

/-- One coherent machine step, each case from its accepted equation:
    - `reg`: the unified evaluator on the core projection, admitted
      only where it leaves canonical memory alone;
    - `lade`: a `loadByte` observation (forwarding included), no state
      change;
    - `gibAus`: a `issueByte` store issue on the shared TSO view;
    - `spüle`: a `flushKern` drain into shared memory;
    - `fehler`: explicit refusal (fetch/decode/permission/profile). -/
inductive HwSchritt : HwMaschine → HwMaschine → HwEreignis → Prop where
  | reg {m : HwMaschine} (c : Nat) (i : ExtInstr) (t' : FpZustand)
      (hstep : stepExt i (projFp m c) (m.bereit c) = .weiter t')
      (hmem : t'.kern.speicher = m.mem) :
      HwSchritt m (setKernVonFp m c t') (.regAusf c i)
  | lade {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (h : loadByte (tsoAnsicht m) c a = some v) :
      HwSchritt m m (.leseBeob c a v)
  | gibAus {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (s' : TSOZustand)
      (h : issueByte (tsoAnsicht m) c a v = some s') :
      HwSchritt m (setTso m s') (.schreibAusgabe c a v)
  | spüle {m : HwMaschine} (c : Nat) (e : TSOEintrag)
      (s' : TSOZustand)
      (h : flushKern (tsoAnsicht m) c = some s')
      (hkopf : (m.puffer c).head? = some e) :
      HwSchritt m (setTso m s') (.spülung c e)
  | fehler {m : HwMaschine} (c : Nat)
      (h : fetchExt (projFp m c) (geholt (projZustand m c)) = none) :
      HwSchritt m m (.verweigert c)

/-! ## 4. Step preservation and accepted-equation correspondence.

  Permissions, profiles and the single shared memory survive every
  step; forwarding and drain effects are exactly the accepted TSO
  lemmas, lifted to the machine. -/

/-- Every machine step preserves well-formedness. -/
theorem hwSchritt_wf (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | reg c i t' hstep hmem => exact setKernDaten_wf _ c _ hwf
  | lade c a v h => exact hwf
  | gibAus c a v s' h => exact setTso_wf _ s' hwf
  | spüle c e s' h hkopf => exact setTso_wf _ s' hwf
  | fehler c h => exact hwf

/-- A store issue changes no canonical byte (buffer only). -/
theorem hwGibAus_kein_speicher (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) (h : HwSchritt m m' (.schreibAusgabe c a v))
    (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x := by
  cases h with
  | gibAus c a v s' h =>
    exact issue_kein_speicher (tsoAnsicht m) s' c a v h x

/-- Forwarding: after core `c` issues byte `v` at readable `a`, core
    `c` observes `v` -- exactly `load_nach_issue`, lifted. -/
theorem hwWeiterleitung (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte) (s' : TSOZustand)
    (h : issueByte (tsoAnsicht m) c a v = some s')
    (hrd : (tsoAnsicht m).mem.lesbar a = true) :
    loadByte s' c a = some v :=
  load_nach_issue (tsoAnsicht m) s' c a v h hrd

/-- A flush installs the buffer head into shared memory -- exactly
    `flush_schreibt_kopf`, lifted to the machine view. -/
theorem hwSpülung_schreibt (m : HwMaschine) (c : Nat) (s' : TSOZustand)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (he : m.puffer c = e :: rest)
    (h : flushKern (tsoAnsicht m) c = some s') :
    s'.mem.bytes e.addr = e.wert := by
  exact flush_schreibt_kopf (tsoAnsicht m) s' c h e rest he

/-! ## 5. Embeddings: pilot and extended execution are preserved.

  The old evaluator rides along unchanged (`laufAlt`); refusal and the
  divide trap (`halt`) survive the embedding with their exact
  admissibility conditions. No desired hardware refinement is copied:
  every arm cites its accepted selection lemma. -/

/-- The lift succeeds exactly where the old evaluator succeeds. -/
theorem hwLaufAlt_some (d : Decodiert) (t : FpZustand) (s' : Zustand)
    (h : schritt d t.kern = some s') :
    laufAlt d t = some { t with kern := s' } := by
  unfold laufAlt
  rw [h]

/-- The lift refuses exactly where the old evaluator refuses. -/
theorem hwLaufAlt_none (d : Decodiert) (t : FpZustand)
    (h : schritt d t.kern = none) :
    laufAlt d t = none := by
  unfold laufAlt
  rw [h]

/-- Pilot success is unified success, on the machine projection. -/
theorem hwPilot_weiter (m : HwMaschine) (c : Nat) (d : Decodiert)
    (b : BereitProfil) (s' : Zustand)
    (h : schritt d (projZustand m c) = some s') :
    stepExt (.pilot d) (projFp m c) b =
      .weiter { projFp m c with kern := s' } := by
  have hl : laufAlt d (projFp m c) = some { projFp m c with kern := s' } :=
    hwLaufAlt_some d (projFp m c) s' h
  exact stepExt_pilot d (projFp m c) _ b hl

/-- Pilot refusal is unified refusal, including stopped outcomes. -/
theorem hwPilot_verweigert (m : HwMaschine) (c : Nat) (d : Decodiert)
    (b : BereitProfil)
    (h : schritt d (projZustand m c) = none) :
    stepExt (.pilot d) (projFp m c) b = .verweigert := by
  have hl : laufAlt d (projFp m c) = none :=
    hwLaufAlt_none d (projFp m c) h
  exact stepExt_pilot_verweigert d (projFp m c) b hl

/-- The pilot arm never traps: no silent halt is introduced. -/
theorem hwPilot_kein_halt (d : Decodiert) (t : FpZustand)
    (b : BereitProfil) :
    stepExt (.pilot d) t b ≠ .halt := by
  cases hL : laufAlt d t with
  | some t' =>
    have hs := stepExt_pilot d t t' b hL
    rw [hs]
    intro h
    cases h
  | none =>
    have hs := stepExt_pilot_verweigert d t b hL
    rw [hs]
    intro h
    cases h

/-- The divide trap survives the embedding: accepted hardware halt in,
    unified halt out, on the machine projection. -/
theorem hwMuldiv_halt (m : HwMaschine) (c : Nat) (q : MulDivDecodiert)
    (b : BereitProfil)
    (h : mulDivSchritt q (projZustand m c) = .hardwareHalt) :
    stepExt (.muldiv q) (projFp m c) b = .halt :=
  stepExt_muldiv_halt q (projFp m c) b h

/-! ## 6. Word discipline: bytes issued, groups guarded, tearing refused.

  A word store is NEVER the SC `write64` effect: it is eight
  `issueByte` steps over `wortEintraege`. A grouped drain additionally
  needs `WortGruppe` (exact eight entries plus `FremdFrei`); a partial
  buffer, a foreign footprint entry, or alignment alone never groups.
  LOCK RMW has no machine step: it is explicitly refused until the
  locked662 producer lands (adapter in §9). -/

/-- Fold `issueByte` over an entry list: one refusal fails the whole
    word. Memory is untouched throughout (each issue keeps `mem`). -/
def issueListe (s : TSOZustand) (c : Nat) : List TSOEintrag →
    Option TSOZustand
  | [] => some s
  | e :: rest =>
    match issueByte s c e.addr e.wert with
    | none => none
    | some s1 => issueListe s1 c rest

/-- A successful word fold appends exactly the entries, oldest first. -/
theorem issueListe_haengt_an (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (h : issueListe s c l = some s') :
    s'.puffer c = s.puffer c ++ l := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    simp
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      have ihh := ih s1 s' h
      have hp : (s1.puffer c) = s.puffer c ++ [e] := by
        have := issue_haengt_an s s1 c e.addr e.wert h1
        simpa using this
      rw [ihh, hp, List.append_assoc]
      rfl

/-- A word fold leaves canonical memory unchanged. -/
theorem issueListe_kein_speicher (s s' : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (h : issueListe s c l = some s')
    (x : Adresse) :
    s'.mem.bytes x = s.mem.bytes x := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    rw [h]
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      rw [ih s1 s' h]
      exact issue_kein_speicher s s1 c e.addr e.wert h1 x

/-- Word store on the machine: eight buffered byte issues, never the
    SC word effect. `none` = at least one byte refused. -/
def hwWortAusgabe (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) : Option HwMaschine :=
  match issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none => none
  | some s' => some (setTso m s')

/-- A successful word store appends exactly the eight canonical
    entries to the acting core's buffer. -/
theorem hwWortAusgabe_puffer (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : hwWortAusgabe m c a v = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege a v := by
  unfold hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact issueListe_haengt_an (tsoAnsicht m) s' c _ h1

/-- A word store changes no canonical byte. -/
theorem hwWortAusgabe_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : hwWortAusgabe m c a v = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact issueListe_kein_speicher (tsoAnsicht m) s' c _ h1 x

/-- A partial buffer is no group: tearing is refused structurally. -/
theorem hwTeilwort_keine_gruppe (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort)
    (hne : s.puffer c ≠ wortEintraege a v) :
    ¬ WortGruppe s c a v := by
  intro hgrp
  obtain ⟨hbufl, _⟩ := hgrp
  exact hne hbufl

/-- A foreign footprint entry refuses the group. -/
theorem hwGruppe_verweigert_bei_fremdeintrag (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Wort) (d : Nat) (hne : d ≠ c)
    (e : TSOEintrag) (hmem : e ∈ s.puffer d)
    (hfuss : e.addr ∈ Fuss a) :
    ¬ WortGruppe s c a v := by
  intro hgrp
  obtain ⟨_, hff⟩ := hgrp
  exact (hff d hne e hmem) hfuss

/-- A grouped buffer admits no LOCK step on the acting core: the
    accepted `gruppe_verweigert_lock`, lifted to the machine view. -/
theorem hwGruppe_schliesst_lock_aus (m : HwMaschine) (c : Nat)
    (a : Adresse) (v delta : Wort)
    (hgrp : WortGruppe (tsoAnsicht m) c a v) :
    lockSchritt (.xadd64 a delta) c (tsoAnsicht m) = none :=
  gruppe_verweigert_lock (tsoAnsicht m) c a v delta hgrp

/-- LOCK requests are explicitly refused until the locked662 producer
    provides the checked RMW path (adapter in §9). -/
def hwLockAnfrage (_m : HwMaschine) (_c : Nat)
    (_b : SperrBefehl) : Option HwMaschine := none

/-- Every LOCK request refuses. -/
theorem hwLock_verweigert (m : HwMaschine) (c : Nat)
    (b : SperrBefehl) :
    hwLockAnfrage m c b = none := rfl

/-! ## 7. Computable fetched-byte register step.

  Fetch reads the core projection's ACTUAL executable bytes, decodes
  through the unified chain, and runs the unified evaluator. Stops
  (`halt`, `verweigert`) are carried, never hidden. The register path
  is justified exactly where the accepted step leaves memory alone
  (the `HwSchritt.reg` gate); memory-changing instructions must use
  the §3/§6 issue path instead. -/

/-- Machine-level register outcome: the successor machine, the
    hardware trap, or explicit refusal. -/
inductive HwRegAusgang where
  | weiter : HwMaschine → HwRegAusgang
  | halt : HwRegAusgang
  | verweigert : HwRegAusgang

/-- One fetched-byte register step on core `c`: fetch, unified
    decode, unified step, re-embed core data. Memory and buffers are
    kept by construction (see the justification below). -/
def hwByteschrittReg (m : HwMaschine) (c : Nat) : HwRegAusgang :=
  match fetchExt (projFp m c) (geholt (projZustand m c)) with
  | none => .verweigert
  | some (i, _) =>
    match stepExt i (projFp m c) (m.bereit c) with
    | .weiter t' => .weiter (setKernVonFp m c t')
    | .halt => .halt
    | .verweigert => .verweigert

/-- Selection: a fetched instruction justifies a machine `reg` step
    exactly where it leaves canonical memory alone. -/
theorem hwByteschrittReg_rechtfertigt (m : HwMaschine) (c : Nat)
    (i : ExtInstr) (rest : List Byte) (t' : FpZustand)
    (hf : fetchExt (projFp m c) (geholt (projZustand m c)) = some (i, rest))
    (hs : stepExt i (projFp m c) (m.bereit c) = .weiter t')
    (hmem : t'.kern.speicher = m.mem) :
    hwByteschrittReg m c = .weiter (setKernVonFp m c t') ∧
      HwSchritt m (setKernVonFp m c t') (.regAusf c i) := by
  simp only [hwByteschrittReg, hf, hs]
  exact ⟨trivial, .reg c i t' hs hmem⟩

/-- Fetch refusal is register-step refusal. -/
theorem hwByteschrittReg_verweigert (m : HwMaschine) (c : Nat)
    (hf : fetchExt (projFp m c) (geholt (projZustand m c)) = none) :
    hwByteschrittReg m c = .verweigert := by
  simp only [hwByteschrittReg, hf]

/-- Control-state refusal on the machine: without OS vector state the
    packed-integer arm refuses in every state -- the accepted
    `stepVector_profil_verweigert`, lifted. No silent trust. -/
theorem hwVec_ohne_os_verweigert (m : HwMaschine) (c : Nat)
    (v : VectorDec)
    (hos : (m.bereit c).osXmm = false)
    (hok : laengeOk v.laenge = true) :
    stepExt (.vec v) (projFp m c) (m.bereit c) = .verweigert := by
  apply stepExt_vec_verweigert
  apply stepVector_profil_verweigert v (projFp m c) (m.bereit c) hok
  unfold vecEintritt
  rw [hos]

/-! ## 8. Joint witness: two cores, fetched bytes, buffered store.

  Core 0 fetches two register-only instructions from ACTUAL
  executable memory (narrow `mov32rr`, then scalar `movsdRR`);
  afterwards core 0 issues a buffered byte store that core 1 first
  observes as absent (no foreign forwarding in TSO) and, after the
  drain, as present in shared memory. Core 1 starts on non-executable
  memory and refuses. Every claim below is a closed decidable
  observation (`decide`/`rfl`); no machine equality is ever decided. -/

/-- Witness image: narrow move (3 bytes) then scalar FP move (4). -/
def hwWitBild : List Byte :=
  encodeNarrow (.mov32rr .rax .rcx) ++ fpEncodeMovsdRR .xmm0 .xmm1

/-- Witness bytes: the image at 4096, zeroes elsewhere. -/
def hwWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match hwWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness code permission: exactly the 7 image bytes. -/
def hwWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 7)

/-- Witness data permission: eight bytes at 8192. -/
def hwWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8192 + 8)

/-- Witness shared memory: code is execute-only, data read/write. -/
def hwWitMem : Speicher :=
  { bytes := hwWitBytes, lesbar := hwWitDaten,
    schreibbar := hwWitDaten, ausfuehrbar := hwWitCode }

/-- Witness core-0 registers: values in rcx, zero in rax. -/
def hwWitReg0 : Register → Wort := fun q =>
  if q = Register.rcx then BitVec.ofNat 64 9
  else if q = Register.rax then BitVec.ofNat 64 5
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness core-0 XMM: the value as low double-word in xmm1. -/
def hwWitXmm0 : XmmDatei := fun q =>
  if q = .xmm1 then vecJoin (BitVec.ofNat 64 7) (BitVec.ofNat 64 0)
  else (BitVec.ofNat 128 0)

/-- Witness core data: core 0 runs at 4096, core 1 idles on the
    (non-executable) data page. -/
def hwWitKern : Nat → HwKern
  | 0 => ⟨hwWitReg0, zeugeFlags, BitVec.ofNat 64 4096, hwWitXmm0,
      kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def hwWitStart : HwMaschine :=
  ⟨hwWitMem, hwWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed: full silicon admits all. -/
theorem hwWitStart_wf : HwWf hwWitStart := by
  intro c f _
  cases f <;> rfl

/-- Read core RIP out of a register outcome. -/
def hwRipOut (o : HwRegAusgang) (c : Nat) : Option Wort :=
  match o with
  | .weiter m => some (m.kerne c).rip
  | _ => none

/-- Read a core register out of a register outcome. -/
def hwRegOut (o : HwRegAusgang) (c : Nat) (q : Register) :
    Option Wort :=
  match o with
  | .weiter m => some ((m.kerne c).register q)
  | _ => none

/-- Read an XMM low double-word out of a register outcome. -/
def hwXmmTiefOut (o : HwRegAusgang) (c : Nat) (q : XmmReg) :
    Option Wort :=
  match o with
  | .weiter m => some (xmmTief (m.kerne c).xmm q)
  | _ => none

/-- Read a shared-memory byte out of a register outcome. -/
def hwMemOut (o : HwRegAusgang) (a : Adresse) : Option Byte :=
  match o with
  | .weiter m => some (m.mem.bytes a)
  | _ => none

/-- Read a buffer length out of a register outcome. -/
def hwBufOut (o : HwRegAusgang) (c : Nat) : Option Nat :=
  match o with
  | .weiter m => some (m.puffer c).length
  | _ => none

/-- First fetched step on core 0. -/
def hwWitO1 : HwRegAusgang := hwByteschrittReg hwWitStart 0

/-- Second fetched step on core 0 (over the first successor). -/
def hwWitO2 : HwRegAusgang :=
  match hwWitO1 with
  | .weiter m1 => hwByteschrittReg m1 0
  | x => x

/-- Step one advances RIP past the 3-byte narrow move. -/
theorem hwWit_o1_rip :
    hwRipOut hwWitO1 0 = some (BitVec.ofNat 64 4099) := by
  decide

/-- Step one moves the 32-bit value into rax. -/
theorem hwWit_o1_rax :
    hwRegOut hwWitO1 0 .rax = some (BitVec.ofNat 64 9) := by
  decide

/-- Step one leaves shared memory alone. -/
theorem hwWit_o1_mem_still :
    hwMemOut hwWitO1 (BitVec.ofNat 64 8192) =
      some (BitVec.ofNat 8 0) := by
  decide

/-- Step one issues no buffer entry. -/
theorem hwWit_o1_puffer_leer : hwBufOut hwWitO1 0 = some 0 := by
  decide

/-- Step two advances RIP past the 4-byte scalar move. -/
theorem hwWit_o2_rip :
    hwRipOut hwWitO2 0 = some (BitVec.ofNat 64 4103) := by
  decide

/-- Step two lands the low double-word in xmm0. -/
theorem hwWit_o2_xmm :
    hwXmmTiefOut hwWitO2 0 .xmm0 = some (BitVec.ofNat 64 7) := by
  decide

/-- Step two leaves shared memory alone. -/
theorem hwWit_o2_mem_still :
    hwMemOut hwWitO2 (BitVec.ofNat 64 8192) =
      some (BitVec.ofNat 8 0) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable memory. -/
theorem hwWit_kern1_verweigert :
    hwByteschrittReg hwWitStart 1 = .verweigert := by
  rfl

/- CUTS:
   Skeleton only: data vocabulary and projections so far.
   NOT proved: well-formedness, steps, embeddings, witnesses, adapters.
-/

#print axioms HwMaschine

end Gabbro.Grammatik.X86
