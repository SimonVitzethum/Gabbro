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

/- CUTS:
   Skeleton only: data vocabulary and projections so far.
   NOT proved: well-formedness, steps, embeddings, witnesses, adapters.
-/

#print axioms HwMaschine

end Gabbro.Grammatik.X86
