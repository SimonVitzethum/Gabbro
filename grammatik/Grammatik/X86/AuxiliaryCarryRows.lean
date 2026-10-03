/-
  File:      Grammatik/X86/AuxiliaryCarryRows.lean
  Subject:   Auxiliary-carry rows for the admitted 720 integer execution.

  Lane 1100: for every integer row the accepted 720 consumer connects to
  shared TSO execution (the exact `ConcIntOp` set: load/store at
  b8/b16/b32/b64 through `concLoadMaschine`/`concStoreMaschine`), either
  the DEFINED hardware AF value over the canonical helpers or a proved
  non-observability lemma consumed by every flag consumer. All eight
  rows take the second leg: MOV affects no flags (Intel SDM Vol. 2A MOV
  entry: "Flags Affected: None"), so flags -- and the `af` Option Bool
  abstraction in particular -- are preserved, never invented; the
  `bedingung_af_frei` identity (lane 692 family, imported not forked)
  shows no flag consumer can observe AF behind these rows. The `af`
  abstraction is never cited as a defined hardware AF result.

  Provenance: Intel SDM 325462-093US MOV entry ("Flags Affected:
  None"); headings are provenance, never silicon proofs.
-/
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.ArchitecturalFlags
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- One admitted 720 row on the coherent machine: loads merge through
    the accepted partial-register discipline, stores issue into the
    acting core's buffer. `none` is an explicit refusal. -/
def auxRowStep (op : ConcIntOp) (m : HwMaschine) (c len : Nat) :
    Option HwMaschine :=
  match op with
  | .load b dst base disp => concLoadMaschine m c b dst base disp len
  | .store b base src disp => concStoreMaschine m c b base src disp len

/-- Defined-AF claims over admitted 720 rows. Empty on purpose: no
    admitted row defines AF (MOV affects no flags), so any defined
    value for a future row must arrive as a new constructor carrying
    its canonical-helper equation -- never a fiat value, never a
    weakened consumer. -/
inductive AuxDefined : ConcIntOp → Bool → Prop

/-- Routing: a load row IS the accepted 720 load adapter. -/
theorem auxRowStep_load (b : Breite) (dst base : Register)
    (disp : BitVec 32) (m : HwMaschine) (c len : Nat) :
    auxRowStep (.load b dst base disp) m c len =
      concLoadMaschine m c b dst base disp len := rfl

/-- Routing: a store row IS the accepted 720 store adapter. -/
theorem auxRowStep_store (b : Breite) (base src : Register)
    (disp : BitVec 32) (m : HwMaschine) (c len : Nat) :
    auxRowStep (.store b base src disp) m c len =
      concStoreMaschine m c b base src disp len := rfl

/-- Every admitted row keeps the flags (MOV discipline, reused from
    the accepted 720 adapters, never a forked flag semantics): in
    particular the `af` Option Bool abstraction is preserved, never
    invented and never cited as a defined hardware AF result. -/
theorem auxFlags_erhalten (op : ConcIntOp) (m m' : HwMaschine)
    (c len : Nat) (h : auxRowStep op m c len = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  cases op with
  | load b dst base disp =>
    rw [auxRowStep_load] at h
    exact concLoadMaschine_flags m m' c b dst base disp len h
  | store b base src disp =>
    rw [auxRowStep_store] at h
    exact concStoreMaschine_flags m m' c b base src disp len h

/-- AF non-observability behind every admitted row, consumed by every
    flag consumer: the row keeps the flags (above), and the imported
    `bedingung_af_frei` identity (692 family, never a forked consumer
    rule) shows no condition can observe AF behind it. Every premise
    is used: `h` fixes the preserved flags, `cnd`/`a`/`b` the consumer
    and the two AF choices. -/
theorem auxAf_verbrauch (op : ConcIntOp) (m m' : HwMaschine)
    (c len : Nat) (h : auxRowStep op m c len = some m')
    (cnd : Bedingung) (a b : Option Bool) :
    bedingung cnd {(m'.kerne c).flags with af := a} =
      bedingung cnd {(m.kerne c).flags with af := b} := by
  have hf := auxFlags_erhalten op m m' c len h
  rw [hf]
  exact bedingung_af_frei cnd _ a b

/-- PLANTED PROBE (unadmitted-row AF refusal): no admitted 720 row
    carries a defined AF value -- any AF claim over any of these rows
    is refused structurally. -/
theorem auxKeinDefiniert (op : ConcIntOp) (v : Bool) :
    ¬ AuxDefined op v := by
  intro h
  cases h

/-- PLANTED PROBE (concrete unadmitted row): the 8-bit load -- which
    has no accepted byte producer at all (`concDecode_nur_b64_b32`)
    -- carries no defined AF value either. -/
theorem auxProbe_afUndefiniert_b8load :
    ¬ ∃ v : Bool,
      AuxDefined (.load .b8 .rax .rbx (BitVec.ofNat 32 0)) v := by
  intro h
  obtain ⟨v, hv⟩ := h
  exact auxKeinDefiniert _ v hv

/-- TARGET 1: per-row defined-or-unobservable disjunction over the
    exact admitted 720 row set (`ConcIntOp`: load/store at
    b8/b16/b32/b64). Every row takes the second leg -- flags preserved
    with AF unobservable to every consumer -- since no admitted row
    defines AF; the first leg stands ready for future rows carrying
    their canonical-helper equation. -/
theorem auxCarry_definiert_alle (op : ConcIntOp) (m m' : HwMaschine)
    (c len : Nat) (h : auxRowStep op m c len = some m') :
    (∃ v : Bool, AuxDefined op v) ∨
      ((m'.kerne c).flags = (m.kerne c).flags ∧
       ∀ (cnd : Bedingung) (a b : Option Bool),
         bedingung cnd {(m'.kerne c).flags with af := a} =
           bedingung cnd {(m.kerne c).flags with af := b}) := by
  exact Or.inr ⟨auxFlags_erhalten op m m' c len h,
    fun cnd a b => auxAf_verbrauch op m m' c len h cnd a b⟩

/-- TARGET 2: fetched execution agreement. The representative row is
    the accepted 720 witness store: its bytes are fetched from actual
    executable memory (`concWit_fetch_decode`), the shared dispatcher
    runs it on `HwMaschine` through the accepted 720 connection
    (`concStoreMaschine`, reused not rebuilt), flags are preserved,
    and the TSO projection is reached. -/
theorem auxCarry_byteschritt :
    ∃ m1 : HwMaschine,
      concDecode (geholt (projZustand concWitM0 0)) =
        some ((.store .b32 .rbx .rax (BitVec.ofNat 32 0)), 7) ∧
      auxRowStep (.store .b32 .rbx .rax (BitVec.ofNat 32 0))
        concWitM0 0 7 = some m1 ∧
      (m1.kerne 0).flags = (concWitM0.kerne 0).flags ∧
      TSOErreichbar (tsoAnsicht concWitM0) (tsoAnsicht m1) := by
  have hdec := concWit_fetch_decode
  cases he : concStoreMaschine concWitM0 0 .b32 .rbx .rax
      (BitVec.ofNat 32 0) 7 with
  | none =>
    have hc := concWit_store_rip
    simp [he] at hc
  | some m1 =>
    refine ⟨m1, hdec, ?_, ?_, ?_⟩
    · rw [auxRowStep_store]
      exact he
    · exact concStoreMaschine_flags concWitM0 m1 0 .b32 .rbx .rax
        (BitVec.ofNat 32 0) 7 he
    · exact concStoreMaschine_erreichbar concWitM0 m1 0 .b32 .rbx .rax
        (BitVec.ofNat 32 0) 7 he

/-- PLANTED PROBE (flag-consumer bypass refusal): reading AF
    directly -- bypassing `bedingung` -- cannot move any consumer on
    the witness flags: both AF choices agree, so a bypass claim is
    refused by the imported identity, not by weakening the consumer. -/
theorem auxProbe_keinAfbypass :
    bedingung .e {(concWitM0.kerne 0).flags with af := some true} =
      bedingung .e {(concWitM0.kerne 0).flags with af := none} :=
  bedingung_af_frei .e _ _ _

/-- JOINT WITNESS for both targets on one non-degenerate program: the
    accepted 720 witness run (fetched narrow `store32` bytes, issued
    width-selected through the shared dispatcher with flags
    preserved, TSO-reached) drains observably into shared memory (the
    cell moves 0 to `0x04`, observed from both cores) beside both
    planted refusals. Non-degeneracy at this layer: a reached run with
    a memory-changing step (the drain changes actual shared memory);
    the hardware analogue of "a table some function writes" is the
    written footprint cell `concWitA`, written by the store row and
    read back by both cores -- no Gabbro source table exists at this
    layer, and none is claimed. -/
theorem auxCarry_zeuge :
    (∃ m1 : HwMaschine,
      auxRowStep (.store .b32 .rbx .rax (BitVec.ofNat 32 0))
        concWitM0 0 7 = some m1 ∧
      (m1.kerne 0).flags = (concWitM0.kerne 0).flags ∧
      TSOErreichbar (tsoAnsicht concWitM0) (tsoAnsicht m1)) ∧
    concWitMem.bytes concWitA = BitVec.ofNat 8 0 ∧
    concWitNachFlush = some (some (BitVec.ofNat 8 4)) ∧
    concWitFremdNachFlush = some (some concWitV) ∧
    (∀ op v, ¬ AuxDefined op v) ∧
    (bedingung .e {(concWitM0.kerne 0).flags with af := some true} =
      bedingung .e {(concWitM0.kerne 0).flags with af := none}) := by
  obtain ⟨m1, _, hstep, hflags, hreach⟩ := auxCarry_byteschritt
  exact ⟨⟨m1, hstep, hflags, hreach⟩, concWit_anfang_null,
    concWit_spuelung, concWit_fremd_neu, auxKeinDefiniert,
    auxProbe_keinAfbypass⟩

/- CUTS:
    Proved here, layering over (never editing) the accepted 720/692/660
    modules, reusing their equations and identities (never a forked flag
    semantics, never a rebuilt connection):
    - `auxRowStep`: one dispatcher over the exact admitted 720 row set
      (`ConcIntOp`: load/store at b8/b16/b32/b64) onto the accepted 720
      machine adapters, with definitional routing equations.
    - `auxFlags_erhalten`: every admitted row keeps the flags (MOV
      discipline): the `af` Option Bool abstraction is preserved, never
      invented, never cited as a defined hardware AF result.
    - `auxAf_verbrauch`: AF non-observability consumed by every flag
      consumer, via the imported `bedingung_af_frei` identity.
    - TARGET `auxCarry_definiert_alle`: per-row defined-or-unobservable
      disjunction; all eight rows take the unobservable leg.
    - TARGET `auxCarry_byteschritt`: fetched execution agreement for the
      representative witness store on `HwMaschine` through the accepted
      720 connection, with flags preserved and the TSO projection
      reached.
    - Joint `auxCarry_zeuge` on the non-degenerate witness run (drain
      changes shared memory 0 to `0x04`, both cores observe) with both
      planted probes (`auxKeinDefiniert` over every row,
      `auxProbe_afUndefiniert_b8load` concrete,
      `auxProbe_keinAfbypass` against a direct-AF consumer bypass).
    NOT proved here, and not claimed:
    - No row is left without a verdict, but no row carries a DEFINED
      hardware AF value: all eight admitted rows (load/store at
      b8/b16/b32/b64) stay on the unobservable leg because the manual
      MOV row defines no flags ("Flags Affected: None"). A future row
      that defines AF (ADD/SUB/NEG families) needs a new `AuxDefined`
      constructor with its canonical-helper equation
      (`afAdd`/`afSub` over `Ganzzahl`, `negWf` over `ShiftLogic`,
      per-width `afAddB`/`afSubB` identities of lane 692); a fiat
      value or a weakened consumer is refused by construction.
    - No silicon correspondence: the MOV flag sentence is manual
      provenance (Intel SDM 325462-093US), not a silicon proof.
    - No per-access target-to-W/GX simulation, no source/IR/ABI/loader/
      entry/budget claim; `none`/`verweigert` is the absence of a
      transition, never a halt claim.
    - MERGE NOTE: the additive `import Grammatik.X86.AuxiliaryCarryRows`
      at the end of `grammatik/Grammatik.lean` could not be added by
      this lane (no write permission outside the two owned files); the
      merger must append that one line. Until then this module is
      checked via `./lean-probe` only and is not part of `./lean-bau`.
-/

#print axioms auxRowStep_load
#print axioms auxRowStep_store
#print axioms auxFlags_erhalten
#print axioms auxAf_verbrauch
#print axioms auxKeinDefiniert
#print axioms auxProbe_afUndefiniert_b8load
#print axioms auxCarry_definiert_alle
#print axioms auxCarry_byteschritt
#print axioms auxProbe_keinAfbypass
#print axioms auxCarry_zeuge

end Gabbro.Grammatik.X86
