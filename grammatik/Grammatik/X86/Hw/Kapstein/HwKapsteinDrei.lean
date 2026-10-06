/-
  File:      Grammatik/X86/HwKapsteinDrei.lean
  Subject:   Capstone, third step: the accepted REX.W LEA family wired
             into the decoder chain and the coherent machine.

  Lane 1363: on top of the second union `HwVollSchritt2` (lane 1311,
  `HwKapsteinZwei.lean`, reused unchanged), wire the accepted REX.W
  LEA family (`decodeLea`, `leaFormSchritt`, `encodeAdr` from
  `AddressEncoding`, reused unchanged): one new chain arm that runs
  only where `kapDecode` refuses, one `HwAdapter` plug in the style
  of `adapterRot`, and a reached witness beside planted refusals.
  No accepted definition is redefined; no hardware correspondence
  beyond self-consistency is claimed (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.Speicher.AddressEncoding
import Grammatik.X86.Befehle.Kompakt.LeaPureForm
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.Hw.Kapstein.HwKapsteinZwei
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Kern.Gleitprofil

namespace Gabbro.Grammatik.X86

/-- Third-union decoded row: the whole capstone chain plus one REX.W
    LEA arm carrying destination, address form and consumed length. -/
inductive Kap3Dekodiert where
  | alt : KapDekodiert → Kap3Dekodiert
  | lea : Register → AdrForm → Nat → Kap3Dekodiert
  deriving DecidableEq, Repr

/-- The third chain: the accepted chain first (no shadowing), the
    accepted LEA decoder where the chain refuses, gated by the
    checked instruction length. -/
def kapDecode3 : List Byte → Option (Kap3Dekodiert × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.alt k, rest)
    | none =>
      match decodeLea bs with
      | some (dst, f, rest) =>
        let l := bs.length - rest.length
        match laengeOk l with
        | true => some (.lea dst f l, rest)
        | false => none
      | none => none

/-! ## 1. Agreement: the old chain embeds exactly; LEA takes only
    what the old chain refuses. Every premise is used: the earlier
    `none` routes past the old arm, the `some` takes the arm. -/

/-- The accepted chain embeds exactly. -/
theorem kap3_alt (bs : List Byte) (k : KapDekodiert) (rest : List Byte)
    (h : kapDecode bs = some (k, rest)) :
    kapDecode3 bs = some (.alt k, rest) := by
  unfold kapDecode3
  simp only [h]

/-- The LEA arm agrees where the accepted chain refuses. -/
theorem kap3_lea (bs : List Byte) (dst : Register) (f : AdrForm)
    (rest : List Byte)
    (hkap : kapDecode bs = none)
    (hlea : decodeLea bs = some (dst, f, rest))
    (hok : laengeOk (bs.length - rest.length) = true) :
    kapDecode3 bs =
      some (.lea dst f (bs.length - rest.length), rest) := by
  unfold kapDecode3
  simp only [hkap, hlea, hok]

/-! ## 2. New rows: the accepted LEA pins decode through the third
    chain; the accepted chain refuses them (gap evidence). -/

/-- GAP: the accepted chain refuses the scaled-index LEA bytes. -/
theorem kap3_luecke_skaliert :
    kapDecode [natByte 72, natByte 141, natByte 68, natByte 203,
      natByte 5] = none := by
  decide

/-- NEW ROW: scaled-index LEA decodes through the third chain. -/
theorem kap3_lea_skaliert :
    kapDecode3 [natByte 72, natByte 141, natByte 68, natByte 203,
      natByte 5] =
      some (.lea .rax
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8) 5, []) := by
  decide

/-- OVERLAP: the accepted chain already takes the eight-byte
    scaled-disp32 LEA through its integer-core `lea64` arm. -/
theorem kap3_kern_lea64_hoch :
    kapDecode [natByte 75, natByte 141, natByte 132, natByte 136,
      natByte 16, natByte 0, natByte 0, natByte 0] =
      some (.kern ⟨.lea64 .rax .r8 (some (.r9, .s4))
        (BitVec.ofNat 32 16), 8⟩, []) := by
  decide

/-- OVERLAP KEPT: the third chain prefers the accepted `lea64` arm
    on the eight-byte form (no shadowing). -/
theorem kap3_hoch_bleibt_alt :
    kapDecode3 [natByte 75, natByte 141, natByte 132, natByte 136,
      natByte 16, natByte 0, natByte 0, natByte 0] =
      some (.alt (.kern ⟨.lea64 .rax .r8 (some (.r9, .s4))
        (BitVec.ofNat 32 16), 8⟩), []) :=
  kap3_alt _ _ _ kap3_kern_lea64_hoch

/-- GAP: the accepted chain refuses the REX.R scaled-disp8 LEA. -/
theorem kap3_luecke_r8_skaliert :
    kapDecode [natByte 76, natByte 141, natByte 68, natByte 203,
      natByte 5] = none := by
  decide

/-- NEW ROW: REX.R scaled-disp8 LEA decodes through the third chain. -/
theorem kap3_lea_r8_skaliert :
    kapDecode3 [natByte 76, natByte 141, natByte 68, natByte 203,
      natByte 5] =
      some (.lea .r8
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8) 5, []) := by
  decide

/-- GAP: the accepted chain refuses the REX.R base-plus-disp8 LEA. -/
theorem kap3_luecke_r8_rbp :
    kapDecode [natByte 76, natByte 141, natByte 69, natByte 5] =
      none := by
  decide

/-- NEW ROW: REX.R base-plus-disp8 LEA decodes through the third chain. -/
theorem kap3_lea_r8_rbp :
    kapDecode3 [natByte 76, natByte 141, natByte 69, natByte 5] =
      some (.lea .r8 (basisDisp8Form .rbp (natByte 5)) 4, []) := by
  decide

/-- NEW ROW: RIP-relative image reference. -/
theorem kap3_lea_rip :
    kapDecode3 [natByte 72, natByte 141, natByte 5, natByte 249,
      natByte 15, natByte 0, natByte 0] =
      some (.lea .rax (ripForm (BitVec.ofNat 32 4089)) 7, []) := by
  decide

/-! ## 3. Refusals: what neither the old chain nor LEA admits. -/

/-- REFUSAL: LEA without REX.W stays refused. -/
theorem kap3_nichts_ohne_rex :
    kapDecode3 [natByte 141, natByte 68, natByte 203, natByte 5] =
      none := by
  decide

/-- REFUSAL: a legacy operand-size prefix before LEA stays refused. -/
theorem kap3_nichts_vorsatz :
    kapDecode3 [natByte 102, natByte 72, natByte 141, natByte 68,
      natByte 203, natByte 5] = none := by
  decide

/-- REFUSAL: LOCK NOP stays refused. -/
theorem kap3_nichts_lock90 :
    kapDecode3 [natByte 240, natByte 144] = none := by
  decide

/-! ## 4. Encoder: canonical REX.W LEA bytes with decoder round trip.
    The accepted `encodeAdr` tail is reused unchanged; only the
    opcode byte is added. -/

/-- Canonical LEA bytes: REX.W, opcode `8D`, then the accepted tail. -/
def leaEncode (dst : Register) (f : AdrForm) : Option (List Byte) :=
  match encodeAdr dst f with
  | some (rex :: tail) => some (rex :: natByte 141 :: tail)
  | _ => none

/-- ROUND TRIP: scaled-disp8 encodes and decodes back exactly. -/
theorem kap3_rundweg_skaliert :
    (leaEncode .rax
      (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8)).bind
      decodeLea =
      some ((.rax,
        skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, [])) := by
  decide

/-- ROUND TRIP: the REX.R scaled form round-trips through new bytes. -/
theorem kap3_rundweg_r8_skaliert :
    (leaEncode .r8
      (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8)).bind
      decodeLea =
      some ((.r8,
        skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, [])) := by
  decide

/-- ROUND TRIP: the RIP-relative form round-trips exactly. -/
theorem kap3_rundweg_rip :
    (leaEncode .rax (ripForm (BitVec.ofNat 32 4089))).bind decodeLea =
      some ((.rax, ripForm (BitVec.ofNat 32 4089), [])) := by
  decide

/-- ENCODER REFUSAL: the pilot-owned base-plus-disp32 shape encodes
    to nothing (the accepted encoder refusal, lifted). -/
theorem kap3_encode_pilot_basis :
    leaEncode .rax (basisForm .rbx (BitVec.ofNat 32 5)) = none := by
  decide

/-! ## 5. Machine adapter: the LEA family on the coherent machine.

    The producer plug instantiates `HwAdapter LeaDecodiert`: the
    accepted `leaFormSchritt` runs on the core projection with the
    post-decode RIP as the RIP base; success re-embeds core data
    over the shared memory, refusal admits no successor state. -/

/-- Decoded LEA event on the coherent machine: destination, address
    form and consumed length. -/
structure LeaDecodiert where
  dst : Register
  form : AdrForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- The LEA plug: one checked LEA event step on the coherent
    machine. `none` = decode-length refusal, never a silent
    successor. -/
def adapterLea : HwAdapter LeaDecodiert :=
  ⟨fun m c d =>
    match leaFormSchritt d.dst d.form d.laenge (projZustand m c)
        (ripNach (projZustand m c).rip d.laenge) with
    | some s' =>
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
    | none => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterLea_wf (m : HwMaschine) (c : Nat)
    (d : LeaDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterLea).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterLea at h
  simp only at h
  cases hsch : leaFormSchritt d.dst d.form d.laenge (projZustand m c)
      (ripNach (projZustand m c).rip d.laenge) with
  | some s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | none =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the accepted
    family step succeeds, with the successor core data re-embedded. -/
theorem adapterLea_ok (m : HwMaschine) (c : Nat)
    (d : LeaDecodiert) (s' : Zustand)
    (h : leaFormSchritt d.dst d.form d.laenge (projZustand m c)
      (ripNach (projZustand m c).rip d.laenge) = some s') :
    (adapterLea).schritt m c d =
      some (setKernVonFp m c
        ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterLea
  simp only [h]

/-- The successor core sees the family successor registers over
    the shared memory. -/
theorem adapterLea_proj (m : HwMaschine) (c : Nat)
    (d : LeaDecodiert) (s' : Zustand)
    (hok : laengeOk d.laenge = true)
    (h : leaFormSchritt d.dst d.form d.laenge (projZustand m c)
      (ripNach (projZustand m c).rip d.laenge) = some s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne
      c).register = s'.register ∧
    (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).mem =
      m.mem ∧
    s'.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c _,
    setKernVonFp_speicher m c _, ?_⟩
  have hmem := leaFormSchritt_speicher d.dst d.form d.laenge
    (projZustand m c) s' _ hok h
  have hproj : (projZustand m c).speicher = m.mem := rfl
  rw [hproj] at hmem
  exact hmem

/-- The destination holds the accepted effective address. -/
theorem adapterLea_dst (m : HwMaschine) (c : Nat)
    (d : LeaDecodiert) (s' : Zustand)
    (hok : laengeOk d.laenge = true)
    (h : leaFormSchritt d.dst d.form d.laenge (projZustand m c)
      (ripNach (projZustand m c).rip d.laenge) = some s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne
      c).register d.dst =
      adrEff (projZustand m c)
        (ripNach (projZustand m c).rip d.laenge) d.form := by
  rw [setKernVonFp_register]
  exact leaFormSchritt_dst _ _ _ _ _ _ hok h

/-- A bad decode length admits no adapter step. -/
theorem adapterLea_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : LeaDecodiert)
    (h : laengeOk d.laenge = false) :
    (adapterLea).schritt m c d = none := by
  have hstep := leaFormSchritt_laenge_verweigert d.dst d.form d.laenge
    (projZustand m c) (ripNach (projZustand m c).rip d.laenge) h
  unfold adapterLea
  simp only [hstep]

/-! ## 6. Composed step: the second union plus the LEA arm. -/

/-- Third-union events: the whole second union plus one LEA tag.
    (No `DecidableEq`/`Repr`: the second-union event type carries
    non-decidable family events, so none is derived here either.) -/
inductive Kap3Ereignis where
  | alt : Kap2Ereignis → Kap3Ereignis
  | lea : Nat → LeaDecodiert → Kap3Ereignis

/-- The third composed machine step: the whole second union plus
    the LEA adapter arm. -/
inductive HwVollSchritt3 : HwMaschine → HwMaschine → Kap3Ereignis → Prop where
  | alt {m m' : HwMaschine} (k : Kap2Ereignis)
      (h : HwVollSchritt2 m m' k) : HwVollSchritt3 m m' (.alt k)
  | lea {m m' : HwMaschine} (c : Nat) (d : LeaDecodiert)
      (h : (adapterLea).schritt m c d = some m') :
      HwVollSchritt3 m m' (.lea c d)

/-- The second union embeds exactly. -/
theorem kap3_alt_embedded (m m' : HwMaschine) (k : Kap2Ereignis) :
    HwVollSchritt2 m m' k ↔ HwVollSchritt3 m m' (.alt k) := by
  constructor
  · intro h
    exact .alt k h
  · intro h
    cases h with
    | alt _ hstep => exact hstep

/-- LEA embeds exactly. -/
theorem kap3_lea_embedded (m m' : HwMaschine) (c : Nat)
    (d : LeaDecodiert) :
    (adapterLea).schritt m c d = some m' ↔
      HwVollSchritt3 m m' (.lea c d) := by
  constructor
  · intro h
    exact .lea c d h
  · intro h
    cases h with
    | lea _ _ hstep => exact hstep

/-- Decoder-to-event bridge: an `.lea` row is its machine event;
    old-chain rows have no LEA event. -/
def kap3Ereignis : Kap3Dekodiert → Option LeaDecodiert
  | .lea dst f l => some ⟨dst, f, l⟩
  | .alt _ => none

/-- The bridge carries LEA rows exactly. -/
theorem kap3Ereignis_lea (dst : Register) (f : AdrForm) (l : Nat) :
    kap3Ereignis (.lea dst f l) = some ⟨dst, f, l⟩ := rfl

/-- The bridge refuses old-chain rows. -/
theorem kap3Ereignis_alt (k : KapDekodiert) :
    kap3Ereignis (.alt k) = none := rfl

/-! ## 7. Witness: a reached two-core LEA run beside a
    memory-changing TSO drain with owner-only forwarding. -/

/-- Witness registers core 0: base `rbx = 8192`, index `rcx = 1`. -/
def leaHwWitReg0 : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rcx then BitVec.ofNat 64 1
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 computes, core 1 idles. -/
def leaHwWitKern : Nat → HwKern
  | 0 => ⟨leaHwWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon. -/
def leaHwWitStart : HwMaschine :=
  ⟨zeugenSpeicher, leaHwWitKern, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem leaHwWitStart_wf : HwWf leaHwWitStart := by
  intro c f _
  cases f <;> rfl

/-- The witness LEA event: `rax := [rbx + rcx * 8 + 5]`. -/
def leaHwEreignis : LeaDecodiert :=
  ⟨.rax, skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, 5⟩

/-- Core 0 runs the witness LEA through the adapter. -/
def leaHwOut : Option HwMaschine :=
  (adapterLea).schritt leaHwWitStart 0 leaHwEreignis

/-- Read a core register out of an adapter outcome. -/
def leaHwRegOut (o : Option HwMaschine) (c : Nat) (q : Register) :
    Option Wort :=
  match o with
  | some m => some ((m.kerne c).register q)
  | none => none

/-- Core 0 LEA: `rax` holds `8192 + 8 + 5 = 8205`. -/
theorem leaHw_rax :
    leaHwRegOut leaHwOut 0 Register.rax =
      some (BitVec.ofNat 64 8205) := by
  decide

/-- Witness data address. -/
def leaHwWitAdr : Adresse := BitVec.ofNat 64 8200

/-- Witness TSO start: canonical memory, empty buffers. -/
def leaHwWitTso0 : TSOZustand := ⟨zeugenSpeicher, fun _ => []⟩

/-- Core 0 issues byte 42 at the data cell. -/
def leaHwWitTso1 : Option TSOZustand :=
  issueByte leaHwWitTso0 0 leaHwWitAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def leaHwWitEigen : Option (Option Byte) :=
  match leaHwWitTso1 with
  | some s => some (loadByte s 0 leaHwWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def leaHwWitFremd : Option (Option Byte) :=
  match leaHwWitTso1 with
  | some s => some (loadByte s 1 leaHwWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def leaHwWitTso2 : Option TSOZustand :=
  match leaHwWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def leaHwWitNachFlush : Option (Option Byte) :=
  match leaHwWitTso2 with
  | some s => some (some (s.mem.bytes leaHwWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def leaHwWitFremdNach : Option (Option Byte) :=
  match leaHwWitTso2 with
  | some s => some (loadByte s 1 leaHwWitAdr)
  | none => none

/-- The data cell starts zeroed. -/
theorem leaHw_anfang_null :
    zeugenSpeicher.bytes leaHwWitAdr = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem leaHw_weiterleitung :
    leaHwWitEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem leaHw_fremd_alt :
    leaHwWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem leaHw_spuelung_aendert_speicher :
    leaHwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem leaHw_fremd_neu :
    leaHwWitFremdNach = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- A bad decode length refuses the machine step. -/
theorem leaHw_schlechte_laenge_verweigert :
    (adapterLea).schritt leaHwWitStart 0
      ⟨.rax, skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, 0⟩ =
      none :=
  adapterLea_verweigert_bei_laenge _ _ _ (by decide)

/-- A reached third-union LEA step stands on the witness machine. -/
theorem leaHw_schritt_erreichbar :
    ∃ m' : HwMaschine,
      HwVollSchritt3 leaHwWitStart m' (.lea 0 leaHwEreignis) := by
  cases ho : (adapterLea).schritt leaHwWitStart 0 leaHwEreignis with
  | none =>
    have h := leaHw_rax
    unfold leaHwOut leaHwRegOut at h
    rw [ho] at h
    simp only at h
    cases h
  | some m' => exact ⟨m', .lea 0 leaHwEreignis ho⟩

/-- The joint witness: a reached two-core LEA run (`rax = 8205` on
    core 0) beside a buffered store that only the owner forwards
    and a drain that changes actual shared memory from 0 to 42 --
    with the refusal beside it. Non-degenerate: the drain changes
    actual shared memory. -/
theorem leaHw_zeuge :
    leaHwRegOut leaHwOut 0 Register.rax =
        some (BitVec.ofNat 64 8205) ∧
      leaHwWitEigen = some (some (BitVec.ofNat 8 42)) ∧
      leaHwWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      leaHwWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      leaHwWitFremdNach = some (some (BitVec.ofNat 8 42)) ∧
      zeugenSpeicher.bytes leaHwWitAdr = BitVec.ofNat 8 0 ∧
      HwWf leaHwWitStart ∧
      (∃ m' : HwMaschine,
        HwVollSchritt3 leaHwWitStart m' (.lea 0 leaHwEreignis)) ∧
      (adapterLea).schritt leaHwWitStart 0
          ⟨.rax, skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8,
            0⟩ = none ∧
      kapDecode3 [natByte 240, natByte 144] = none := by
  refine ⟨leaHw_rax, leaHw_weiterleitung, leaHw_fremd_alt,
    leaHw_spuelung_aendert_speicher, leaHw_fremd_neu, leaHw_anfang_null,
    leaHwWitStart_wf, leaHw_schritt_erreichbar,
    leaHw_schlechte_laenge_verweigert, kap3_nichts_lock90⟩

/- CUTS:
   Proved here: the accepted REX.W LEA family (`decodeLea`,
   `leaFormSchritt`, `encodeAdr` from `AddressEncoding`, lifted,
   never redefined) wired into a third decoder chain and the
   coherent machine -- the accepted chain first (exact general
   agreement `kap3_alt`), the LEA arm where the chain refuses
   (`kap3_lea`), four new LEA rows with gap evidence (scaled-disp8,
   REX.R scaled-disp8, REX.R base-disp8, RIP-relative), the
   eight-byte scaled-disp32 overlap kept on the accepted
   integer-core `lea64` arm (measured, old arm wins by
   construction), encoder round trips at the `decodeLea` level,
   planted refusals (no REX.W, legacy prefix, LOCK NOP, bad
   decode length, pilot-owned encoder shape), the `HwAdapter
   LeaDecodiert` plug with well-formedness preservation and exact
   evaluator agreement (destination, flags, memory, other
   registers via the accepted `leaFormSchritt_*` lemmas), the
   third composed step with exact embeddings of the second union
   and the LEA arm, a decoder-to-event bridge, and a reached
   two-core run (`rax = 8205` on core 0) beside owner-only
   forwarding and a memory-changing drain (0 becomes 42).
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted
     canonical subsets with self-consistency only, not x86 truth.
     Silicon assumptions named: REX.W LEA computes the effective
     address into the full 64-bit destination, reads no memory,
     changes no flags; every `90H`-free claim is out of scope.
   - The eight-byte overlap agrees only at the decoder-routing
     level (both decoders accept the bytes, the old arm wins);
     no semantic agreement between `leaFormSchritt` and
     `coreSchritt` on the overlap is proved here.
   - Over-refusals inherited from `decodeLea` (no bare-`8D`,
     no legacy prefix, pilot-owned tails stay pilot-owned) and
     from `encodeAdr` (base-plus-disp32 unencodable here).
   - No source/IR/ABI/loader/entry/budget link, no per-access
     target-to-W/GX simulation, no timing/power behaviour.
   - Placement: this file sits at `Grammatik/X86/HwKapsteinDrei.lean`
     per the lane task; the layout rules assign `HwKapstein*` to
     `Grammatik/X86/Hw/Kapstein/` (a maintainer move with import
     rewrite, no semantic change).
-/

#print axioms Kap3Dekodiert
#print axioms kapDecode3
#print axioms kap3_alt
#print axioms kap3_lea
#print axioms kap3_luecke_skaliert
#print axioms kap3_lea_skaliert
#print axioms kap3_kern_lea64_hoch
#print axioms kap3_hoch_bleibt_alt
#print axioms kap3_luecke_r8_skaliert
#print axioms kap3_lea_r8_skaliert
#print axioms kap3_luecke_r8_rbp
#print axioms kap3_lea_r8_rbp
#print axioms kap3_lea_rip
#print axioms kap3_nichts_ohne_rex
#print axioms kap3_nichts_vorsatz
#print axioms kap3_nichts_lock90
#print axioms leaEncode
#print axioms kap3_rundweg_skaliert
#print axioms kap3_rundweg_r8_skaliert
#print axioms kap3_rundweg_rip
#print axioms kap3_encode_pilot_basis
#print axioms LeaDecodiert
#print axioms adapterLea
#print axioms adapterLea_wf
#print axioms adapterLea_ok
#print axioms adapterLea_proj
#print axioms adapterLea_dst
#print axioms adapterLea_verweigert_bei_laenge
#print axioms Kap3Ereignis
#print axioms kap3_alt_embedded
#print axioms kap3_lea_embedded
#print axioms kap3Ereignis_lea
#print axioms kap3Ereignis_alt
#print axioms leaHwWitStart_wf
#print axioms leaHw_rax
#print axioms leaHw_anfang_null
#print axioms leaHw_weiterleitung
#print axioms leaHw_fremd_alt
#print axioms leaHw_spuelung_aendert_speicher
#print axioms leaHw_fremd_neu
#print axioms leaHw_schlechte_laenge_verweigert
#print axioms leaHw_schritt_erreichbar
#print axioms leaHw_zeuge

end Gabbro.Grammatik.X86
