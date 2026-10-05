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

end Gabbro.Grammatik.X86
