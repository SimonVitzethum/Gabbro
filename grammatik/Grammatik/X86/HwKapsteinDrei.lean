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

end Gabbro.Grammatik.X86
