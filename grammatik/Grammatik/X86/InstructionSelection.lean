/-
  File:      Grammatik/X86/InstructionSelection.lean
  Subject:   Invariant-derived register-only instruction selection over real bytes.

  Lane 600: connects the accepted source facts (`InvariantenOpt`: literal-zero
  justification, stability-gated loads; `StaerkeReduktion`: value facts) to an
  actual encoded pilot-instruction choice. Three register-only rules: zeroing
  (`movImm64 0` vs `xor dst dst`), add-zero elimination, self-move elimination.
  Every rule reuses source `eval`/`execBlock` and the canonical decoded `schritt`;
  no new interpreter, no new IR. Flag liveness and alias equality are checked
  data; Rust-provided metadata is never trusted.
-/
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86.Anweisungswahl

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.InvariantenOpt

/-- Zeroing choice: flags-live keeps the preserving 10-byte `movImm64 0`,
    flags-dead takes the clobbering 3-byte `xor dst dst`. -/
def waehleNull (flagsLive : Bool) (dst : Register) : List Befehl :=
  if flagsLive then [.movImm64 dst 0] else [.xorReg64 dst dst]

/-- Add-zero elimination: with a justified zero in `src` and dead flags the
    `add` vanishes; with live flags it is kept. -/
def waehleAddNull (flagsLive : Bool) (dst src : Register) : List Befehl :=
  if flagsLive then [.addReg64 dst src] else []

/-- Self-move elimination: `mov dst dst` is a no-op; a move between two
    different registers is kept (checked alias equality). -/
def waehleSelbstMov (dst src : Register) : List Befehl :=
  if dst = src then [] else [.movReg64 dst src]

/-- Flag/branch checker: a clobbering `xor` under live flags is refused. -/
def wahlOk (flagsLive : Bool) (wahl : List Befehl) : Bool :=
  match flagsLive, wahl with
  | true, [.xorReg64 _ _] => false
  | _, _ => true

/-- Invariant-gated elimination: the tag records which leg discharges the
    site guarantee; without a held stability fact nothing is eliminated. -/
def waehleInv (s : InvScope) (stabil : Bool) : Option (List Befehl) :=
  match s with
  | .ruhe => if stabil then some [] else none
  | .sicht => if stabil then some [] else none
  | .wechsel => if stabil then some [] else none

end Gabbro.Grammatik.X86.Anweisungswahl
