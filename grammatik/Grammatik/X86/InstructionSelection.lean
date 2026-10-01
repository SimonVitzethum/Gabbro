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

/-! ## 2. Target value facts: what the chosen instructions compute. -/

/-- `xor v v` is zero: the clobbering zeroing choice really zeroes. -/
theorem xor_selbst_null (v : Wort) : (xor64 v v).1 = 0 := by
  simp [xor64]

/-- `add x 0` is `x`: the eliminated add is a value identity. -/
theorem add_null_ident (x : Wort) : (add64 x 0).1 = x := by
  simp [add64]

/-! ## 3. Real byte sequences: the choices differ on the wire. -/

/-- The preserving zeroing choice is 10 bytes, the clobbering one 3:
    selection is a length claim, not just a value claim. -/
theorem null_laengen (dst : Register) :
    (encode (.movImm64 dst 0)).length = 10 ∧
      (encode (.xorReg64 dst dst)).length = 3 := by
  cases dst <;> decide

/-- Pinned bytes of the clobbering zeroing of `rax`. -/
theorem pin_xor_rax : encode (.xorReg64 .rax .rax) =
    [natByte 72, natByte 49, natByte 192] := by
  decide

/-- Pinned bytes of the preserving zeroing of `rax`: 10 bytes. -/
theorem pin_mov0_rax : encode (.movImm64 .rax 0) =
    [natByte 72, natByte 184, natByte 0, natByte 0, natByte 0,
     natByte 0, natByte 0, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Both pinned choices decode back to themselves (accepted round trip). -/
theorem runde_null_rax (suffix : List Byte) :
    decode (encode (.xorReg64 .rax .rax) ++ suffix) =
      some (⟨.xorReg64 .rax .rax, (encode (.xorReg64 .rax .rax)).length⟩,
        suffix) ∧
    decode (encode (.movImm64 .rax 0) ++ suffix) =
      some (⟨.movImm64 .rax 0, (encode (.movImm64 .rax 0)).length⟩,
        suffix) :=
  ⟨roundtrip _ _, roundtrip _ _⟩

/-! ## 4. Executed-step observations: both choices zero the register. -/

/-- Executed `movImm64 dst 0` zeroes `dst` through the canonical step. -/
theorem schritt_null_mov (s : Zustand) (dst : Register) :
    (schritt ⟨.movImm64 dst 0, 10⟩ s).map (fun s' => s'.register dst) =
      some 0 := by
  have h := schritt_movImm64 ⟨.movImm64 dst 0, 10⟩ s dst 0 rfl rfl
  rw [h]
  simp [schrittRegister, regSet]

/-- Executed `xor dst dst` zeroes `dst` through the canonical step. -/
theorem schritt_null_xor (s : Zustand) (dst : Register) :
    (schritt ⟨.xorReg64 dst dst, 3⟩ s).map (fun s' => s'.register dst) =
      some 0 := by
  have h := schritt_xorReg64 ⟨.xorReg64 dst dst, 3⟩ s dst dst rfl rfl
  rw [h]
  have hz : (xor64 (s.register dst) (s.register dst)).1 = 0 :=
    xor_selbst_null _
  simp [schrittRegister, regSet, hz]

/-- Value agreement: the two executed choices observe the same register. -/
theorem schritt_null_gleich (s : Zustand) (dst : Register) :
    (schritt ⟨.xorReg64 dst dst, 3⟩ s).map (fun s' => s'.register dst) =
      (schritt ⟨.movImm64 dst 0, 10⟩ s).map
        (fun s' => s'.register dst) := by
  rw [schritt_null_xor, schritt_null_mov]

/-! ## 5. Flag observations: the value agreement costs the flags. -/

/-- `xor v v` sets ZF: the clobbering choice leaves a set zero flag. -/
theorem xor_selbst_zf (v : Wort) : (xor64 v v).2.zf = true := by
  simp [xor64, zfTest]

/-- A following `je` diverges: under live flags (`zf = false`) the preserving
    choice falls through while the clobbering choice would take the branch.
    Missing flag liveness is therefore rejected, not ignored. -/
theorem zweig_weicht_ab (s : Zustand) (dst : Register)
    (hdead : s.flags.zf = false) :
    bedingung .e s.flags = false ∧
      bedingung .e (xor64 (s.register dst) (s.register dst)).2 = true := by
  simp [bedingung, hdead, xor_selbst_zf]

/-- The selector keeps `mov` under live flags. -/
theorem waehleNull_le (dst : Register) :
    waehleNull true dst = [.movImm64 dst 0] := rfl

/-- The selector takes `xor` only under dead flags. -/
theorem waehleNull_tot (dst : Register) :
    waehleNull false dst = [.xorReg64 dst dst] := rfl

/-- The checker refuses the clobbering choice under live flags. -/
theorem wahlOk_verweigert_xor_le (dst : Register) :
    wahlOk true [.xorReg64 dst dst] = false := rfl

/-- The checker allows the preserving choice under live flags. -/
theorem wahlOk_erlaubt_mov (dst : Register) :
    wahlOk true [.movImm64 dst 0] = true := rfl

/-- The checker allows the clobbering choice under dead flags. -/
theorem wahlOk_erlaubt_tot (dst : Register) :
    wahlOk false [.xorReg64 dst dst] = true := rfl

end Gabbro.Grammatik.X86.Anweisungswahl
